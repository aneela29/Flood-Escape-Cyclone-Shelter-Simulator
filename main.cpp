// ============================================================================
//  Flood Escape and Cyclone Shelter Rescue Simulator  (3D, OpenGL + FreeGLUT)
//  Course : CSE-4742 Computer Graphics Lab
//
//  Build (MSYS2 MINGW64 terminal):
//    g++ main.cpp -o flood_sim.exe -lfreeglut -lopengl32 -lglu32
//  Run:
//    ./flood_sim.exe
//
//  Controls:
//    S = Start   P = Pause   C = Resume   R = Reset      (also: right-click menu)
//    Left mouse drag = rotate camera,  Mouse wheel / + / - = zoom
//    Arrow keys = rotate camera
//    1 = Overview  2 = Cyclone shelter  3 = River & boats  4 = Top view
//    Z = toggle safe-zone overlay   N = toggle rain   [ / ] = slower / faster
// ============================================================================
#include <GL/freeglut.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <queue>
#include <algorithm>

using std::vector;

static const float PI = 3.14159265f;

// ------------------------------- World layout ------------------------------
static const int   NX = 3, NZ = 5;
static const float XR[NX] = { -30.f, 0.f, 30.f };              // vertical roads (x)
static const float ZR[NZ] = { -24.f, -12.f, 0.f, 12.f, 24.f }; // horizontal roads (z)
static const float MAP = 50.f;                                 // town spans -50..50
static const float RIVER_Z0 = -42.f, RIVER_Z1 = -30.f;         // river band
static const float ROAD_HW = 2.0f;                             // road half width
static const float SH_X = 0.f, SH_Z = 42.f, SH_HALF = 8.f;     // shelter centre/size
static const float FLOOR_H = 3.4f;                             // shelter storey height
static const int   SHELTER_CAP = 500;
static const float SIM_SECONDS = 110.f;                        // time for full flood
static const int   NODES = NX * NZ + 1;                        // road intersections + shelter node
static const int   SNODE = NX * NZ;                            // shelter entrance node (0,34)
static const int   SLINK = 1 * NZ + 4;                         // node (0,24) links to shelter

// ------------------------------- Data types --------------------------------
struct V2 { float x, z; };
struct Seg { float x1, z1, x2, z2; bool horiz; };
struct House { float x, z; int style; };
struct Tree { float x, z, s; };

enum PState { P_WAIT, P_WALK, P_STRAND, P_BOAT, P_TOSHELTER, P_SAFE };
struct Person {
    float x = 0, z = 0, startT = 0, r = 1, g = 1, b = 1, phase = 0, retry = 0;
    PState st = P_WAIT;
    vector<V2> path;
    size_t pi = 0;
    bool claimed = false;
    int boat = -1;
};

enum BState { B_IDLE, B_PICK, B_DELIVER };
struct Boat {
    float x = 0, z = 0, ang = 0;
    BState st = B_IDLE;
    vector<V2> wp;
    size_t wi = 0;
    vector<int> cargo;
    int target = -1;
};

enum { ST_IDLE, ST_RUN, ST_PAUSE };

// ------------------------------- Global state ------------------------------
static int   simState = ST_IDLE;
static float flood = 0.f;          // 0..1 flood progress
static float animT = 0.f;          // animation clock (waves, bobbing)
static float simSpeed = 1.f;
static int   rescued = 0;
static bool  showSafe = true, showRain = true;

static vector<Seg>    segs;
static vector<House>  houses;
static vector<Tree>   trees;
static vector<Person> people;
static vector<Boat>   boats;

static int  par[NODES];
static bool reach[NODES];

static int winW = 1280, winH = 720;
static int lastT = 0;

// camera
static float camYaw = 200.f, camPitch = 38.f, camDist = 135.f;
static float camTX = 0.f, camTY = 0.f, camTZ = 5.f;
static int   lastMX = 0, lastMY = 0;
static bool  dragging = false;

// rain
static const int NRAIN = 1800;
static float rainX[NRAIN], rainY[NRAIN], rainZ[NRAIN];

// ------------------------------- Small helpers -----------------------------
static float rand01() { return rand() / (float)RAND_MAX; }
static float hash01(int n) { float s = sinf(n * 12.9898f) * 43758.5453f; return s - floorf(s); }

static float waterY() { return -0.4f + 2.0f * flood; }
static float floodZ() { return flood < 0.2f ? -31.f : -30.f + (flood - 0.2f) / 0.8f * 60.f; }
static bool  inWater(float z) { return waterY() > 0.12f && z < floodZ() - 0.2f; }

static bool stepToward(float &x, float &z, const V2 &t, float d) {
    float dx = t.x - x, dz = t.z - z, L = sqrtf(dx * dx + dz * dz);
    if (L <= d) { x = t.x; z = t.z; return true; }
    x += dx / L * d; z += dz / L * d;
    return false;
}

// ------------------------------- Drawing helpers ---------------------------
static void box(float cx, float cy, float cz, float sx, float sy, float sz) {
    glPushMatrix(); glTranslatef(cx, cy, cz); glScalef(sx, sy, sz); glutSolidCube(1.0); glPopMatrix();
}
static void boxBase(float cx, float y0, float cz, float sx, float sy, float sz) {
    box(cx, y0 + sy * 0.5f, cz, sx, sy, sz);
}
static void quadXZ(float x1, float z1, float x2, float z2, float y) {
    glBegin(GL_QUADS);
    glNormal3f(0, 1, 0);
    glVertex3f(x1, y, z1); glVertex3f(x1, y, z2); glVertex3f(x2, y, z2); glVertex3f(x2, y, z1);
    glEnd();
}

static void setPerspective(float fovy, float aspect, float zn, float zf) {
    float t = tanf(fovy * PI / 360.f) * zn, r = t * aspect;
    glFrustum(-r, r, -t, t, zn, zf);
}
static void lookAt(float ex, float ey, float ez, float cx, float cy, float cz) {
    float fx = cx - ex, fy = cy - ey, fz = cz - ez;
    float fl = sqrtf(fx * fx + fy * fy + fz * fz); fx /= fl; fy /= fl; fz /= fl;
    float sx = -fz, sy = 0.f, sz = fx;
    float sl = sqrtf(sx * sx + sz * sz); sx /= sl; sz /= sl;
    float ux = sy * fz - sz * fy, uy = sz * fx - sx * fz, uz = sx * fy - sy * fx;
    GLfloat m[16] = { sx, ux, -fx, 0,  sy, uy, -fy, 0,  sz, uz, -fz, 0,  0, 0, 0, 1 };
    glMultMatrixf(m);
    glTranslatef(-ex, -ey, -ez);
}

// ------------------------------- Road graph --------------------------------
static float nodeX(int id) { return id == SNODE ? 0.f : XR[id / NZ]; }
static float nodeZ(int id) { return id == SNODE ? 34.f : ZR[id % NZ]; }

static int neighbors(int u, int out[5]) {
    int n = 0;
    if (u == SNODE) { out[n++] = SLINK; return n; }
    int ix = u / NZ, jz = u % NZ;
    if (ix > 0)      out[n++] = u - NZ;
    if (ix < NX - 1) out[n++] = u + NZ;
    if (jz > 0)      out[n++] = u - 1;
    if (jz < NZ - 1) out[n++] = u + 1;
    if (u == SLINK)  out[n++] = SNODE;
    return n;
}
static bool edgeBlocked(int a, int b) {
    return floodZ() >= std::min(nodeZ(a), nodeZ(b));
}
static bool segBlocked(const Seg &s) {
    return floodZ() >= std::min(s.z1, s.z2);
}

// BFS from the shelter: par[n] = next node on the shortest SAFE route to the shelter
static void updateGraph() {
    for (int i = 0; i < NODES; i++) { reach[i] = false; par[i] = -1; }
    std::queue<int> q;
    q.push(SNODE); reach[SNODE] = true; par[SNODE] = SNODE;
    while (!q.empty()) {
        int u = q.front(); q.pop();
        int nb[5]; int c = neighbors(u, nb);
        for (int i = 0; i < c; i++) {
            int v = nb[i];
            if (!reach[v] && !edgeBlocked(u, v)) { reach[v] = true; par[v] = u; q.push(v); }
        }
    }
}

static bool planPath(Person &p) {
    int j = 0; for (int k = 1; k < NZ; k++) if (fabsf(p.z - ZR[k]) < fabsf(p.z - ZR[j])) j = k;
    int ix = 0; for (int k = 1; k < NX; k++) if (fabsf(p.x - XR[k]) < fabsf(p.x - XR[ix])) ix = k;
    int n = ix * NZ + j;
    if (!reach[n]) return false;
    p.path.clear();
    if (fabsf(p.z - ZR[j]) > 0.3f) p.path.push_back(V2{ p.x, ZR[j] });
    p.path.push_back(V2{ XR[ix], ZR[j] });
    int c = n;
    while (c != SNODE) { c = par[c]; p.path.push_back(V2{ nodeX(c), nodeZ(c) }); }
    p.path.push_back(V2{ 0.f, 39.f });
    p.pi = 0;
    return true;
}

// ------------------------------- Rescue boats ------------------------------
static bool floodedRoadFor(float z, float &out) {
    bool found = false; float best = 1e9f;
    for (int k = 0; k < NZ; k++) {
        if (ZR[k] < floodZ() - 0.5f) {
            float d = fabsf(ZR[k] - z);
            if (d < best) { best = d; out = ZR[k]; found = true; }
        }
    }
    return found;
}
static int findTarget(const Boat &b, float maxD) {
    int best = -1; float bd = maxD;
    for (size_t i = 0; i < people.size(); i++) {
        const Person &p = people[i];
        if (p.st != P_STRAND || p.claimed || !inWater(p.z)) continue;
        float zr; if (!floodedRoadFor(p.z, zr)) continue;
        float dx = p.x - b.x, dz = p.z - b.z, d = sqrtf(dx * dx + dz * dz);
        if (d < bd) { bd = d; best = (int)i; }
    }
    return best;
}
// boats only travel along "water lanes" (river + flooded roads) so they never cross houses
static void buildRoute(Boat &b, float tx, float tz, bool toDock) {
    b.wp.clear(); b.wi = 0;
    int k = -1; for (int c = 0; c < NX; c++) if (fabsf(b.x - XR[c]) < 0.2f) k = c;
    float xv;
    if (toDock) xv = 0.f;
    else if (k >= 0) xv = XR[k];
    else { int bi = 0; for (int c = 1; c < NX; c++) if (fabsf(tx - XR[c]) < fabsf(tx - XR[bi])) bi = c; xv = XR[bi]; }
    if (fabsf(b.x - xv) > 0.2f) b.wp.push_back(V2{ xv, b.z });
    b.wp.push_back(V2{ xv, tz });
    if (fabsf(tx - xv) > 0.2f) b.wp.push_back(V2{ tx, tz });
}
static void assignTarget(Boat &b, int idx) {
    people[idx].claimed = true; b.target = idx;
    float zr = 0.f; floodedRoadFor(people[idx].z, zr);
    buildRoute(b, people[idx].x, zr, false);
}
static void updateBoats(float dt) {
    for (size_t i = 0; i < boats.size(); i++) {
        Boat &b = boats[i];
        if (b.st == B_IDLE) {
            int t = findTarget(b, 1e9f);
            if (t >= 0) { assignTarget(b, t); b.st = B_PICK; }
        }
        if (b.st != B_IDLE) {
            if (b.wi < b.wp.size()) {
                V2 t = b.wp[b.wi];
                float dx = t.x - b.x, dz = t.z - b.z;
                if (dx * dx + dz * dz > 1e-4f) b.ang = atan2f(dx, dz);
                if (stepToward(b.x, b.z, t, 8.f * dt)) b.wi++;
            }
            if (b.wi >= b.wp.size()) {
                if (b.st == B_PICK) {
                    Person &p = people[b.target];
                    p.st = P_BOAT; p.boat = (int)i; b.cargo.push_back(b.target);
                    int t2 = -1;
                    if (b.cargo.size() < 3) t2 = findTarget(b, 30.f);
                    if (t2 >= 0) assignTarget(b, t2);
                    else { buildRoute(b, 0.f, std::min(floodZ() - 1.5f, 31.f), true); b.st = B_DELIVER; }
                } else if (b.st == B_DELIVER) {
                    for (size_t k = 0; k < b.cargo.size(); k++) {
                        Person &p = people[b.cargo[k]];
                        p.st = P_TOSHELTER; p.path.clear();
                        p.path.push_back(V2{ 0.f, 36.f }); p.path.push_back(V2{ 0.f, 39.f });
                        p.pi = 0; rescued++;
                    }
                    b.cargo.clear(); b.st = B_IDLE;
                }
            }
        }
        for (size_t k = 0; k < b.cargo.size(); k++) {
            Person &p = people[b.cargo[k]];
            float off = ((float)k - 1.f) * 1.1f;
            p.x = b.x + sinf(b.ang) * off; p.z = b.z + cosf(b.ang) * off;
        }
    }
}

// ------------------------------- People ------------------------------------
static void updatePeople(float dt) {
    for (size_t i = 0; i < people.size(); i++) {
        Person &p = people[i];
        switch (p.st) {
        case P_WAIT:
            if (inWater(p.z)) p.st = P_STRAND;
            else if (flood >= p.startT) { if (planPath(p)) p.st = P_WALK; else p.st = P_STRAND; }
            break;
        case P_STRAND:
            p.retry -= dt;
            if (!inWater(p.z) && p.retry <= 0.f) { p.retry = 0.5f; if (planPath(p)) p.st = P_WALK; }
            break;
        case P_WALK:
            if (inWater(p.z)) { p.st = P_STRAND; break; }
            if (stepToward(p.x, p.z, p.path[p.pi], 4.f * dt)) p.pi++;
            if (p.pi >= p.path.size()) p.st = P_SAFE;
            break;
        case P_TOSHELTER:
            if (stepToward(p.x, p.z, p.path[p.pi], 4.f * dt)) p.pi++;
            if (p.pi >= p.path.size()) p.st = P_SAFE;
            break;
        default: break;
        }
    }
}

// ------------------------------- World init --------------------------------
static void initWorld() {
    srand(12345);
    flood = 0.f; rescued = 0; simState = ST_IDLE; simSpeed = 1.f;

    segs.clear();
    const float hx[5] = { -50, -30, 0, 30, 50 };
    for (int k = 0; k < NZ; k++) for (int i = 0; i < 4; i++) segs.push_back(Seg{ hx[i], ZR[k], hx[i + 1], ZR[k], true });
    const float vz[7] = { -30, -24, -12, 0, 12, 24, 34 };
    for (int k = 0; k < NX; k++) for (int i = 0; i < 6; i++) segs.push_back(Seg{ XR[k], vz[i], XR[k], vz[i + 1], false });

    houses.clear(); people.clear(); trees.clear(); boats.clear();
    const float HX[8] = { -44, -36, -21, -9, 9, 21, 36, 44 };
    const float HZ[4] = { -18, -6, 6, 18 };
    for (int i = 0; i < 8; i++) for (int j = 0; j < 4; j++) {
        houses.push_back(House{ HX[i], HZ[j], (i + j) % 4 });
        trees.push_back(Tree{ HX[i], HZ[j] - 3.9f, 0.75f + 0.3f * rand01() });
        for (int k = 0; k < 3; k++) {
            Person p;
            p.x = HX[i] + (k - 1) * 1.3f; p.z = HZ[j] + 3.4f;
            p.startT = 0.12f + 0.43f * rand01();
            p.r = 0.3f + 0.7f * rand01(); p.g = 0.3f + 0.7f * rand01(); p.b = 0.3f + 0.7f * rand01();
            p.phase = rand01() * 6.28f;
            people.push_back(p);
        }
    }
    for (float x = -48; x <= 48; x += 12) trees.push_back(Tree{ x + 3.f * rand01(), -27.5f, 0.9f });
    const float FX[6] = { -45, -33, -20, 20, 33, 45 };
    for (int i = 0; i < 6; i++) { trees.push_back(Tree{ FX[i], 40.f, 1.0f }); trees.push_back(Tree{ FX[i] + 3, 46.f, 1.1f }); }

    const float BX[3] = { -22, 0, 22 };
    for (int i = 0; i < 3; i++) { Boat b; b.x = BX[i]; b.z = -36.f; boats.push_back(b); }

    for (int i = 0; i < NRAIN; i++) { rainX[i] = (rand01() * 2 - 1) * 110; rainY[i] = rand01() * 45; rainZ[i] = rand01() * 150 - 70; }
    updateGraph();
}

static void updateSim(float dt) {
    if (simState != ST_RUN) return;
    float d = dt * simSpeed;
    flood = std::min(1.f, flood + d / SIM_SECONDS);
    updateGraph();
    updatePeople(d);
    updateBoats(d);
    if (flood > 0.05f) for (int i = 0; i < NRAIN; i++) { rainY[i] -= 45.f * dt; if (rainY[i] < 0) rainY[i] += 45.f; }
}

// ------------------------------- Scene drawing -----------------------------
static void drawGround() {
    glColor3f(0.30f, 0.58f, 0.25f);
    quadXZ(-300, RIVER_Z1, 300, 300, 0.f);
    quadXZ(-300, -300, 300, RIVER_Z0, 0.f);
    glColor3f(0.38f, 0.68f, 0.31f);
    quadXZ(-MAP, RIVER_Z1, MAP, MAP, 0.01f);
    glColor3f(0.35f, 0.27f, 0.18f);                 // river bed
    quadXZ(-300, RIVER_Z0, 300, RIVER_Z1, -1.4f);
    glColor3f(0.45f, 0.35f, 0.22f);                 // river banks
    glBegin(GL_QUADS);
    glNormal3f(0, 0, -1);
    glVertex3f(-300, -1.4f, RIVER_Z1); glVertex3f(300, -1.4f, RIVER_Z1); glVertex3f(300, 0, RIVER_Z1); glVertex3f(-300, 0, RIVER_Z1);
    glNormal3f(0, 0, 1);
    glVertex3f(-300, -1.4f, RIVER_Z0); glVertex3f(300, -1.4f, RIVER_Z0); glVertex3f(300, 0, RIVER_Z0); glVertex3f(-300, 0, RIVER_Z0);
    glEnd();
}

static void drawRoads() {
    glColor3f(0.22f, 0.22f, 0.24f);
    for (int k = 0; k < NX; k++) quadXZ(XR[k] - ROAD_HW, RIVER_Z1, XR[k] + ROAD_HW, 34.f, 0.03f);
    for (int k = 0; k < NZ; k++) quadXZ(-MAP, ZR[k] - ROAD_HW, MAP, ZR[k] + ROAD_HW, 0.035f);
    glColor3f(0.92f, 0.9f, 0.7f);
    for (int k = 0; k < NX; k++) for (float z = -28; z < 32; z += 4) quadXZ(XR[k] - 0.1f, z, XR[k] + 0.1f, z + 2, 0.05f);
    for (int k = 0; k < NZ; k++) for (float x = -48; x < 48; x += 4) quadXZ(x, ZR[k] - 0.1f, x + 2, ZR[k] + 0.1f, 0.055f);
}

static void drawBlocked() {
    float pulse = 0.5f + 0.5f * sinf(animT * 4.f);
    for (size_t i = 0; i < segs.size(); i++) {
        const Seg &s = segs[i];
        if (!segBlocked(s)) continue;
        glDisable(GL_LIGHTING); glEnable(GL_BLEND);
        glColor4f(0.9f, 0.08f, 0.08f, 0.35f + 0.2f * pulse);
        if (s.horiz) quadXZ(s.x1, s.z1 - ROAD_HW, s.x2, s.z1 + ROAD_HW, 0.07f);
        else         quadXZ(s.x1 - ROAD_HW, s.z1, s.x1 + ROAD_HW, s.z2, 0.07f);
        glDisable(GL_BLEND); glEnable(GL_LIGHTING);
        float cx = (s.x1 + s.x2) * 0.5f, cz = (s.z1 + s.z2) * 0.5f;     // road barrier
        glColor3f(0.95f, 0.5f, 0.05f);
        if (s.horiz) boxBase(cx, 0, cz, 0.3f, 0.9f, 3.6f); else boxBase(cx, 0, cz, 3.6f, 0.9f, 0.3f);
    }
}

static void drawPad(float cx, float cz) {
    glDisable(GL_LIGHTING); glEnable(GL_BLEND);
    glColor4f(0.1f, 0.8f, 0.3f, 0.55f);
    glBegin(GL_TRIANGLE_FAN);
    glVertex3f(cx, 0.08f, cz);
    for (int i = 0; i <= 24; i++) { float a = i * 2 * PI / 24; glVertex3f(cx + 4.5f * cosf(a), 0.08f, cz + 4.5f * sinf(a)); }
    glEnd();
    glDisable(GL_BLEND); glEnable(GL_LIGHTING);
    glColor3f(0.85f, 0.85f, 0.85f); boxBase(cx, 0, cz, 0.15f, 4.0f, 0.15f);
    glColor3f(0.1f, 0.7f, 0.25f);   box(cx + 0.9f, 3.4f, cz, 1.7f, 1.0f, 0.06f);
}

static void drawSafeZones() {
    drawPad(-22, 40); drawPad(22, 40); drawPad(-38, 36); drawPad(38, 36);
    if (!showSafe) return;
    float fz = std::max(floodZ(), RIVER_Z1);
    float pulse = 0.5f + 0.5f * sinf(animT * 3.f);
    glDisable(GL_LIGHTING); glEnable(GL_BLEND);
    glColor4f(1.f, 0.55f, 0.1f, 0.22f + 0.1f * pulse); quadXZ(-MAP, fz, MAP, std::min(fz + 4.f, MAP), 0.06f);   // danger band
    if (fz + 4.f < MAP) { glColor4f(0.1f, 0.9f, 0.3f, 0.16f + 0.06f * pulse); quadXZ(-MAP, fz + 4.f, MAP, MAP, 0.06f); } // safe ground
    glDisable(GL_BLEND); glEnable(GL_LIGHTING);
}

// Safe route display: shortest unblocked route from every reachable junction to the shelter
static void drawRouteTree() {
    glDisable(GL_LIGHTING); glEnable(GL_BLEND);
    for (int n = 0; n < SNODE; n++) {
        if (!reach[n]) continue;
        float x1 = nodeX(n), z1 = nodeZ(n), x2 = nodeX(par[n]), z2 = nodeZ(par[n]);
        glColor4f(0.1f, 1.f, 0.35f, 0.55f);
        quadXZ(std::min(x1, x2) - 0.55f, std::min(z1, z2) - 0.55f, std::max(x1, x2) + 0.55f, std::max(z1, z2) + 0.55f, 0.09f);
        float dx = x2 - x1, dz = z2 - z1, L = sqrtf(dx * dx + dz * dz); dx /= L; dz /= L;
        glColor4f(1.f, 1.f, 1.f, 0.95f);
        glBegin(GL_TRIANGLES);
        for (float s = fmodf(animT * 5.f, 3.f); s < L; s += 3.f) {
            float px = x1 + dx * s, pz = z1 + dz * s, qx = -dz, qz = dx;
            glNormal3f(0, 1, 0);
            glVertex3f(px + dx * 0.9f, 0.11f, pz + dz * 0.9f);
            glVertex3f(px - dx * 0.5f + qx * 0.7f, 0.11f, pz - dz * 0.5f + qz * 0.7f);
            glVertex3f(px - dx * 0.5f - qx * 0.7f, 0.11f, pz - dz * 0.5f - qz * 0.7f);
        }
        glEnd();
    }
    glDisable(GL_BLEND); glEnable(GL_LIGHTING);
}

static void drawHouse(const House &h) {
    static const float wall[4][3] = { {0.93f,0.87f,0.72f}, {0.85f,0.75f,0.65f}, {0.75f,0.85f,0.90f}, {0.90f,0.80f,0.80f} };
    static const float roof[3][3] = { {0.70f,0.25f,0.20f}, {0.35f,0.40f,0.50f}, {0.50f,0.30f,0.20f} };
    glColor3fv(wall[h.style % 4]); boxBase(h.x, 0, h.z, 5, 3.2f, 5);
    glColor3fv(roof[h.style % 3]);
    glPushMatrix(); glTranslatef(h.x, 3.2f, h.z); glRotatef(-90, 1, 0, 0); glRotatef(45, 0, 0, 1);
    glutSolidCone(4.6, 2.2, 4, 1); glPopMatrix();
    glColor3f(0.35f, 0.22f, 0.12f); box(h.x, 0.9f, h.z + 2.51f, 1.0f, 1.8f, 0.08f);
    glColor3f(0.5f, 0.75f, 0.9f);
    box(h.x - 1.5f, 2.0f, h.z + 2.51f, 0.8f, 0.8f, 0.06f); box(h.x + 1.5f, 2.0f, h.z + 2.51f, 0.8f, 0.8f, 0.06f);
}

static void drawTree(const Tree &t) {
    glPushMatrix(); glTranslatef(t.x, 0, t.z); glScalef(t.s, t.s, t.s);
    glColor3f(0.4f, 0.26f, 0.13f); box(0, 0.9f, 0, 0.45f, 1.8f, 0.45f);
    glColor3f(0.12f, 0.45f, 0.18f);
    glPushMatrix(); glTranslatef(0, 1.4f, 0); glRotatef(-90, 1, 0, 0); glutSolidCone(1.6, 2.6, 10, 2); glPopMatrix();
    glColor3f(0.16f, 0.52f, 0.2f);
    glPushMatrix(); glTranslatef(0, 2.8f, 0); glRotatef(-90, 1, 0, 0); glutSolidCone(1.2, 2.2, 10, 2); glPopMatrix();
    glPopMatrix();
}

static float levelY(int lvl) { return lvl == 0 ? 0.3f : lvl * FLOOR_H + 0.4f; }

static void drawCrowd(int n) {
    for (int k = 0; k < n; k++) {
        int lvl = k % 5;
        float x = (hash01(k * 3 + 1) * 2 - 1) * (SH_HALF - 1.2f);
        float z = (hash01(k * 7 + 5) * 2 - 1) * (SH_HALF - 1.2f);
        float y = levelY(lvl);
        glPushMatrix(); glTranslatef(x, y, z);
        glColor3f(0.3f + 0.7f * hash01(k * 11), 0.3f + 0.7f * hash01(k * 13), 0.3f + 0.7f * hash01(k * 17));
        box(0, 0.55f, 0, 0.5f, 0.8f, 0.32f);
        glColor3f(0.95f, 0.78f, 0.62f);
        glPushMatrix(); glTranslatef(0, 1.2f, 0); glutSolidSphere(0.2, 8, 6); glPopMatrix();
        glPopMatrix();
    }
}

static void drawSign3D(const char *s, float width, float cx, float cy, float cz) {
    glDisable(GL_LIGHTING);
    float len = glutStrokeLength(GLUT_STROKE_ROMAN, (const unsigned char *)s);
    float sc = width / len;
    glPushMatrix(); glTranslatef(cx, cy, cz); glRotatef(180, 0, 1, 0); glScalef(sc, sc, sc);
    glTranslatef(-len * 0.5f, -50.f, 0);
    glColor3f(1, 1, 1); glLineWidth(3.f);
    for (; *s; ++s) glutStrokeCharacter(GLUT_STROKE_ROMAN, *s);
    glPopMatrix(); glLineWidth(1.f);
    glEnable(GL_LIGHTING);
}

static void drawShelter(int crowd) {
    glPushMatrix(); glTranslatef(SH_X, 0, SH_Z);
    const float W = 2 * SH_HALF;
    glColor3f(0.55f, 0.55f, 0.55f); boxBase(0, 0, 0, W + 2, 0.3f, W + 2);                 // plinth
    for (int s = 1; s <= 4; s++) { glColor3f(0.86f, 0.86f, 0.82f); boxBase(0, s * FLOOR_H, 0, W, 0.4f, W); } // slabs
    glColor3f(0.72f, 0.72f, 0.72f);                                                          // pillars
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) {
        float px = -7.5f + i * 5.f, pz = -7.5f + j * 5.f;
        boxBase(px, 0.3f, pz, 0.8f, 4 * FLOOR_H - 0.3f, 0.8f);
    }
    glColor3f(0.9f, 0.9f, 0.86f); boxBase(0, 0.3f, SH_HALF - 0.2f, W, 4 * FLOOR_H, 0.3f);   // back wall
    for (int s = 1; s <= 4; s++) {                                                           // railings
        float y = s * FLOOR_H + 0.4f;
        glColor3f(s % 2 ? 0.15f : 0.9f, s % 2 ? 0.45f : 0.9f, s % 2 ? 0.75f : 0.9f);
        boxBase(0, y, -SH_HALF + 0.1f, W, 1.0f, 0.15f);
        boxBase(-SH_HALF + 0.1f, y, 0, 0.15f, 1.0f, W);
        boxBase(SH_HALF - 0.1f, y, 0, 0.15f, 1.0f, W);
    }
    // sign board on the roof
    float ry = 4 * FLOOR_H + 0.4f;
    glColor3f(0.8f, 0.8f, 0.8f);
    boxBase(-5.5f, ry, -SH_HALF + 0.1f, 0.3f, 1.3f, 0.3f); boxBase(5.5f, ry, -SH_HALF + 0.1f, 0.3f, 1.3f, 0.3f);
    glColor3f(0.05f, 0.5f, 0.22f); box(0, ry + 1.9f, -SH_HALF - 0.1f, 13.f, 2.6f, 0.3f);
    drawSign3D("CYCLONE SHELTER", 11.5f, 0, ry + 1.9f, -SH_HALF - 0.3f);
    // flag
    glColor3f(0.85f, 0.85f, 0.85f); boxBase(SH_HALF - 1.f, ry, SH_HALF - 1.f, 0.12f, 5.f, 0.12f);
    glColor3f(0.1f, 0.7f, 0.25f);  box(SH_HALF - 1.9f, ry + 4.3f, SH_HALF - 1.f, 1.7f, 1.0f, 0.05f);
    drawCrowd(crowd);
    glPopMatrix();
}

static void drawPerson(const Person &p) {
    if (p.st == P_SAFE) return;
    float y = 0.f;
    if (p.st == P_BOAT) y = waterY() + 0.12f + 0.05f * sinf(animT * 2.f + p.boat) + 0.5f;
    float bob = (p.st == P_WALK || p.st == P_TOSHELTER) ? 0.08f * fabsf(sinf(animT * 10.f + p.phase)) : 0.f;
    glPushMatrix(); glTranslatef(p.x, y + bob, p.z);
    glColor3f(0.2f, 0.2f, 0.28f); box(0, 0.2f, 0, 0.4f, 0.4f, 0.3f);
    glColor3f(p.r, p.g, p.b);     box(0, 0.8f, 0, 0.55f, 0.8f, 0.35f);
    glColor3f(0.95f, 0.78f, 0.62f);
    glPushMatrix(); glTranslatef(0, 1.45f, 0); glutSolidSphere(0.25, 10, 8); glPopMatrix();
    if (p.st == P_STRAND) {                                   // raised arms + blinking beacon
        box(-0.4f, 1.4f, 0, 0.14f, 0.6f, 0.14f); box(0.4f, 1.4f, 0, 0.14f, 0.6f, 0.14f);
        if (sinf(animT * 6.f + p.phase) > 0.f) { glColor3f(1.f, 0.4f, 0.05f); glPushMatrix(); glTranslatef(0, 2.4f, 0); glutSolidSphere(0.22, 8, 6); glPopMatrix(); }
    }
    glPopMatrix();
}

static void drawBoat(const Boat &b, int i) {
    float y = waterY() + 0.12f + 0.05f * sinf(animT * 2.f + i);
    glPushMatrix(); glTranslatef(b.x, y, b.z); glRotatef(b.ang * 180.f / PI, 0, 1, 0);
    glColor3f(0.95f, 0.45f, 0.10f); box(0, 0.2f, 0, 1.8f, 0.7f, 4.4f);
    glPushMatrix(); glTranslatef(0, 0.2f, 2.2f); glRotatef(45, 0, 1, 0); glScalef(1.27f, 0.7f, 1.27f); glutSolidCube(1.0); glPopMatrix();
    glColor3f(0.95f, 0.95f, 0.95f); box(0, 0.58f, 0, 1.9f, 0.14f, 4.5f);
    box(0, 1.1f, -1.3f, 1.2f, 0.9f, 1.2f);
    glColor3f(0.85f, 0.1f, 0.1f); box(0, 1.15f, -1.91f, 0.5f, 0.15f, 0.05f); box(0, 1.15f, -1.91f, 0.15f, 0.5f, 0.05f);
    glColor3f(0.4f, 0.4f, 0.4f); boxBase(0, 1.5f, -1.3f, 0.08f, 0.8f, 0.08f);
    if (sinf(animT * 8.f + i) > 0.f) { glColor3f(0.2f, 0.4f, 1.f); glPushMatrix(); glTranslatef(0, 2.4f, -1.3f); glutSolidSphere(0.18, 8, 6); glPopMatrix(); }
    glPopMatrix();
}

static float wave(float x, float z) { return 0.06f * sinf(0.6f * x + animT * 1.8f) * cosf(0.5f * z + animT * 1.4f); }

static void drawWater() {
    float wy = waterY(), zEnd = std::max(floodZ(), RIVER_Z1);
    glEnable(GL_BLEND); glDepthMask(GL_FALSE);
    glColor4f(0.13f, 0.40f, 0.62f, 0.70f);
    quadXZ(-300, RIVER_Z0, -55, zEnd, wy); quadXZ(55, RIVER_Z0, 300, zEnd, wy);
    const float st = 2.5f; const int n = 44;
    for (float z = RIVER_Z0; z < zEnd - 0.001f; z += st) {
        float z2 = std::min(z + st, zEnd);
        glBegin(GL_QUAD_STRIP);
        for (int i = 0; i <= n; i++) {
            float x = -55.f + i * st;
            glNormal3f(0, 1, 0);
            glVertex3f(x, wy + wave(x, z), z);
            glVertex3f(x, wy + wave(x, z2), z2);
        }
        glEnd();
    }
    if (floodZ() > RIVER_Z1) {                         // foam line at the flood front
        glDisable(GL_LIGHTING); glColor4f(1, 1, 1, 0.55f);
        quadXZ(-300, zEnd - 0.3f, 300, zEnd + 0.3f, wy + 0.08f);
        glEnable(GL_LIGHTING);
    }
    glDepthMask(GL_TRUE); glDisable(GL_BLEND);
}

static void drawRain() {
    if (!showRain || flood < 0.05f) return;
    int n = std::min(NRAIN, (int)(150 + flood * NRAIN * 0.9f));
    glDisable(GL_LIGHTING); glEnable(GL_BLEND); glLineWidth(1.f);
    glColor4f(0.75f, 0.8f, 0.9f, 0.45f);
    glBegin(GL_LINES);
    for (int i = 0; i < n; i++) { glVertex3f(rainX[i], rainY[i], rainZ[i]); glVertex3f(rainX[i] - 0.2f, rainY[i] - 1.4f, rainZ[i] - 0.1f); }
    glEnd();
    glDisable(GL_BLEND); glEnable(GL_LIGHTING);
}

// ------------------------------- HUD ---------------------------------------
static void rect2D(float x1, float y1, float x2, float y2) {
    glBegin(GL_QUADS); glVertex2f(x1, y1); glVertex2f(x2, y1); glVertex2f(x2, y2); glVertex2f(x1, y2); glEnd();
}
static void text2D(float x, float y, const char *s, void *font) {
    glRasterPos2f(x, y); while (*s) glutBitmapCharacter(font, *s++);
}

static void drawHUD(int sheltered, int waiting, int crowd) {
    int blocked = 0; for (size_t i = 0; i < segs.size(); i++) if (segBlocked(segs[i])) blocked++;
    int stage = 1 + std::min(4, (int)(flood * 5.f));
    static const char *names[5] = { "Normal", "Rising", "High", "Severe", "Extreme" };
    int connected = 0; for (int i = 0; i < SNODE; i++) if (reach[i]) connected++;
    int total = (int)people.size();

    glMatrixMode(GL_PROJECTION); glPushMatrix(); glLoadIdentity(); glOrtho(0, winW, 0, winH, -1, 1);
    glMatrixMode(GL_MODELVIEW);  glPushMatrix(); glLoadIdentity();
    glDisable(GL_LIGHTING); glDisable(GL_DEPTH_TEST); glDisable(GL_FOG); glEnable(GL_BLEND);

    float px = 10, py = winH - 10, pw = 370, ph = 300;
    glColor4f(0.03f, 0.07f, 0.13f, 0.80f); rect2D(px, py - ph, px + pw, py);
    glColor4f(0.2f, 0.6f, 1.f, 0.9f);      rect2D(px, py - 4, px + pw, py);
    char buf[128];
    float y = py - 28;
    void *F = GLUT_BITMAP_9_BY_15;
    glColor3f(1, 1, 1); text2D(px + 10, y, "FLOOD ESCAPE & CYCLONE SHELTER RESCUE", F); y -= 26;

    const char *stat = simState == ST_IDLE ? "READY  (press S to start)" : simState == ST_PAUSE ? "PAUSED" : "RUNNING";
    if (sheltered == total) stat = "ALL RESIDENTS ARE SAFE";
    snprintf(buf, sizeof buf, "Status        : %s", stat);                       glColor3f(0.8f, 0.9f, 1.f); text2D(px + 10, y, buf, F); y -= 22;
    snprintf(buf, sizeof buf, "Flood Stage   : %d / 5 (%s)", stage, names[stage - 1]);
    glColor3f(1.f, 0.8f - 0.12f * stage, 0.3f);                                  text2D(px + 10, y, buf, F); y -= 22;
    snprintf(buf, sizeof buf, "Water Rise    : %.1f m", flood * 4.5f);           glColor3f(0.5f, 0.8f, 1.f); text2D(px + 10, y, buf, F); y -= 22;
    snprintf(buf, sizeof buf, "Blocked Roads : %d / %d", blocked, (int)segs.size());
    glColor3f(blocked ? 1.f : 0.6f, blocked ? 0.35f : 1.f, 0.35f);               text2D(px + 10, y, buf, F); y -= 22;
    snprintf(buf, sizeof buf, "Safe Route    : %s", connected > 0 ? "OPEN to shelter" : "ALL ROUTES CUT");
    glColor3f(connected > 0 ? 0.3f : 1.f, connected > 0 ? 1.f : 0.3f, 0.3f);     text2D(px + 10, y, buf, F); y -= 22;
    snprintf(buf, sizeof buf, "Sheltered     : %d / %d residents", sheltered, total);
    glColor3f(0.3f, 1.f, 0.5f);                                                  text2D(px + 10, y, buf, F); y -= 22;
    snprintf(buf, sizeof buf, "Waiting Rescue: %d", waiting);                    glColor3f(1.f, 0.7f, 0.2f); text2D(px + 10, y, buf, F); y -= 22;
    snprintf(buf, sizeof buf, "Boat Rescues  : %d", rescued);                    glColor3f(1.f, 0.6f, 0.3f); text2D(px + 10, y, buf, F); y -= 22;
    snprintf(buf, sizeof buf, "Shelter Crowd : %d / %d", crowd, SHELTER_CAP);    glColor3f(0.9f, 0.9f, 0.5f); text2D(px + 10, y, buf, F); y -= 22;
    snprintf(buf, sizeof buf, "Sim Speed     : x%.1f", simSpeed);                glColor3f(0.8f, 0.8f, 0.8f); text2D(px + 10, y, buf, F); y -= 16;
    glColor4f(0.2f, 0.2f, 0.25f, 0.9f); rect2D(px + 10, y - 6, px + pw - 10, y + 2);
    glColor4f(0.2f, 0.6f, 1.f, 1.f);    rect2D(px + 10, y - 6, px + 10 + (pw - 20) * flood, y + 2);

    glColor4f(0.03f, 0.07f, 0.13f, 0.8f); rect2D(0, 0, (float)winW, 26);
    glColor3f(0.9f, 0.9f, 0.9f);
    text2D(10, 9, "[S] Start  [P] Pause  [C] Resume  [R] Reset  |  Drag: rotate  Wheel: zoom  |  1-4: views  Z: safe zones  N: rain  [ ]: speed",
           GLUT_BITMAP_8_BY_13);

    glEnable(GL_FOG); glEnable(GL_DEPTH_TEST); glEnable(GL_LIGHTING); glDisable(GL_BLEND);
    glMatrixMode(GL_PROJECTION); glPopMatrix();
    glMatrixMode(GL_MODELVIEW);  glPopMatrix();
}

// ------------------------------- Callbacks ---------------------------------
static void display() {
    float k = std::min(1.f, flood * 1.3f);
    float sr = 0.55f - 0.23f * k, sg = 0.75f - 0.37f * k, sb = 0.95f - 0.50f * k;
    glClearColor(sr, sg, sb, 1.f);
    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
    GLfloat fc[4] = { sr, sg, sb, 1.f }; glFogfv(GL_FOG_COLOR, fc);
    GLfloat dif[4] = { 0.9f - 0.3f * k, 0.9f - 0.3f * k, 0.85f - 0.25f * k, 1.f }; glLightfv(GL_LIGHT0, GL_DIFFUSE, dif);

    glMatrixMode(GL_MODELVIEW); glLoadIdentity();
    float cp = cosf(camPitch * PI / 180.f), sp = sinf(camPitch * PI / 180.f);
    float cy = cosf(camYaw * PI / 180.f), sy = sinf(camYaw * PI / 180.f);
    lookAt(camTX + camDist * cp * sy, camTY + camDist * sp, camTZ + camDist * cp * cy, camTX, camTY, camTZ);
    GLfloat lp[4] = { 0.5f, 1.0f, 0.35f, 0.f }; glLightfv(GL_LIGHT0, GL_POSITION, lp);

    int sheltered = 0, waiting = 0;
    for (size_t i = 0; i < people.size(); i++) { if (people[i].st == P_SAFE) sheltered++; if (people[i].st == P_STRAND) waiting++; }
    int arrivals = simState == ST_IDLE ? 0 : (int)(flood * 260.f);
    int crowd = std::min(SHELTER_CAP, sheltered + arrivals);

    drawGround(); drawRoads(); drawBlocked(); drawSafeZones(); drawRouteTree();
    for (size_t i = 0; i < houses.size(); i++) drawHouse(houses[i]);
    for (size_t i = 0; i < trees.size(); i++) drawTree(trees[i]);
    drawShelter(crowd);
    for (size_t i = 0; i < people.size(); i++) drawPerson(people[i]);
    for (size_t i = 0; i < boats.size(); i++) drawBoat(boats[i], (int)i);
    drawWater();
    drawRain();
    drawHUD(sheltered, waiting, crowd);
    glutSwapBuffers();
}

static void reshape(int w, int h) {
    if (h == 0) h = 1;
    winW = w; winH = h;
    glViewport(0, 0, w, h);
    glMatrixMode(GL_PROJECTION); glLoadIdentity(); setPerspective(50.f, (float)w / h, 1.f, 1200.f);
    glMatrixMode(GL_MODELVIEW);
}

static void timer(int) {
    int now = glutGet(GLUT_ELAPSED_TIME);
    float dt = (now - lastT) / 1000.f; lastT = now;
    if (dt > 0.1f) dt = 0.1f;
    if (simState != ST_PAUSE) animT += dt;
    updateSim(dt);
    glutPostRedisplay();
    glutTimerFunc(16, timer, 0);
}

static void startSim()  { if (simState == ST_IDLE)  simState = ST_RUN; }
static void pauseSim()  { if (simState == ST_RUN)   simState = ST_PAUSE; }
static void resumeSim() { if (simState == ST_PAUSE) simState = ST_RUN; }

static void setView(float tx, float ty, float tz, float d, float yaw, float pitch) {
    camTX = tx; camTY = ty; camTZ = tz; camDist = d; camYaw = yaw; camPitch = pitch;
}

static void keyboard(unsigned char k, int, int) {
    switch (k) {
    case 's': case 'S': startSim(); break;
    case 'p': case 'P': pauseSim(); break;
    case 'c': case 'C': resumeSim(); break;
    case 'r': case 'R': initWorld(); break;
    case 'z': case 'Z': showSafe = !showSafe; break;
    case 'n': case 'N': showRain = !showRain; break;
    case '[': simSpeed = std::max(0.5f, simSpeed - 0.5f); break;
    case ']': simSpeed = std::min(4.0f, simSpeed + 0.5f); break;
    case '+': case '=': camDist = std::max(25.f, camDist * 0.92f); break;
    case '-': case '_': camDist = std::min(300.f, camDist * 1.08f); break;
    case '1': setView(0, 0, 5, 135, 200, 38); break;
    case '2': setView(0, 6, 42, 55, 200, 22); break;
    case '3': setView(0, 0, -15, 70, 150, 28); break;
    case '4': setView(0, 0, 5, 150, 180, 85); break;
    case 27: exit(0);
    }
}
static void special(int k, int, int) {
    switch (k) {
    case GLUT_KEY_LEFT:  camYaw -= 5.f; break;
    case GLUT_KEY_RIGHT: camYaw += 5.f; break;
    case GLUT_KEY_UP:    camPitch = std::min(85.f, camPitch + 4.f); break;
    case GLUT_KEY_DOWN:  camPitch = std::max(8.f, camPitch - 4.f); break;
    }
}
static void mouse(int b, int s, int x, int y) {
    if (b == GLUT_LEFT_BUTTON) { dragging = (s == GLUT_DOWN); lastMX = x; lastMY = y; }
}
static void motion(int x, int y) {
    if (!dragging) return;
    camYaw -= (x - lastMX) * 0.35f;
    camPitch += (y - lastMY) * 0.35f;
    camPitch = std::max(8.f, std::min(85.f, camPitch));
    lastMX = x; lastMY = y;
}
static void wheel(int, int dir, int, int) {
    camDist *= dir > 0 ? 0.92f : 1.08f;
    camDist = std::max(25.f, std::min(300.f, camDist));
}
static void menuCb(int id) {
    switch (id) {
    case 1: startSim(); break;
    case 2: pauseSim(); break;
    case 3: resumeSim(); break;
    case 4: initWorld(); break;
    case 5: showRain = !showRain; break;
    case 6: showSafe = !showSafe; break;
    }
}

static void initGL() {
    glEnable(GL_DEPTH_TEST);
    glEnable(GL_LIGHTING); glEnable(GL_LIGHT0);
    glEnable(GL_COLOR_MATERIAL); glColorMaterial(GL_FRONT_AND_BACK, GL_AMBIENT_AND_DIFFUSE);
    glEnable(GL_NORMALIZE); glShadeModel(GL_SMOOTH);
    GLfloat amb[4] = { 0.42f, 0.42f, 0.46f, 1.f }; glLightModelfv(GL_LIGHT_MODEL_AMBIENT, amb);
    glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
    glEnable(GL_FOG); glFogi(GL_FOG_MODE, GL_LINEAR); glFogf(GL_FOG_START, 200.f); glFogf(GL_FOG_END, 600.f);
}

int main(int argc, char **argv) {
    glutInit(&argc, argv);
    glutInitDisplayMode(GLUT_DOUBLE | GLUT_RGB | GLUT_DEPTH);
    glutInitWindowSize(winW, winH);
    glutInitWindowPosition(60, 40);
    glutCreateWindow("Flood Escape and Cyclone Shelter Rescue Simulator (3D)");
    initGL();
    initWorld();

    glutDisplayFunc(display);
    glutReshapeFunc(reshape);
    glutKeyboardFunc(keyboard);
    glutSpecialFunc(special);
    glutMouseFunc(mouse);
    glutMotionFunc(motion);
    glutMouseWheelFunc(wheel);

    glutCreateMenu(menuCb);
    glutAddMenuEntry("Start", 1);
    glutAddMenuEntry("Pause", 2);
    glutAddMenuEntry("Resume", 3);
    glutAddMenuEntry("Reset", 4);
    glutAddMenuEntry("Toggle Rain", 5);
    glutAddMenuEntry("Toggle Safe-Zone Overlay", 6);
    glutAttachMenu(GLUT_RIGHT_BUTTON);

    lastT = glutGet(GLUT_ELAPSED_TIME);
    glutTimerFunc(16, timer, 0);
    glutMainLoop();
    return 0;
}