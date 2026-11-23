// ============================================================================
//  FLOOD ESCAPE & CYCLONE SHELTER RESCUE SIMULATOR  -  realistic edition (v2)
//  3D, C++ / OpenGL (fixed pipeline) / freeglut  (+ WinMM for generated sound)
//
//  What is in this version
//   * a full landscape: river valley, paddy fields, villages, hills and
//     mountains up to the horizon, sky dome with sun / moon / stars / storm
//     clouds, fog and distance haze  (no more "floating piece of land")
//   * DAY / NIGHT mode (N): street lamps, lit windows, car lights, boat
//     search-lights, power cut when the flood becomes dangerous
//   * 4 camera views
//        1 Overview (orbit)   2 Person view (walk on foot)
//        3 Top view           4 Ride a rescue boat
//   * people with a walk cycle, wading in water, stranded on roofs waving
//   * RESCUE BOATS with crews: they find stranded / wading people, sound the
//     siren, people board the boat, the boat brings them to the shelter landing
//   * weather: rain that grows into a cyclone, wind that bends trees,
//     lightning with delayed thunder (speed of sound)
//   * generated sound (no .wav files needed): rain, wind, thunder, boat engines,
//     rescue sirens, shelter warning siren, flood water, birds / crickets.
//     Sounds are positional (left / right, near / far).
//
//  Compile (MSYS2 MINGW64 terminal):
//     g++ main.cpp -o main.exe -O2 -lfreeglut -lopengl32 -lglu32 -lwinmm
//  Run:
//     ./main.exe
//
//  CONTROLS
//    ENTER / SPACE ... start  (SPACE = pause/resume)   P pause   R reset
//    1 2 3 4 ......... Overview / Person / Top / Boat view   V next view
//    B ............... next rescue boat (boat view)
//    W A S D ......... walk (person) / move camera (overview, top)   SHIFT = fast
//    Arrow keys ...... look / rotate        Mouse L-drag look/rotate, R-drag pan
//    Q / E ........... lower / raise (person: climb up to look around), wheel zoom
//    N day/night   F sim speed   M sound on/off   H hide panel   F11 fullscreen
// ============================================================================
#define _USE_MATH_DEFINES
#ifdef _WIN32
#ifndef NOMINMAX
#define NOMINMAX
#endif
#include <windows.h>
#include <mmsystem.h>
#endif
#include <GL/freeglut.h>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cctype>
#include <vector>
#include <algorithm>

static const float PI = 3.14159265f;
static const float DEG = PI / 180.0f;

// ----------------------------------------------------------------------------
//  Small utilities
// ----------------------------------------------------------------------------
static unsigned int g_rs = 2024u;
static float rnd() { g_rs = g_rs * 1664525u + 1013904223u; return ((g_rs >> 8) & 0xFFFF) / 65535.0f; }
static float rr(float a, float b) { return a + (b - a) * rnd(); }
static float len2(float a, float b) { return sqrtf(a * a + b * b); }
static float clampf(float v, float a, float b) { return v < a ? a : (v > b ? b : v); }
static float clamp01(float v) { return clampf(v, 0.0f, 1.0f); }
static float mixf(float a, float b, float t) { return a + (b - a) * t; }
static float smooth01(float t) { t = clamp01(t); return t * t * (3 - 2 * t); }
static float wrapAng(float a) { while (a > PI) a -= 2 * PI; while (a < -PI) a += 2 * PI; return a; }
static float hash2(int a, int b) {
    unsigned int h = (unsigned int)a * 374761393u + (unsigned int)b * 668265263u;
    h = (h ^ (h >> 13)) * 1274126177u;
    return ((h ^ (h >> 16)) & 0xFFFF) / 65535.0f;
}

// ----------------------------------------------------------------------------
//  World constants
// ----------------------------------------------------------------------------
static const float WORLD = 100.0f;      // simulated town: -100 .. +100
static const int   GN = 100;            // terrain / navigation grid cells per side
static const float CELL = 2.0f;
static const float OUTER = 520.0f, OCELL = 20.0f;   // surrounding landscape
static const float SHX = 40.0f, SHZ = 48.0f, PAD = 4.2f;   // cyclone shelter position / ground height
static const float WATER_START = -0.3f, WATER_MAX = 3.3f, RISE_RATE = 0.045f;
static const int   NBOAT = 5, BOAT_CAP = 8;

// ----------------------------------------------------------------------------
//  Simulation state
// ----------------------------------------------------------------------------
static float waterLevel = WATER_START;
static bool  started = false, running = false;
static int   speedMul = 1;
static float rt = 0.0f, simT = 0.0f, peakT = -1.0f;
static int   lastT = 0;
static int   sheltered = 0, boatRescued = 0, lastStage = 0;
static bool  powerOn = true;
static float shelterSirenT = 0.0f;

// weather & time of day
static bool  nightMode = false;
static float night = 0.0f;                       // 0 = day, 1 = night (smooth)
static float rainAmt = 0.0f, rainTarget = 0.0f, windAmt = 0.12f, storm = 0.1f;
static float flash = 0.0f, boltLife = 0.0f, nextBolt = 8.0f;
static float boltP[16][3]; static int boltN = 0;
static const float windX = 0.94f, windZ = 0.34f;  // wind direction (unit)

// camera
enum { V_OVER = 0, V_PERSON, V_TOP, V_BOAT };
static const char* VIEW_NAMES[4] = { "Overview", "Person view (on foot)", "Top view", "Rescue boat" };
static int   viewMode = V_OVER;
static float camYaw = 20, camPitch = 36, camDist = 150, tgx = 0, tgy = 0, tgz = 18;
static float topH = 190;
static float pX = 6, pZ = 3, pYaw = 70, pPitch = -4, pLift = 0;
static int   boatCam = 0;
static float bLookYaw = 0, bLookPitch = -6;
static float eyeX = 0, eyeY = 0, eyeZ = 0, fovDeg = 45;
static float lisX = 0, lisY = 0, lisZ = 0, lisRX = 1, lisRZ = 0;   // sound listener
static float fwdX = 0, fwdY = 0, fwdZ = -1;
static bool  keys[256], sKeys[4];
static bool  shiftHeld = false;
static int   winW = 1280, winH = 720;
static bool  fullScr = true, soundOn = true, showHUD = true;
static GLuint sceneList = 0;

static char  hudMsg[200] = "Press START (or ENTER) to begin the cyclone.  1-4 = views,  N = day / night.";
static float hudMsgT = 12.0f;
static void setMsg(const char* m) { snprintf(hudMsg, sizeof hudMsg, "%s", m); hudMsgT = 6.0f; }

// ----------------------------------------------------------------------------
//  Terrain height (river valley + banks + hills + far mountains + shelter hill)
// ----------------------------------------------------------------------------
static float riverZ(float x) { return -30.0f + 10.0f * sinf(x * 0.04f); }

static float terrainH(float x, float z) {
    float d = fabsf(z - riverZ(x));
    float h;
    if (d < 7.0f)        h = -2.0f + d * 0.35f;
    else if (d < 100.0f) h = 0.45f + (d - 7.0f) * 0.05f;
    else                 h = 5.1f + (d - 100.0f) * 0.012f;
    h += 0.18f * sinf(x * 0.31f) * cosf(z * 0.27f);
    float e = std::max(0.0f, fabsf(z - 10.0f) - 60.0f);          // hills north & south of the valley
    if (e > 0) {
        float k = clamp01(e / 20.0f);
        h += 24.0f * (1.0f - expf(-e / 30.0f))
           + k * (3.0f * sinf(x * 0.05f + z * 0.03f) * sinf(x * 0.021f - z * 0.04f) + 1.5f * sinf(x * 0.11f + 1.0f) * sinf(z * 0.09f));
    }
    float r = len2(x, z - 10.0f);                                  // far mountain ring
    if (r > 320.0f) { float a = atan2f(z - 10.0f, x); h += (r - 320.0f) * 0.22f * (0.65f + 0.35f * sinf(a * 7.0f + 1.3f) * sinf(a * 3.0f)); }
    float sd = len2(x - SHX, z - SHZ);
    if (sd < 14.0f) h = PAD;
    else if (sd < 24.0f) { float t = (sd - 14.0f) / 10.0f; h = PAD * (1 - t) + h * t; }
    return h;
}

// ----------------------------------------------------------------------------
//  Drawing helpers
// ----------------------------------------------------------------------------
static void normalOf(float ax, float ay, float az, float bx, float by, float bz, float cx, float cy, float cz) {
    float ux = bx - ax, uy = by - ay, uz = bz - az;
    float vx = cx - ax, vy = cy - ay, vz = cz - az;
    glNormal3f(uy * vz - uz * vy, uz * vx - ux * vz, ux * vy - uy * vx);
}
static void quadV(float ax, float ay, float az, float bx, float by, float bz,
                  float cx, float cy, float cz, float dx, float dy, float dz) {
    normalOf(ax, ay, az, bx, by, bz, cx, cy, cz);
    glVertex3f(ax, ay, az); glVertex3f(bx, by, bz); glVertex3f(cx, cy, cz); glVertex3f(dx, dy, dz);
}
// box whose bottom centre is (x,y,z)
static void boxB(float x, float y, float z, float w, float h, float d, float r, float g, float b) {
    glColor3f(r, g, b);
    glPushMatrix(); glTranslatef(x, y + h * 0.5f, z); glScalef(w, h, d); glutSolidCube(1.0); glPopMatrix();
}
// box whose centre is (x,y,z), current colour
static void boxC(float x, float y, float z, float w, float h, float d) {
    glPushMatrix(); glTranslatef(x, y, z); glScalef(w, h, d); glutSolidCube(1.0); glPopMatrix();
}
static void cylB(float x, float y, float z, float rad, float h, float r, float g, float b) {
    glColor3f(r, g, b);
    glPushMatrix(); glTranslatef(x, y, z); glRotatef(-90, 1, 0, 0); glutSolidCylinder(rad, h, 10, 1); glPopMatrix();
}

// ----------------------------------------------------------------------------
//  Light halos (street lamps, windows, sirens ...) - drawn as soft sprites
// ----------------------------------------------------------------------------
struct Glow { float x, y, z, r, g, b, s, k; };
static std::vector<Glow> glows;
static void addGlow(float x, float y, float z, float r, float g, float b, float s, float k) {
    float m[16]; glGetFloatv(GL_MODELVIEW_MATRIX, m);
    Glow gl;
    gl.x = m[0] * x + m[4] * y + m[8] * z + m[12];
    gl.y = m[1] * x + m[5] * y + m[9] * z + m[13];
    gl.z = m[2] * x + m[6] * y + m[10] * z + m[14];
    gl.r = r; gl.g = g; gl.b = b; gl.s = s; gl.k = k;
    glows.push_back(gl);
}
static void drawGlows() {
    glDisable(GL_LIGHTING); glDisable(GL_FOG);
    glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA, GL_ONE);
    glDepthMask(GL_FALSE); glEnable(GL_POINT_SMOOTH);
    glMatrixMode(GL_MODELVIEW); glPushMatrix(); glLoadIdentity();
    float K = winH * 0.5f / tanf(fovDeg * 0.5f * DEG);
    for (size_t i = 0; i < glows.size(); i++) {
        const Glow& g = glows[i];
        float depth = -g.z;
        if (depth < 0.3f) continue;
        float px = 2.0f * g.s * 4.5f * K / depth;
        if (px > 140) px = 140;
        if (px < 2) px = 2;
        float a = g.k;
        glPointSize(px);        glColor4f(g.r, g.g, g.b, 0.08f * a); glBegin(GL_POINTS); glVertex3f(g.x, g.y, g.z); glEnd();
        glPointSize(px * 0.5f); glColor4f(g.r, g.g, g.b, 0.18f * a); glBegin(GL_POINTS); glVertex3f(g.x, g.y, g.z); glEnd();
        glPointSize(std::max(2.0f, px * 0.18f)); glColor4f(1, 1, 1, 0.35f * a); glBegin(GL_POINTS); glVertex3f(g.x, g.y, g.z); glEnd();
    }
    glPopMatrix();
    glDisable(GL_POINT_SMOOTH); glDepthMask(GL_TRUE); glDisable(GL_BLEND);
    glEnable(GL_FOG); glEnable(GL_LIGHTING);
}

// stroke text on signs (centred, fits w x h)
static void signText(const char* s, float w, float h, float r, float g, float b) {
    float len = (float)glutStrokeLength(GLUT_STROKE_ROMAN, (const unsigned char*)s);
    float sc = std::min(w / len, h / 119.0f);
    glDisable(GL_LIGHTING);
    glColor3f(r, g, b);
    glLineWidth(2.0f);
    glPushMatrix();
    glTranslatef(-len * sc * 0.5f, -59.0f * sc, 0);
    glScalef(sc, sc, sc);
    for (const char* p = s; *p; p++) glutStrokeCharacter(GLUT_STROKE_ROMAN, *p);
    glPopMatrix();
    glLineWidth(1);
    glEnable(GL_LIGHTING);
}

// ----------------------------------------------------------------------------
//  Roads
// ----------------------------------------------------------------------------
struct Road { float x1, z1, x2, z2, w, len, thr; const char* name; };
static std::vector<Road> roads, extRoads;

static Road makeRoad(float x1, float z1, float x2, float z2, float w, const char* nm) {
    Road r; r.x1 = x1; r.z1 = z1; r.x2 = x2; r.z2 = z2; r.w = w;
    r.len = len2(x2 - x1, z2 - z1); r.thr = 1000.0f; r.name = nm;
    return r;
}
static void roadPoint(const Road& R, float t, float& x, float& z) {
    x = R.x1 + (R.x2 - R.x1) * t / R.len;
    z = R.z1 + (R.z2 - R.z1) * t / R.len;
}
static void initRoads() {
    roads.push_back(makeRoad(-90, 0, 90, 0, 5, "Main Road A"));
    roads.push_back(makeRoad(-90, 25, 90, 25, 5, "Main Road B"));
    roads.push_back(makeRoad(-75, -8, -75, 60, 4, "West Link"));
    roads.push_back(makeRoad(-40, -8, -40, 60, 4, "Market Road"));
    roads.push_back(makeRoad(0, -8, 0, 60, 4, "Central Road"));
    roads.push_back(makeRoad(40, -8, 40, 42, 5, "Shelter Road"));
    roads.push_back(makeRoad(75, -8, 75, 60, 4, "East Link"));
    for (size_t i = 0; i < roads.size(); i++) {
        float m = 1000.0f;
        for (float t = 0; t <= roads[i].len; t += 1.0f) {
            float x, z; roadPoint(roads[i], t, x, z);
            m = std::min(m, terrainH(x, z));
        }
        roads[i].thr = m + 0.1f;          // flood threshold of this road
    }
    // the two main roads continue out of town (highway to the next villages)
    extRoads.push_back(makeRoad(-500, 0, -90, 0, 5, ""));  extRoads.push_back(makeRoad(90, 0, 500, 0, 5, ""));
    extRoads.push_back(makeRoad(-500, 25, -90, 25, 5, "")); extRoads.push_back(makeRoad(90, 25, 500, 25, 5, ""));
}
static float distToSeg(float px, float pz, float ax, float az, float bx, float bz) {
    float vx = bx - ax, vz = bz - az;
    float t = ((px - ax) * vx + (pz - az) * vz) / (vx * vx + vz * vz);
    t = clampf(t, 0.0f, 1.0f);
    return len2(px - (ax + vx * t), pz - (az + vz * t));
}

// ----------------------------------------------------------------------------
//  Houses (different designs) + their windows (lit at night)
// ----------------------------------------------------------------------------
struct House { float x, z, y, w, d, ang; int type, floors; float wr, wg, wb, pr, pg, pb; };
static std::vector<House> houses, outerHouses;

struct WinL { float x, y, z, ax, az, hh, nx, nz, seed; };
static std::vector<WinL> winLights;
static const House* g_curH = 0;

static const float WALLC[7][3] = {
    {0.96f, 0.92f, 0.80f}, {0.98f, 0.85f, 0.70f}, {0.85f, 0.90f, 0.96f}, {0.96f, 0.80f, 0.80f},
    {0.90f, 0.95f, 0.84f}, {0.90f, 0.78f, 0.60f}, {0.76f, 0.48f, 0.38f} };
static const float ROOFC[6][3] = {
    {0.72f, 0.28f, 0.20f}, {0.55f, 0.33f, 0.20f}, {0.30f, 0.40f, 0.55f},
    {0.35f, 0.50f, 0.35f}, {0.85f, 0.55f, 0.25f}, {0.60f, 0.20f, 0.25f} };
static const float TINC[3][3] = { {0.45f, 0.62f, 0.75f}, {0.62f, 0.66f, 0.68f}, {0.35f, 0.60f, 0.50f} };

static House newHouse(int type, float ang) {
    House H; H.type = type; H.ang = ang; H.floors = 1;
    switch (type) {
    case 0: H.w = rr(6, 8);  H.d = rr(5, 6);   H.floors = 1; break;
    case 1: H.w = rr(7, 9);  H.d = rr(6, 7);   H.floors = 2; break;
    case 2: H.w = rr(9, 12); H.d = rr(6, 7);   H.floors = 3 + (int)(rnd() * 2.99f); break;
    default: H.w = rr(9, 12); H.d = rr(4.5f, 5.5f); H.floors = 1; break;
    }
    int wi = (int)(rnd() * 6.99f);
    H.wr = WALLC[wi][0]; H.wg = WALLC[wi][1]; H.wb = WALLC[wi][2];
    if (type == 3) { int ti = (int)(rnd() * 2.99f); H.pr = TINC[ti][0]; H.pg = TINC[ti][1]; H.pb = TINC[ti][2]; }
    else           { int ri = (int)(rnd() * 5.99f); H.pr = ROOFC[ri][0]; H.pg = ROOFC[ri][1]; H.pb = ROOFC[ri][2]; }
    H.x = H.z = H.y = 0;
    return H;
}
static void setHouseY(House& H) {
    float r = std::max(H.w, H.d) / 2.0f, m = terrainH(H.x, H.z);
    m = std::max(m, terrainH(H.x - r, H.z - r)); m = std::max(m, terrainH(H.x + r, H.z - r));
    m = std::max(m, terrainH(H.x - r, H.z + r)); m = std::max(m, terrainH(H.x + r, H.z + r));
    H.y = m;
}
// height people stand at when they climb onto the roof
static float houseRoofStand(const House& H) {
    switch (H.type) {
    case 0: return H.y + 3.2f + 2.3f;
    case 1: return H.y + 6.2f + 2.6f;
    case 2: return H.y + 3.0f * H.floors + 0.5f;
    default: return H.y + 2.7f + 0.6f;
    }
}
// footprint half sizes in world axes (houses are rotated by multiples of 90 deg)
static void houseHalf(const House& H, float& hx, float& hz) {
    int q = ((int)(H.ang / 90.0f + 0.5f)) & 1;
    hx = (q ? H.d : H.w) * 0.5f; hz = (q ? H.w : H.d) * 0.5f;
}

static void recordWin(float lx, float ly, float lz, float hw, float hh, float zs) {
    if (!g_curH) return;
    const House& H = *g_curH;
    float a = H.ang * DEG, c = cosf(a), s = sinf(a);
    WinL w;
    w.x = H.x + c * lx + s * lz; w.z = H.z - s * lx + c * lz; w.y = H.y + ly;
    w.ax = c * hw; w.az = -s * hw; w.hh = hh;
    w.nx = s * zs; w.nz = c * zs;
    w.seed = hash2((int)(w.x * 13.0f), (int)(w.y * 7.0f + w.z * 11.0f));
    winLights.push_back(w);
}

static void gableRoof(float y, float w, float d, float h, float ov,
                      float r, float g, float b, float wr, float wg, float wb) {
    float x0 = -w / 2 - ov, x1 = w / 2 + ov, z0 = -d / 2 - ov, z1 = d / 2 + ov, yt = y + h;
    float hx = w / 2, hz = d / 2;
    glColor3f(r, g, b);
    glBegin(GL_QUADS);
    quadV(x0, y, z1, x1, y, z1, x1, yt, 0, x0, yt, 0);
    quadV(x1, y, z0, x0, y, z0, x0, yt, 0, x1, yt, 0);
    glEnd();
    glColor3f(wr, wg, wb);
    glBegin(GL_TRIANGLES);
    normalOf(-hx, y, -hz, -hx, y, hz, -hx, yt, 0);
    glVertex3f(-hx, y, -hz); glVertex3f(-hx, y, hz); glVertex3f(-hx, yt, 0);
    normalOf(hx, y, hz, hx, y, -hz, hx, yt, 0);
    glVertex3f(hx, y, hz); glVertex3f(hx, y, -hz); glVertex3f(hx, yt, 0);
    glEnd();
}
static void shedRoof(float y, float w, float d, float h, float ov,
                     float r, float g, float b, float wr, float wg, float wb) {
    float x0 = -w / 2 - ov, x1 = w / 2 + ov, z0 = -d / 2 - ov, z1 = d / 2 + ov;
    float hx = w / 2, hz = d / 2;
    float tb = (-hz - z0) / (z1 - z0), tf = (hz - z0) / (z1 - z0);
    float hb = h * (1 - tb), hf = h * (1 - tf);
    glColor3f(r, g, b);
    glBegin(GL_QUADS);
    quadV(x0, y + h, z0, x1, y + h, z0, x1, y, z1, x0, y, z1);
    glEnd();
    glColor3f(r * 0.8f, g * 0.8f, b * 0.8f);
    glBegin(GL_QUADS);
    for (float rx = x0 + 0.6f; rx < x1 - 0.3f; rx += 1.2f) {
        float yy0 = y + h + 0.04f, yy1 = y + 0.04f;
        quadV(rx, yy0, z0, rx + 0.12f, yy0, z0, rx + 0.12f, yy1, z1, rx, yy1, z1);
    }
    glEnd();
    glColor3f(wr, wg, wb);
    glBegin(GL_QUADS);
    quadV(-hx, y, -hz, -hx, y, hz, -hx, y + hf, hz, -hx, y + hb, -hz);
    quadV(hx, y, hz, hx, y, -hz, hx, y + hb, -hz, hx, y + hf, hz);
    glEnd();
}
static void windowsFront(float w, float d, float fh, int floors, int cols, float zsign, bool skipDoor) {
    for (int f = 0; f < floors; f++)
        for (int c = 0; c < cols; c++) {
            float x = -w / 2 + (c + 0.5f) * w / cols;
            if (skipDoor && f == 0 && fabsf(x) < 1.3f) continue;
            float gw = w / cols * 0.42f, gh = fh * 0.36f, gy = f * fh + fh * 0.38f;
            boxB(x, gy, zsign * (d / 2 + 0.03f), gw, gh, 0.1f, 0.42f, 0.58f, 0.70f);
            boxB(x, f * fh + fh * 0.33f, zsign * (d / 2 + 0.06f), w / cols * 0.5f, 0.12f, 0.12f, 0.95f, 0.95f, 0.95f);
            recordWin(x, gy + gh * 0.5f, zsign * (d / 2 + 0.13f), gw * 0.5f, gh * 0.5f, zsign);
        }
}
static void drawHouse(const House& H) {
    g_curH = &H;
    glPushMatrix();
    glTranslatef(H.x, H.y, H.z);
    glRotatef(H.ang, 0, 1, 0);
    float w = H.w, d = H.d;
    boxB(0, -2.5f, 0, w + 0.5f, 2.5f, d + 0.5f, 0.55f, 0.55f, 0.52f);          // foundation
    if (H.type == 0) {                                                          // small cottage
        float wh = 3.2f;
        boxB(0, 0, 0, w, wh, d, H.wr, H.wg, H.wb);
        gableRoof(wh, w, d, 2.3f, 0.5f, H.pr, H.pg, H.pb, H.wr, H.wg, H.wb);
        boxB(0, 0, d / 2 + 0.04f, 1.2f, 2.2f, 0.12f, 0.45f, 0.28f, 0.15f);
        boxB(0, 0, d / 2 + 0.6f, 2.2f, 0.25f, 1.2f, 0.7f, 0.7f, 0.68f);
        windowsFront(w, d, wh, 1, 3, 1, true);
        windowsFront(w, d, wh, 1, 3, -1, false);
    } else if (H.type == 1) {                                                   // two-storey house
        float wh = 6.2f;
        boxB(0, 0, 0, w, wh, d, H.wr, H.wg, H.wb);
        boxB(0, 3.0f, 0, w + 0.2f, 0.25f, d + 0.2f, 0.85f, 0.85f, 0.82f);
        gableRoof(wh, w, d, 2.6f, 0.6f, H.pr, H.pg, H.pb, H.wr, H.wg, H.wb);
        boxB(w * 0.25f, wh + 1.0f, 0, 0.9f, 2.5f, 0.9f, 0.6f, 0.35f, 0.3f);
        boxB(0, 0, d / 2 + 0.04f, 1.3f, 2.3f, 0.12f, 0.40f, 0.25f, 0.15f);
        boxB(0, 3.05f, d / 2 + 0.7f, w * 0.55f, 0.2f, 1.4f, 0.75f, 0.75f, 0.72f);
        boxB(0, 3.25f, d / 2 + 1.35f, w * 0.55f, 0.8f, 0.1f, 0.6f, 0.35f, 0.25f);
        windowsFront(w, d, 3.1f, 2, 3, 1, true);
        windowsFront(w, d, 3.1f, 2, 3, -1, false);
    } else if (H.type == 2) {                                                   // multi-storey apartment
        float fh = 3.0f, wh = fh * H.floors;
        boxB(0, 0, 0, w, wh, d, H.wr * 0.9f, H.wg * 0.9f, H.wb * 0.9f);
        for (int f = 1; f <= H.floors; f++)
            boxB(0, f * fh - 0.15f, 0, w + 0.3f, 0.3f, d + 0.3f, 0.82f, 0.82f, 0.80f);
        boxB(0, wh, 0, w + 0.4f, 0.5f, d + 0.4f, H.pr, H.pg, H.pb);
        boxB(0, 0, d / 2 + 0.04f, 1.8f, 2.4f, 0.12f, 0.30f, 0.30f, 0.35f);
        cylB(w * 0.25f, wh + 0.5f, -d * 0.2f, 0.9f, 1.4f, 0.4f, 0.55f, 0.7f);
        boxB(-w * 0.3f, wh + 0.5f, d * 0.2f, 1.6f, 1.2f, 1.6f, 0.7f, 0.7f, 0.7f);
        windowsFront(w, d, fh, H.floors, 4, 1, true);
        windowsFront(w, d, fh, H.floors, 4, -1, false);
        for (int f = 1; f < H.floors; f++)
            boxB(0, f * fh, d / 2 + 0.55f, w * 0.85f, 0.15f, 1.1f, 0.65f, 0.65f, 0.65f);
    } else {                                                                    // tin-roof long house
        float wh = 2.7f;
        boxB(0, 0, 0, w, wh, d, H.wr, H.wg, H.wb);
        shedRoof(wh, w, d, 1.2f, 0.6f, H.pr, H.pg, H.pb, H.wr, H.wg, H.wb);
        boxB(-w * 0.25f, 0, d / 2 + 0.04f, 1.1f, 2.0f, 0.12f, 0.42f, 0.27f, 0.15f);
        boxB(0, 0, d / 2 + 0.8f, w, 0.2f, 1.6f, 0.72f, 0.68f, 0.6f);
        for (int k = 0; k < 3; k++)
            boxB(-w / 2 + 0.3f + k * (w - 0.6f) / 2, 0, d / 2 + 1.5f, 0.15f, 2.4f, 0.15f, 0.45f, 0.3f, 0.2f);
        windowsFront(w, d, wh, 1, 4, 1, true);
        windowsFront(w, d, wh, 1, 4, -1, false);
    }
    glPopMatrix();
    g_curH = 0;
}

// ----------------------------------------------------------------------------
//  Trees & rocks
// ----------------------------------------------------------------------------
struct Tree { float x, y, z, s; int kind; float r, g, b, ph; };
struct Rock { float x, z, s, rot; };
static std::vector<Tree> trees, outerTrees;
static std::vector<Rock> rocks;

static bool spotFree(float x, float z, float margin) {
    for (size_t i = 0; i < roads.size(); i++)
        if (distToSeg(x, z, roads[i].x1, roads[i].z1, roads[i].x2, roads[i].z2) < roads[i].w / 2 + 1.0f + margin) return false;
    for (size_t i = 0; i < houses.size(); i++)
        if (len2(x - houses[i].x, z - houses[i].z) < len2(houses[i].w, houses[i].d) / 2 + margin) return false;
    if (len2(x - SHX, z - SHZ) < 18.0f) return false;
    return true;
}
static Tree makeTree(float x, float z, float s, int kind) {
    Tree t; t.x = x; t.z = z; t.s = s; t.kind = kind; t.y = terrainH(x, z); t.ph = rr(0, 6.28f);
    if (kind == 1)         { t.r = rr(0.12f, 0.2f);  t.g = rr(0.36f, 0.46f); t.b = rr(0.22f, 0.30f); }
    else if (kind == 3)    { t.r = rr(0.25f, 0.35f); t.g = rr(0.55f, 0.65f); t.b = rr(0.18f, 0.25f); }   // palm / banana
    else if (rnd() < 0.08f){ t.r = rr(0.80f, 0.90f); t.g = rr(0.55f, 0.68f); t.b = rr(0.15f, 0.25f); }
    else                   { t.r = rr(0.22f, 0.38f); t.g = rr(0.50f, 0.66f); t.b = rr(0.18f, 0.28f); }
    return t;
}
static void addTree(float x, float z, float s, int kind) { trees.push_back(makeTree(x, z, s, kind)); }

static void makeTrees() {
    for (int c = 0; c < 28; c++) {
        float cx, cz; int zone = c % 4;
        if (zone == 0)      { cx = rr(-95, 95);  cz = rr(-95, -50); }
        else if (zone == 1) { cx = rr(-95, 95);  cz = rr(62, 95); }
        else if (zone == 2) { cx = rr(-95, -82); cz = rr(-50, 62); }
        else                { cx = rr(82, 95);   cz = rr(-50, 62); }
        int n = (int)rr(14, 26);
        for (int i = 0; i < n; i++) {
            float x = cx + rr(-11, 11), z = cz + rr(-11, 11);
            if (fabsf(x) > 96 || fabsf(z) > 96) continue;
            if (!spotFree(x, z, 2.5f) || terrainH(x, z) < 0.5f) continue;
            addTree(x, z, rr(1.0f, 1.9f), rnd() < 0.45f ? 1 : (rnd() < 0.6f ? 0 : 2));
        }
    }
    for (size_t i = 0; i < roads.size(); i++)
        for (float t = 4; t < roads[i].len; t += rr(7, 11)) {
            float x, z; roadPoint(roads[i], t, x, z);
            float dx = (roads[i].x2 - roads[i].x1) / roads[i].len, dz = (roads[i].z2 - roads[i].z1) / roads[i].len;
            float side = rnd() < 0.5f ? -1.0f : 1.0f, off = roads[i].w / 2 + rr(4.5f, 8.0f);
            x += -dz * side * off; z += dx * side * off;
            if (spotFree(x, z, 1.5f) && terrainH(x, z) > 0.45f) addTree(x, z, rr(0.8f, 1.3f), (int)(rnd() * 3.99f));
        }
    for (int i = 0; i < 260; i++) {
        float x = rr(-92, 92), z = rr(-14, 66);
        if (spotFree(x, z, 2.2f) && terrainH(x, z) > 0.5f) addTree(x, z, rr(0.8f, 1.5f), (int)(rnd() * 3.99f));
    }
    for (int i = 0; i < 70; i++) {
        float x = rr(-95, 95), z = rr(-95, 95);
        if (spotFree(x, z, 1.5f) && terrainH(x, z) > -0.1f) {
            Rock r; r.x = x; r.z = z; r.s = rr(0.8f, 2.2f); r.rot = rr(0, 360); rocks.push_back(r);
        }
    }
}

static void drawTree(const Tree& T, float sway) {
    float s = T.s;
    glPushMatrix();
    glTranslatef(T.x, T.y, T.z);
    if (sway != 0.0f) glRotatef(sway, windZ, 0, -windX);         // lean with the wind
    if (T.kind == 3) {                                            // palm / coconut tree
        cylB(0, 0, 0, 0.2f * s, 5.2f * s, 0.50f, 0.38f, 0.25f);
        glColor3f(T.r, T.g, T.b);
        for (int k = 0; k < 7; k++) {
            glPushMatrix(); glTranslatef(0, 5.2f * s, 0); glRotatef(k * 51.0f, 0, 1, 0); glRotatef(-62 - sway * 2.0f, 1, 0, 0);
            glScalef(0.45f, 0.12f, 1.0f); glutSolidSphere(1.8f * s, 6, 4); glPopMatrix();
        }
        glPopMatrix();
        return;
    }
    cylB(0, 0, 0, 0.25f * s, 1.8f * s, 0.42f, 0.29f, 0.17f);
    glColor3f(T.r, T.g, T.b);
    if (T.kind == 0) {
        glPushMatrix(); glTranslatef(0, 2.9f * s, 0); glScalef(1, 1.15f, 1); glutSolidSphere(1.5f * s, 8, 6); glPopMatrix();
    } else if (T.kind == 1) {
        for (int i = 0; i < 3; i++) {
            glPushMatrix(); glTranslatef(0, (1.2f + i * 1.3f) * s, 0); glRotatef(-90, 1, 0, 0);
            glutSolidCone((2.0f - i * 0.55f) * s, 2.3f * s, 8, 1); glPopMatrix();
        }
    } else {
        glPushMatrix(); glTranslatef(0, 2.6f * s, 0); glutSolidSphere(1.7f * s, 8, 6); glPopMatrix();
        glPushMatrix(); glTranslatef(0.9f * s, 3.5f * s, 0.3f * s); glutSolidSphere(1.2f * s, 7, 5); glPopMatrix();
    }
    glPopMatrix();
}
static void drawRock(const Rock& R) {
    glPushMatrix();
    glTranslatef(R.x, terrainH(R.x, R.z) + R.s * 0.3f, R.z);
    glRotatef(R.rot, 0, 1, 0);
    glScalef(R.s * 0.8f, R.s * 0.5f, R.s * 0.65f);
    glColor3f(0.60f, 0.60f, 0.57f);
    glutSolidDodecahedron();
    glPopMatrix();
}

// ----------------------------------------------------------------------------
//  Terrain mesh (smooth shaded), surrounding landscape, roads, lamps
// ----------------------------------------------------------------------------
static void terrainColorAt(float x, float z, float h, float slope, float& r, float& g, float& b) {
    float d = fabsf(z - riverZ(x));
    if (h < -0.25f) { r = 0.40f; g = 0.36f; b = 0.27f; }
    else if (d < 11.0f && h < 0.9f) { float t = clamp01((h + 0.25f) / 1.1f); r = mixf(0.52f, 0.40f, t); g = mixf(0.47f, 0.55f, t); b = mixf(0.33f, 0.25f, t); }
    else { float t = clamp01((h - 0.5f) / 16.0f); r = 0.33f - 0.12f * t; g = 0.55f - 0.17f * t; b = 0.21f - 0.05f * t; }
    if (h > 18.0f) { float u = clamp01((h - 18.0f) / 30.0f); r = mixf(r, 0.45f, u); g = mixf(g, 0.46f, u); b = mixf(b, 0.44f, u); }
    if (slope > 0.6f) { float u = clamp01((slope - 0.6f) * 1.5f); r = mixf(r, 0.42f, u); g = mixf(g, 0.40f, u); b = mixf(b, 0.36f, u); }
    float j = (hash2((int)floorf(x * 0.7f), (int)floorf(z * 0.7f)) - 0.5f) * 0.05f;
    r += j; g += j * 1.3f; b += j * 0.8f;
}
static void terrVert(float x, float z, float e, bool colourIt) {
    float h = terrainH(x, z);
    float hx = terrainH(x + e, z) - terrainH(x - e, z), hz = terrainH(x, z + e) - terrainH(x, z - e);
    if (colourIt) {
        float r, g, b; terrainColorAt(x, z, h, sqrtf(hx * hx + hz * hz) / (2 * e), r, g, b);
        glColor3f(r, g, b);
    }
    glNormal3f(-hx, 2 * e, -hz);
    glVertex3f(x, h, z);
}
static void drawTerrainMesh() {
    for (int i = 0; i < GN; i++) {
        float x0 = -WORLD + i * CELL, x1 = x0 + CELL;
        glBegin(GL_TRIANGLE_STRIP);
        for (int j = 0; j <= GN; j++) { float z = -WORLD + j * CELL; terrVert(x1, z, 1.0f, true); terrVert(x0, z, 1.0f, true); }
        glEnd();
    }
    // skirt hides tiny cracks where the detailed town meets the coarse landscape
    glColor3f(0.33f, 0.40f, 0.22f);
    glBegin(GL_QUADS);
    for (int k = 0; k < GN; k++) {
        float a = -WORLD + k * CELL, b = a + CELL;
        float E[4][4] = { {a, -WORLD, b, -WORLD}, {a, WORLD, b, WORLD}, {-WORLD, a, -WORLD, b}, {WORLD, a, WORLD, b} };
        for (int e = 0; e < 4; e++) {
            float h1 = terrainH(E[e][0], E[e][1]), h2 = terrainH(E[e][2], E[e][3]);
            glNormal3f(0, 1, 0);
            glVertex3f(E[e][0], h1, E[e][1]); glVertex3f(E[e][2], h2, E[e][3]);
            glVertex3f(E[e][2], h2 - 5, E[e][3]); glVertex3f(E[e][0], h1 - 5, E[e][1]);
        }
    }
    glEnd();
}
static void drawOuterTerrain() {
    int n = (int)(2 * OUTER / OCELL);
    glBegin(GL_QUADS);
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++) {
            float x0 = -OUTER + i * OCELL, x1 = x0 + OCELL, z0 = -OUTER + j * OCELL, z1 = z0 + OCELL;
            if (x0 >= -WORLD && x1 <= WORLD && z0 >= -WORLD && z1 <= WORLD) continue;
            float cx = (x0 + x1) * 0.5f, cz = (z0 + z1) * 0.5f, hc = terrainH(cx, cz);
            float sl = fabsf(terrainH(x1, cz) - terrainH(x0, cz)) / OCELL + fabsf(terrainH(cx, z1) - terrainH(cx, z0)) / OCELL;
            float r, g, b; terrainColorAt(cx, cz, hc, sl, r, g, b);
            float d = fabsf(cz - riverZ(cx));
            if (hc > 0.6f && hc < 8.0f && d > 14.0f) {                 // paddy fields, mustard, ploughed land
                float f = hash2(i, j), v = (hash2(j, i) - 0.5f) * 0.06f;
                if (f < 0.42f)      { r = 0.34f + v; g = 0.60f + v; b = 0.20f; }
                else if (f < 0.56f) { r = 0.64f + v; g = 0.62f + v; b = 0.24f; }
                else if (f < 0.66f) { r = 0.47f + v; g = 0.38f + v; b = 0.25f; }
                else if (f < 0.74f) { r = 0.42f + v; g = 0.66f + v; b = 0.30f; }
            }
            glColor3f(r, g, b);
            terrVert(x0, z0, 6.0f, false); terrVert(x0, z1, 6.0f, false);
            terrVert(x1, z1, 6.0f, false); terrVert(x1, z0, 6.0f, false);
        }
    glEnd();
}
static void drawRoadStrip(const Road& R, float lift) {
    float dx = (R.x2 - R.x1) / R.len, dz = (R.z2 - R.z1) / R.len, px = -dz, pz = dx;
    float hw = R.w / 2;
    int n = (int)(R.len / 2.0f);
    for (int i = 0; i < n; i++) {
        float t0 = i * 2.0f, t1 = (i == n - 1) ? R.len : (i + 1) * 2.0f;
        float ax = R.x1 + dx * t0, az = R.z1 + dz * t0, bx = R.x1 + dx * t1, bz = R.z1 + dz * t1;
        float ha = terrainH(ax, az) + lift, hb = terrainH(bx, bz) + lift;
        float sw = hw + 0.8f;
        glColor3f(0.70f, 0.69f, 0.64f);
        glBegin(GL_QUADS);
        quadV(ax + px * sw, ha - 0.04f, az + pz * sw, bx + px * sw, hb - 0.04f, bz + pz * sw,
              bx - px * sw, hb - 0.04f, bz - pz * sw, ax - px * sw, ha - 0.04f, az - pz * sw);
        glEnd();
        glColor3f(0.27f, 0.28f, 0.30f);
        glBegin(GL_QUADS);
        quadV(ax + px * hw, ha, az + pz * hw, bx + px * hw, hb, bz + pz * hw,
              bx - px * hw, hb, bz - pz * hw, ax - px * hw, ha, az - pz * hw);
        glEnd();
        if (i % 2 == 0) {
            float c = 0.12f;
            glColor3f(0.92f, 0.92f, 0.86f);
            glBegin(GL_QUADS);
            quadV(ax + px * c, ha + 0.02f, az + pz * c, bx + px * c, hb + 0.02f, bz + pz * c,
                  bx - px * c, hb + 0.02f, bz - pz * c, ax - px * c, ha + 0.02f, az - pz * c);
            glEnd();
        }
    }
}

struct Lamp { float x, y, z; };
static std::vector<Lamp> lamps;
static void drawLampPosts() {
    lamps.clear();
    for (int idx = 0; idx < 2; idx++) {
        const Road& R = roads[idx];
        float dx = (R.x2 - R.x1) / R.len, dz = (R.z2 - R.z1) / R.len, px = -dz, pz = dx;
        int k = 0;
        for (float t = 6; t < R.len; t += 14, k++) {
            float x, z; roadPoint(R, t, x, z);
            float side = (k % 2) ? 1.0f : -1.0f, off = R.w / 2 + 1.0f;
            float lx = x + px * side * off, lz = z + pz * side * off, y = terrainH(lx, lz);
            boxB(lx, y, lz, 0.18f, 4.2f, 0.18f, 0.25f, 0.25f, 0.28f);
            boxB(lx, y + 4.2f, lz, 0.8f, 0.25f, 0.8f, 0.55f, 0.55f, 0.5f);
            Lamp L; L.x = lx; L.y = y + 4.15f; L.z = lz; lamps.push_back(L);
        }
    }
}

// ----------------------------------------------------------------------------
//  Cyclone shelter (raised, multi-storey building with open ground floor)
// ----------------------------------------------------------------------------
static const float SH_W = 26.0f, SH_D = 12.0f, SH_FH = 3.4f;
static float shelterFloorY(int f) { return PAD + 0.4f + f * SH_FH; }

static void drawShelterStatic() {
    glPushMatrix();
    glTranslatef(SHX, 0, SHZ);
    float W = SH_W, D = SH_D, FH = SH_FH;
    boxB(0, PAD - 0.8f, 0, W + 4, 0.8f, D + 4, 0.62f, 0.62f, 0.6f);
    boxB(0, PAD, 0, W + 2, 0.4f, D + 2, 0.78f, 0.78f, 0.75f);
    for (int f = 1; f <= 4; f++) {
        float y = shelterFloorY(f);
        boxB(0, y - 0.4f, 0, W, 0.4f, D, 0.86f, 0.86f, 0.82f);
        boxB(0, y, D / 2 - 0.1f, W, 0.9f, 0.15f, 0.96f, 0.62f, 0.2f);
        boxB(0, y, -D / 2 + 0.1f, W, 0.9f, 0.15f, 0.96f, 0.62f, 0.2f);
        boxB(-W / 2 + 0.1f, y, 0, 0.15f, 0.9f, D, 0.96f, 0.62f, 0.2f);
        boxB(W / 2 - 0.1f, y, 0, 0.15f, 0.9f, D, 0.96f, 0.62f, 0.2f);
    }
    for (int k = 0; k <= 5; k++)
        for (int s = -1; s <= 1; s += 2)
            boxB(-W / 2 + 1.0f + k * (W - 2.0f) / 5.0f, PAD + 0.4f, s * (D / 2 - 0.9f), 0.8f, 4 * FH, 0.8f, 0.92f, 0.92f, 0.9f);
    boxB(0, PAD + 0.4f, 0, W - 2, 4 * FH - 0.4f, 0.4f, 0.88f, 0.86f, 0.8f);
    boxB(W / 2 + 2.5f, PAD + 0.4f, 0, 4.5f, 4 * FH + 1.5f, D * 0.65f, 0.9f, 0.55f, 0.2f);
    boxB(W / 2 + 2.5f, PAD + 0.4f + 4 * FH + 1.5f, 0, 5.0f, 0.4f, D * 0.65f + 0.6f, 0.3f, 0.45f, 0.65f);
    float roofY = shelterFloorY(4);
    boxB(0, roofY, 0, 13, 2.4f, 0.4f, 0.12f, 0.55f, 0.30f);                         // green sign board
    cylB(7, roofY, -3, 1.6f, 2.2f, 0.4f, 0.55f, 0.75f);
    cylB(10, roofY, -2, 1.2f, 1.8f, 0.4f, 0.55f, 0.75f);
    for (int i = 0; i < 5; i++)
        boxB(0, PAD + 0.4f - i * 0.15f, D / 2 + 1.2f + i * 0.5f, 8.0f, 0.15f, 0.5f, 0.75f, 0.75f, 0.72f);
    // signal flag mast
    boxB(-W / 2 - 3.0f, PAD, D / 2 + 2.0f, 0.18f, 13.0f, 0.18f, 0.75f, 0.75f, 0.78f);
    glPopMatrix();
}

// ----------------------------------------------------------------------------
//  Outer villages & groves (static decoration of the wider landscape)
// ----------------------------------------------------------------------------
static bool onExtRoad(float x, float z, float m) {
    if (fabsf(x) < 90) return false;
    return fabsf(z) < 6 + m || fabsf(z - 25) < 6 + m;
}
static void makeOuterWorld() {
    for (int v = 0; v < 60; v++) {                       // villages along the river valley
        float cx = rr(-470, 470), cz = rr(-85, 105);
        if (fabsf(cx) < 125 && fabsf(cz) < 125) continue;
        float h = terrainH(cx, cz);
        if (h < 0.7f || h > 14.0f || fabsf(cz - riverZ(cx)) < 18) continue;
        int n = (int)rr(4, 10);
        for (int k = 0; k < n; k++) {
            float x = cx + rr(-24, 24), z = cz + rr(-24, 24);
            if (fabsf(x) < 112 && fabsf(z) < 112) continue;
            float hh = terrainH(x, z);
            if (hh < 0.7f || hh > 14.0f || fabsf(z - riverZ(x)) < 14 || onExtRoad(x, z, 6)) continue;
            bool clash = false;
            for (size_t q = 0; q < outerHouses.size(); q++) if (len2(outerHouses[q].x - x, outerHouses[q].z - z) < 11) { clash = true; break; }
            if (clash) continue;
            float rp = rnd(); int type = rp < 0.45f ? 0 : (rp < 0.7f ? 3 : 1);
            House H = newHouse(type, 90.0f * (int)(rnd() * 3.99f)); H.x = x; H.z = z; setHouseY(H);
            outerHouses.push_back(H);
        }
        for (int k = 0; k < 14; k++) {
            float x = cx + rr(-34, 34), z = cz + rr(-34, 34);
            if ((fabsf(x) < 112 && fabsf(z) < 112) || onExtRoad(x, z, 2)) continue;
            bool clash = false;
            for (size_t q = 0; q < outerHouses.size(); q++) if (len2(outerHouses[q].x - x, outerHouses[q].z - z) < 7) { clash = true; break; }
            if (clash || terrainH(x, z) < 0.6f) continue;
            Tree t = makeTree(x, z, rr(1.0f, 1.7f), rnd() < 0.35f ? 3 : (int)(rnd() * 2.99f)); t.y -= 0.4f; outerTrees.push_back(t);
        }
    }
    for (int c = 0; c < 70; c++) {                       // groves / forest patches on hills
        float cx = rr(-480, 480), cz = rr(-420, 420);
        if (fabsf(cx) < 120 && fabsf(cz) < 120) continue;
        int n = (int)rr(6, 16);
        for (int k = 0; k < n; k++) {
            float x = cx + rr(-16, 16), z = cz + rr(-16, 16);
            if ((fabsf(x) < 108 && fabsf(z) < 108) || onExtRoad(x, z, 2)) continue;
            float h = terrainH(x, z);
            if (h < 0.6f || h > 55.0f || fabsf(z - riverZ(x)) < 10) continue;
            Tree t = makeTree(x, z, rr(1.2f, 2.2f), h > 12 ? 1 : (int)(rnd() * 2.99f)); t.y -= 0.4f; outerTrees.push_back(t);
        }
    }
}

// ----------------------------------------------------------------------------
//  People
// ----------------------------------------------------------------------------
enum { P_HOME = 0, P_WALK, P_SAFE, P_STRANDED, P_TO_BOAT, P_IN_BOAT };
struct Person {
    float x, z, y, sx, sz;
    float px[6], pz[6], rx[4], rz[4]; int np, seg;
    float trig, speed, ph, yaw, anim;
    int state, house, boat, seat;
    bool onRoof, rescued, child;
    float roofX, roofZ, roofY;
    float sh[3], pa[3], ha[3], sk[3];
};
static std::vector<Person> people;

static const float SHIRTS[8][3] = { {0.85f, 0.22f, 0.20f}, {0.20f, 0.42f, 0.82f}, {0.95f, 0.78f, 0.20f}, {0.22f, 0.62f, 0.38f},
                                    {0.60f, 0.30f, 0.70f}, {0.95f, 0.55f, 0.70f}, {0.90f, 0.90f, 0.88f}, {0.30f, 0.70f, 0.80f} };
static const float SKIN[4][3] = { {0.92f, 0.76f, 0.62f}, {0.80f, 0.60f, 0.45f}, {0.66f, 0.47f, 0.33f}, {0.50f, 0.34f, 0.23f} };

static void randomLook(float* sh, float* pa, float* ha, float* sk) {
    int c = (int)(rnd() * 7.99f), d = (int)(rnd() * 7.99f), k = 1 + (int)(rnd() * 2.99f);
    for (int q = 0; q < 3; q++) { sh[q] = SHIRTS[c][q]; pa[q] = SHIRTS[d][q] * 0.35f + 0.08f; sk[q] = SKIN[k][q]; }
    float h = rr(0.04f, 0.18f); ha[0] = h; ha[1] = h * 0.8f; ha[2] = h * 0.7f;
}

static void makePeopleFor(int hi, float roadZ, int side) {
    const House& H = houses[hi];
    int n;
    switch (H.type) { case 0: n = 2 + (int)(rnd() * 1.99f); break; case 1: n = 3 + (int)(rnd() * 1.99f); break;
                      case 2: n = 5 + (int)(rnd() * 3.99f); break; default: n = 3 + (int)(rnd() * 2.99f); break; }
    float homeH = terrainH(H.x, roadZ + side * 3.5f);
    float a = H.ang * DEG;
    for (int i = 0; i < n; i++) {
        Person p;
        p.sx = H.x + rr(-H.w / 2 + 0.8f, H.w / 2 - 0.8f);
        p.sz = roadZ + side * rr(3.2f, 3.8f);
        p.x = p.sx; p.z = p.sz; p.y = 0;
        float oz = rr(-1.5f, 1.5f), ox = rr(-1.5f, 1.5f);
        p.rx[0] = p.sx;            p.rz[0] = roadZ + oz;
        p.rx[1] = SHX + ox;        p.rz[1] = roadZ + oz;
        p.rx[2] = SHX + ox;        p.rz[2] = 40.0f;
        p.rx[3] = SHX + rr(-9, 9); p.rz[3] = 43.5f;
        float r = rnd();                                 // not everybody leaves in time
        if (r < 0.50f)      p.trig = homeH - rr(0.5f, 1.4f);   // early evacuees
        else if (r < 0.85f) p.trig = homeH + rr(-0.2f, 0.5f);  // late - will be caught by the water
        else                p.trig = 99.0f;                    // refuse to leave -> end up on the roof
        p.child = rnd() < 0.25f;
        p.speed = rr(1.3f, 1.9f) * (p.child ? 0.85f : 1.0f);
        p.ph = rr(0, 6.28f); p.yaw = (side < 0 ? 0.0f : 180.0f); p.anim = 0;
        p.house = hi; p.boat = -1; p.seat = -1;
        float lx = rr(-H.w / 2 + 1.0f, H.w / 2 - 1.0f);
        p.roofX = H.x + cosf(a) * lx; p.roofZ = H.z - sinf(a) * lx; p.roofY = houseRoofStand(H);
        randomLook(p.sh, p.pa, p.ha, p.sk);
        p.np = 4; p.seg = 0; p.state = P_HOME; p.onRoof = false; p.rescued = false;
        for (int k = 0; k < 4; k++) { p.px[k] = p.rx[k]; p.pz[k] = p.rz[k]; }
        people.push_back(p);
    }
}

struct Spot { float x, y, z, yaw, ph; float sh[3], pa[3], ha[3], sk[3]; bool child; };
static std::vector<Spot> spots;
static void makeSpots() {
    for (int i = 0; i < 700; i++) {
        Spot s; int f = i % 4;
        s.x = SHX + rr(-11.6f, 11.6f); s.z = SHZ + (rnd() < 0.5f ? rr(-4.6f, -0.6f) : rr(0.6f, 4.6f));
        s.y = shelterFloorY(f); s.ph = rr(0, 6.28f); s.yaw = rr(0, 360); s.child = rnd() < 0.25f;
        randomLook(s.sh, s.pa, s.ha, s.sk);
        spots.push_back(s);
    }
}

// articulated person (origin at the feet, facing +z)
// arms: 0 walk swing, 1 both arms waving (help!), 2 megaphone, 3 balancing in water
static void drawHuman(float x, float y, float z, float yawDeg, float swing, int arms, float armT,
                      const float* sh, const float* pa, const float* ha, const float* sk, float sc, bool gear) {
    glPushMatrix();
    glTranslatef(x, y, z); glRotatef(yawDeg, 0, 1, 0); glScalef(sc, sc, sc);
    for (int s = -1; s <= 1; s += 2) {
        glPushMatrix(); glTranslatef(s * 0.12f, 0.85f, 0); glRotatef(s * swing * 32.0f, 1, 0, 0);
        glColor3fv(pa); boxC(0, -0.42f, 0, 0.17f, 0.85f, 0.2f);
        glColor3f(0.1f, 0.1f, 0.1f); boxC(0, -0.85f, 0.05f, 0.18f, 0.1f, 0.3f);
        glPopMatrix();
    }
    glColor3fv(sh); boxC(0, 1.15f, 0, 0.46f, 0.6f, 0.26f);
    if (gear) {                                                            // life jacket
        glColor3f(1.0f, 0.45f, 0.05f); boxC(0, 1.18f, 0, 0.52f, 0.5f, 0.32f);
        glColor3f(0.92f, 0.92f, 0.85f); boxC(0, 1.06f, 0, 0.53f, 0.06f, 0.33f);
    }
    for (int s = -1; s <= 1; s += 2) {
        glPushMatrix(); glTranslatef(s * 0.3f, 1.4f, 0);
        if (arms == 1)               glRotatef(s * (148.0f + 24.0f * sinf(armT * 7.0f + s)), 0, 0, 1);
        else if (arms == 2 && s > 0) glRotatef(-80, 1, 0, 0);
        else if (arms == 3)          glRotatef(s * (38.0f + 8.0f * sinf(armT * 3.0f + s)), 0, 0, 1);
        else                         glRotatef(-s * swing * 30.0f, 1, 0, 0);
        glColor3fv(sh); boxC(0, -0.25f, 0, 0.12f, 0.5f, 0.14f);
        glColor3fv(sk); boxC(0, -0.55f, 0, 0.1f, 0.12f, 0.12f);
        if (arms == 2 && s > 0) {                                        // megaphone
            glColor3f(0.95f, 0.95f, 0.9f);
            glPushMatrix(); glTranslatef(0, -0.62f, 0); glRotatef(90, 1, 0, 0); glutSolidCone(0.13, 0.38, 8, 1); glPopMatrix();
        }
        glPopMatrix();
    }
    glColor3fv(sk); glPushMatrix(); glTranslatef(0, 1.62f, 0); glutSolidSphere(0.15, 10, 8); glPopMatrix();
    if (gear) glColor3f(0.95f, 0.85f, 0.15f); else glColor3fv(ha);          // helmet or hair
    glPushMatrix(); glTranslatef(0, 1.69f, -0.02f); glScalef(1, 0.65f, 1); glutSolidSphere(gear ? 0.18 : 0.16, 10, 8); glPopMatrix();
    glPopMatrix();
}
// a seated person (origin = seat level, facing +z)
static void drawSeated(const float* sh, const float* pa, const float* ha, const float* sk, float sc, float wave, bool vest) {
    glPushMatrix(); glScalef(sc, sc, sc);
    glColor3fv(sh); boxC(0, 0.32f, 0, 0.38f, 0.5f, 0.24f);
    if (vest) { glColor3f(1.0f, 0.45f, 0.05f); boxC(0, 0.36f, 0, 0.44f, 0.42f, 0.30f); }
    for (int s = -1; s <= 1; s += 2) {
        glColor3fv(pa); boxC(s * 0.1f, 0.03f, 0.24f, 0.14f, 0.14f, 0.5f); boxC(s * 0.1f, -0.22f, 0.46f, 0.12f, 0.45f, 0.12f);
        glColor3f(0.1f, 0.1f, 0.1f); boxC(s * 0.1f, -0.46f, 0.52f, 0.13f, 0.08f, 0.22f);
    }
    glColor3fv(sh); boxC(-0.24f, 0.42f, 0.2f, 0.1f, 0.1f, 0.42f);
    glPushMatrix(); glTranslatef(0.24f, 0.52f, 0); glRotatef(-35 + wave, 0, 0, 1); glColor3fv(sh); boxC(0, 0.25f, 0, 0.1f, 0.5f, 0.1f); glPopMatrix();
    glColor3fv(sk); glPushMatrix(); glTranslatef(0, 0.74f, 0); glutSolidSphere(0.15, 10, 8); glPopMatrix();
    glColor3fv(ha); glPushMatrix(); glTranslatef(0, 0.8f, -0.02f); glScalef(1, 0.65f, 1); glutSolidSphere(0.16, 10, 8); glPopMatrix();
    glPopMatrix();
}

// ----------------------------------------------------------------------------
//  Cars
// ----------------------------------------------------------------------------
struct Car { int road; float t, t0, speed; int lane; float r, g, b; bool stuck; };
static std::vector<Car> cars;
static void initCars() {
    cars.clear();
    int spec[6][2] = { {0, 6}, {1, 6}, {3, 3}, {4, 3}, {5, 3}, {6, 2} };
    for (int s = 0; s < 6; s++)
        for (int k = 0; k < spec[s][1]; k++) {
            Car c; c.road = spec[s][0];
            c.t0 = (k + rnd() * 0.6f) * roads[c.road].len / spec[s][1];
            c.t = c.t0;
            c.speed = rr(5, 8) * ((k % 2) ? 1.0f : -1.0f);
            c.lane = c.speed > 0 ? 1 : -1;
            float cr = rnd();
            if (cr < 0.2f) { c.r = 0.75f; c.g = 0.12f; c.b = 0.12f; }
            else if (cr < 0.4f) { c.r = 0.15f; c.g = 0.32f; c.b = 0.70f; }
            else if (cr < 0.6f) { c.r = 0.90f; c.g = 0.80f; c.b = 0.25f; }
            else if (cr < 0.8f) { c.r = 0.88f; c.g = 0.88f; c.b = 0.90f; }
            else { c.r = 0.18f; c.g = 0.50f; c.b = 0.35f; }
            c.stuck = false;
            cars.push_back(c);
        }
}
static void drawCar(const Car& c) {
    const Road& R = roads[c.road];
    float x, z; roadPoint(R, c.t, x, z);
    float dx = (R.x2 - R.x1) / R.len, dz = (R.z2 - R.z1) / R.len;
    float sgn = c.speed > 0 ? 1.0f : -1.0f;
    x += -dz * c.lane * R.w * 0.22f; z += dx * c.lane * R.w * 0.22f;
    float y = terrainH(x, z) + 0.2f;
    glPushMatrix();
    glTranslatef(x, y, z);
    glRotatef(atan2f(dx * sgn, dz * sgn) / DEG, 0, 1, 0);
    boxB(0, 0.35f, 0, 1.7f, 0.65f, 3.5f, c.r, c.g, c.b);
    boxB(0, 1.0f, -0.2f, 1.45f, 0.6f, 1.9f, 0.45f, 0.58f, 0.68f);
    for (int sx = -1; sx <= 1; sx += 2) for (int sz = -1; sz <= 1; sz += 2)
        boxB(sx * 0.85f, 0, sz * 1.1f, 0.28f, 0.7f, 0.7f, 0.08f, 0.08f, 0.08f);
    bool under = y + 0.8f < waterLevel;
    if (!under) {
        if (!c.stuck && night > 0.1f) {
            for (int s = -1; s <= 1; s += 2) {
                addGlow(s * 0.6f, 0.7f, 1.78f, 1.0f, 0.95f, 0.75f, 0.16f, night);
                addGlow(s * 0.6f, 0.7f, -1.78f, 1.0f, 0.1f, 0.08f, 0.10f, night);
            }
        } else if (c.stuck && fmodf(rt * 1.6f, 1.0f) < 0.5f) {            // hazard lights
            for (int s = -1; s <= 1; s += 2) for (int e = -1; e <= 1; e += 2)
                addGlow(s * 0.7f, 0.7f, e * 1.78f, 1.0f, 0.6f, 0.1f, 0.12f, 0.6f + 0.4f * night);
        }
    }
    glPopMatrix();
}

// ----------------------------------------------------------------------------
//  Rescue boats  +  navigation grid (boats only go where the water is deep)
// ----------------------------------------------------------------------------
enum { B_PATROL = 0, B_GO, B_WAIT, B_RETURN, B_UNLOAD };
struct P2 { float x, z; };
struct Boat {
    float x, z, head, spd, roll, pitch;
    float x0, z0, h0, tx, tz;
    int state, pi, load;
    std::vector<P2> path;
    float think, timer, wakeT;
    bool siren;
    int seatUsed[BOAT_CAP];
};
static Boat boats[NBOAT];

struct Wake { float x, z, vx, vz, age, s; };
static std::vector<Wake> wakes;

static float cellHmax[GN][GN];
static unsigned char cellBlock[GN][GN];
static int bfsD[GN][GN], bfsP[GN][GN];
static std::vector<int> bfsQ;

static void cellOf(float x, float z, int& i, int& j) {
    i = (int)floorf((x + WORLD) / CELL); j = (int)floorf((z + WORLD) / CELL);
    i = std::max(0, std::min(GN - 1, i)); j = std::max(0, std::min(GN - 1, j));
}
static void cellCenter(int i, int j, float& x, float& z) { x = -WORLD + (i + 0.5f) * CELL; z = -WORLD + (j + 0.5f) * CELL; }
static bool navCell(int i, int j) {
    if (i < 1 || j < 1 || i >= GN - 1 || j >= GN - 1) return false;
    return !cellBlock[i][j] && (waterLevel - cellHmax[i][j]) >= 0.55f;
}
static void initNav() {
    for (int i = 0; i < GN; i++)
        for (int j = 0; j < GN; j++) {
            float x0 = -WORLD + i * CELL, z0 = -WORLD + j * CELL;
            float m = terrainH(x0 + 1, z0 + 1);
            m = std::max(m, terrainH(x0, z0)); m = std::max(m, terrainH(x0 + 2, z0));
            m = std::max(m, terrainH(x0, z0 + 2)); m = std::max(m, terrainH(x0 + 2, z0 + 2));
            cellHmax[i][j] = m;
            cellBlock[i][j] = len2(x0 + 1 - SHX, z0 + 1 - SHZ) < 15.0f ? 1 : 0;
        }
    for (size_t h = 0; h < houses.size(); h++) {
        float hx, hz; houseHalf(houses[h], hx, hz);
        hx += 1.0f; hz += 1.0f;
        int i0, j0, i1, j1;
        cellOf(houses[h].x - hx, houses[h].z - hz, i0, j0); cellOf(houses[h].x + hx, houses[h].z + hz, i1, j1);
        for (int i = i0; i <= i1; i++) for (int j = j0; j <= j1; j++) cellBlock[i][j] = 1;
    }
}
static void runBFS(int si, int sj) {
    for (int i = 0; i < GN; i++) for (int j = 0; j < GN; j++) bfsD[i][j] = -1;
    bfsQ.clear();
    bfsD[si][sj] = 0; bfsP[si][sj] = -1; bfsQ.push_back(si * GN + sj);
    for (size_t q = 0; q < bfsQ.size(); q++) {
        int c = bfsQ[q], i = c / GN, j = c % GN;
        for (int di = -1; di <= 1; di++)
            for (int dj = -1; dj <= 1; dj++) {
                if (!di && !dj) continue;
                int ni = i + di, nj = j + dj;
                if (!navCell(ni, nj) || bfsD[ni][nj] >= 0) continue;
                if (di && dj && (!navCell(i + di, j) || !navCell(i, j + dj))) continue;
                bfsD[ni][nj] = bfsD[i][j] + 1; bfsP[ni][nj] = c; bfsQ.push_back(ni * GN + nj);
            }
    }
}
static void buildPath(Boat& b, int gi, int gj, float fx, float fz) {
    std::vector<int> cells;
    int c = gi * GN + gj;
    while (c >= 0) { cells.push_back(c); c = bfsP[c / GN][c % GN]; }
    b.path.clear();
    for (int k = (int)cells.size() - 2; k >= 0; k--) {
        P2 p; cellCenter(cells[k] / GN, cells[k] % GN, p.x, p.z); b.path.push_back(p);
    }
    P2 f; f.x = fx; f.z = fz;
    if (b.path.empty()) b.path.push_back(f); else b.path.back() = f;
    b.pi = 0; b.tx = fx; b.tz = fz;
}
static bool lineNav(float x0, float z0, float x1, float z1) {
    float L = len2(x1 - x0, z1 - z0); int n = (int)(L / 1.0f) + 1;
    for (int k = 1; k <= n; k++) {
        float t = k / (float)n; int i, j; cellOf(mixf(x0, x1, t), mixf(z0, z1, t), i, j);
        if (!navCell(i, j)) return false;
    }
    return true;
}
static void steerBoat(Boat& b, float dt, float dh, float vt) {
    if (dt <= 0) return;
    float turn = clampf(dh, -1.1f * dt, 1.1f * dt);
    b.head = wrapAng(b.head + turn);
    float acc = clampf(vt - b.spd, -3.5f * dt, 2.2f * dt);
    b.spd += acc;
    float rollT = -(turn / dt) * 9.0f * clamp01(b.spd / 7.0f);
    b.roll += (rollT - b.roll) * std::min(1.0f, dt * 3.0f);
    float pitchT = (acc / dt) * 1.2f + b.spd * 0.55f;
    b.pitch += (pitchT - b.pitch) * std::min(1.0f, dt * 2.0f);
    float nx = b.x + sinf(b.head) * b.spd * dt, nz = b.z + cosf(b.head) * b.spd * dt;
    if (waterLevel - terrainH(nx, nz) > 0.3f && fabsf(nx) < 97 && fabsf(nz) < 97) { b.x = nx; b.z = nz; }
    else b.spd *= 0.5f;
}
// returns true when the end of the path is reached
static bool followPath(Boat& b, float dt, float cruise, float arriveR) {
    if (b.path.empty()) { steerBoat(b, dt, 0, 0); return true; }
    while (b.pi + 1 < (int)b.path.size() && lineNav(b.x, b.z, b.path[b.pi + 1].x, b.path[b.pi + 1].z)) b.pi++;
    P2 t = b.path[b.pi];
    if (b.pi + 1 < (int)b.path.size() && len2(t.x - b.x, t.z - b.z) < 2.0f) { b.pi++; t = b.path[b.pi]; }
    const P2& f = b.path.back();
    float dF = len2(f.x - b.x, f.z - b.z);
    if (b.pi == (int)b.path.size() - 1 && dF < arriveR) { steerBoat(b, dt, 0, 0); return true; }
    float dh = wrapAng(atan2f(t.x - b.x, t.z - b.z) - b.head);
    float vt = std::min(cruise, 0.8f + dF * 0.45f) * (1.0f - std::min(fabsf(dh) / 1.6f, 0.75f));
    steerBoat(b, dt, dh, vt);
    return false;
}

// boat landing next to the shelter
static bool dockOK = false;
static float dockX = SHX, dockZ = 20, shoreX = SHX, shoreZ = 26;
static void computeDock() {
    dockOK = false;
    float z = SHZ - 12.0f;
    for (; z > -6.0f; z -= 0.5f) if (waterLevel - terrainH(SHX, z) >= 0.75f) break;
    if (z <= -6.0f) return;
    float s = z;
    while (s < SHZ && waterLevel - terrainH(SHX, s) > 0.02f) s += 0.5f;
    dockX = SHX; dockZ = z; shoreX = SHX; shoreZ = s + 1.0f; dockOK = true;
}

static float depthAt(float x, float z) { return waterLevel - terrainH(x, z); }
static bool isCandidate(const Person& p) {
    if (p.boat >= 0) return false;
    if (p.state == P_STRANDED) return true;
    if (p.state == P_WALK && !p.rescued) return depthAt(p.x, p.z) > 0.45f;
    return false;
}
static int pendingOf(int id) {
    int n = 0;
    for (size_t i = 0; i < people.size(); i++) {
        const Person& p = people[i];
        if (p.boat == id && (p.state == P_STRANDED || p.state == P_WALK || p.state == P_TO_BOAT)) n++;
    }
    return n;
}
static void sendPendingToBoat(int id) {
    for (size_t i = 0; i < people.size(); i++) {
        Person& p = people[i];
        if (p.boat == id && (p.state == P_STRANDED || p.state == P_WALK)) p.state = P_TO_BOAT;
    }
}
static int recruitNear(Boat& b, int id, float radius, bool sendNow) {
    int room = BOAT_CAP - b.load - pendingOf(id), n = 0;
    for (size_t i = 0; i < people.size() && room > 0; i++) {
        Person& p = people[i];
        if (!isCandidate(p) || len2(p.x - b.x, p.z - b.z) > radius) continue;
        p.boat = id; if (sendNow) p.state = P_TO_BOAT;
        room--; n++;
    }
    return n;
}
static void startReturn(Boat& b, int id) {
    computeDock();
    if (!dockOK) { b.state = B_PATROL; return; }
    int bi, bj, gi, gj; cellOf(b.x, b.z, bi, bj); runBFS(bi, bj); cellOf(dockX, dockZ, gi, gj);
    int best = -1, bd = 1 << 30;
    for (int di = -4; di <= 4; di++) for (int dj = -4; dj <= 4; dj++) {
        int i = gi + di, j = gj + dj;
        if (i < 0 || j < 0 || i >= GN || j >= GN || bfsD[i][j] < 0) continue;
        int c = abs(di) + abs(dj) * 2;                 // prefer cells closer to the shore
        if (c < bd) { bd = c; best = i * GN + j; }
    }
    if (best < 0) { b.state = B_PATROL; return; }
    float cx, cz; cellCenter(best / GN, best % GN, cx, cz);
    buildPath(b, best / GN, best % GN, cx, cz);
    b.state = B_RETURN;
    char m[160]; snprintf(m, sizeof m, "Rescue Boat %d is taking %d people to the cyclone shelter.", id + 1, b.load); setMsg(m);
}
static void wander(Boat& b) {
    int bi, bj; cellOf(b.x, b.z, bi, bj); runBFS(bi, bj);
    for (int k = 0; k < 80; k++) {
        int i = 2 + (int)(rnd() * (GN - 4)), j = 2 + (int)(rnd() * (GN - 4));
        if (bfsD[i][j] < 6) continue;
        float x, z; cellCenter(i, j, x, z);
        if (depthAt(x, z) < 1.0f) continue;
        buildPath(b, i, j, x, z);
        return;
    }
}
static void boatThink(Boat& b, int id) {
    int pend = pendingOf(id);
    switch (b.state) {
    case B_PATROL:
    case B_GO: {
        // people wading on the road right next to the boat? stop and pick them up
        if (b.load + pend < BOAT_CAP && recruitNear(b, id, 14.0f, false) > 0) {
            b.state = B_WAIT; b.timer = 0; sendPendingToBoat(id);
            char m[160]; snprintf(m, sizeof m, "Rescue Boat %d: SIREN! People in the water nearby - come to the boat!", id + 1); setMsg(m);
            return;
        }
        if (b.state == B_GO) {
            if (pend == 0 || b.timer > 60.0f) {             // nobody left to pick up, or the place is unreachable
                for (size_t i = 0; i < people.size(); i++)
                    if (people[i].boat == id && people[i].state != P_IN_BOAT) people[i].boat = -1;
                b.state = B_PATROL; b.path.clear();
            }
            return;
        }
        if (b.load >= BOAT_CAP) { startReturn(b, id); return; }
        bool any = false;
        for (size_t i = 0; i < people.size(); i++) if (isCandidate(people[i])) { any = true; break; }
        if (any) {
            int bi, bj; cellOf(b.x, b.z, bi, bj); runBFS(bi, bj);
            int best = -1, bestC = 1 << 30, bgi = 0, bgj = 0;
            for (size_t k = 0; k < people.size(); k++) {
                const Person& p = people[k];
                if (!isCandidate(p)) continue;
                int ci, cj; cellOf(p.x, p.z, ci, cj);
                for (int di = -4; di <= 4; di++) for (int dj = -4; dj <= 4; dj++) {
                    int ni = ci + di, nj = cj + dj;
                    if (ni < 0 || nj < 0 || ni >= GN || nj >= GN || bfsD[ni][nj] < 0) continue;
                    int cost = bfsD[ni][nj] * 2 + abs(di) + abs(dj);
                    if (cost < bestC) { bestC = cost; best = (int)k; bgi = ni; bgj = nj; }
                }
            }
            if (best >= 0) {
                float tx, tz; cellCenter(bgi, bgj, tx, tz);
                buildPath(b, bgi, bgj, tx, tz);
                int room = BOAT_CAP - b.load - pend, n = 0;
                float bx = people[best].x, bz = people[best].z;
                for (size_t k = 0; k < people.size() && room > 0; k++) {
                    Person& p = people[k];
                    if (!isCandidate(p) || len2(p.x - bx, p.z - bz) > 12.0f) continue;
                    p.boat = id; room--; n++;
                }
                b.state = B_GO; b.timer = 0;
                char m[160]; snprintf(m, sizeof m, "Rescue Boat %d is heading to %d stranded people.", id + 1, n); setMsg(m);
                return;
            }
        }
        if (b.load > 0) { startReturn(b, id); return; }
        if (b.path.empty() || b.pi >= (int)b.path.size() - 1) wander(b);
    } break;
    case B_WAIT: {
        if (b.load + pend < BOAT_CAP) recruitNear(b, id, 16.0f, true);
        pend = pendingOf(id);
        bool done = (pend == 0 && b.timer > 1.5f);
        if (!done && b.timer > 35.0f) {                       // give up waiting for people who can't reach
            for (size_t i = 0; i < people.size(); i++) {
                Person& p = people[i];
                if (p.boat == id && p.state != P_IN_BOAT && p.state != P_SAFE) {
                    if (p.state == P_TO_BOAT) { p.state = P_STRANDED; p.onRoof = p.y > terrainH(p.x, p.z) + 1.0f && p.onRoof; }
                    p.boat = -1;
                }
            }
            done = true;
        }
        if (done) {
            if (b.load >= (BOAT_CAP * 3) / 4) startReturn(b, id);
            else { b.state = B_PATROL; b.path.clear(); }
        }
    } break;
    case B_RETURN: if (b.path.empty()) startReturn(b, id); break;
    default: break;
    }
}

static void seatLocal(int seat, float& sx, float& sz) {
    sx = (seat % 2) ? 0.62f : -0.62f;
    sz = 1.35f - (seat / 2) * 0.72f;
}
static void boatLocalToWorld(const Boat& b, float lx, float lz, float& wx, float& wz) {
    float c = cosf(b.head), s = sinf(b.head);
    wx = b.x + c * lx + s * lz; wz = b.z - s * lx + c * lz;
}

static void updateBoats(float dt) {
    for (int id = 0; id < NBOAT; id++) {
        Boat& b = boats[id];
        b.think -= dt;
        if (b.think <= 0) { b.think = 0.5f; boatThink(b, id); }
        switch (b.state) {
        case B_PATROL:
            b.siren = false;
            followPath(b, dt, 4.5f, 4.0f);
            break;
        case B_GO: {
            bool arrived = followPath(b, dt, 7.0f, 3.0f);
            b.timer += dt;
            b.siren = len2(b.tx - b.x, b.tz - b.z) < 40.0f;
            if (arrived) {
                b.state = B_WAIT; b.timer = 0; b.siren = true; sendPendingToBoat(id);
                char m[160]; snprintf(m, sizeof m, "Rescue Boat %d arrived - siren on, people are coming to the boat.", id + 1); setMsg(m);
            }
        } break;
        case B_WAIT:
            b.siren = true; b.timer += dt;
            steerBoat(b, dt, 0, 0);
            break;
        case B_RETURN:
            b.siren = false;
            if (followPath(b, dt, 7.0f, 3.0f)) { b.state = B_UNLOAD; b.timer = 0; }
            break;
        case B_UNLOAD:
            b.siren = false; b.timer += dt;
            steerBoat(b, dt, 0, 0);
            if (b.timer > 0.5f) {
                b.timer = 0;
                int who = -1;
                for (size_t i = 0; i < people.size(); i++) if (people[i].boat == id && people[i].state == P_IN_BOAT) { who = (int)i; break; }
                if (who < 0) { b.state = B_PATROL; b.path.clear(); b.load = 0; for (int s = 0; s < BOAT_CAP; s++) b.seatUsed[s] = 0; break; }
                Person& p = people[who];
                b.seatUsed[p.seat] = 0; b.load--;
                p.state = P_WALK; p.boat = -1; p.seat = -1; p.rescued = true; p.onRoof = false;
                computeDock();
                p.px[0] = shoreX + rr(-1.5f, 1.5f); p.pz[0] = shoreZ + 1.0f;
                p.px[1] = SHX + rr(-9, 9);         p.pz[1] = 43.5f;
                p.np = 2; p.seg = 0;
                boatRescued++;
            }
            break;
        }
        // wake foam behind a moving boat
        b.wakeT -= dt;
        if (b.spd > 1.2f && b.wakeT <= 0) {
            b.wakeT = 0.07f;
            for (int s = -1; s <= 1; s += 2) {
                Wake w; boatLocalToWorld(b, s * 0.7f, -3.0f, w.x, w.z);
                float c = cosf(b.head), sn = sinf(b.head);
                w.vx = c * s * 1.4f - sn * 0.5f; w.vz = -sn * s * 1.4f - c * 0.5f;
                w.age = 0; w.s = 0.6f + b.spd * 0.08f;
                wakes.push_back(w);
            }
        }
    }
    for (size_t i = 0; i < wakes.size();) {
        Wake& w = wakes[i];
        w.age += dt; w.x += w.vx * dt; w.z += w.vz * dt; w.vx *= 0.98f; w.vz *= 0.98f; w.s += dt * 0.9f;
        if (w.age > 3.2f) { wakes[i] = wakes.back(); wakes.pop_back(); } else i++;
    }
}

static void drawBoatModel(int id) {
    const Boat& b = boats[id];
    float bob = 0.07f * sinf(rt * 1.9f + id * 1.3f);
    float rollW = 2.5f * windAmt * sinf(rt * 1.3f + id);
    glPushMatrix();
    glTranslatef(b.x, waterLevel + 0.05f + bob, b.z);
    glRotatef(b.head / DEG, 0, 1, 0);
    glRotatef(-b.pitch, 1, 0, 0);
    glRotatef(b.roll + rollW, 0, 0, 1);
    boxB(0, -0.38f, -0.1f, 1.75f, 0.45f, 5.6f, 0.20f, 0.21f, 0.24f);          // hull
    for (int s = -1; s <= 1; s += 2) {                                          // inflatable tubes
        glColor3f(0.96f, 0.42f, 0.08f);
        glPushMatrix(); glTranslatef(s * 0.98f, 0.08f, -2.9f); glutSolidCylinder(0.42, 5.65, 14, 1); glPopMatrix();
        glPushMatrix(); glTranslatef(s * 0.98f, 0.08f, 2.75f); glutSolidSphere(0.42, 12, 8); glPopMatrix();
        glColor3f(0.95f, 0.95f, 0.92f);
        for (int k = 0; k < 2; k++) { glPushMatrix(); glTranslatef(s * 0.98f, 0.08f, -1.6f + k * 2.6f); glutSolidCylinder(0.435, 0.24, 14, 1); glPopMatrix(); }
    }
    glColor3f(0.96f, 0.42f, 0.08f);
    glPushMatrix(); glTranslatef(-0.98f, 0.08f, 2.75f); glRotatef(90, 0, 1, 0); glutSolidCylinder(0.40, 1.96, 12, 1); glPopMatrix();
    boxB(0, -0.3f, -2.95f, 1.6f, 0.7f, 0.14f, 0.25f, 0.25f, 0.28f);           // transom
    float tilt = clampf(-b.roll * 2.0f, -25, 25);
    glPushMatrix(); glTranslatef(0, 0.0f, -3.15f); glRotatef(tilt, 0, 1, 0);     // outboard motor
    boxB(0, 0.05f, -0.15f, 0.5f, 0.7f, 0.6f, 0.08f, 0.08f, 0.09f);
    boxB(0, -0.95f, -0.2f, 0.14f, 1.0f, 0.16f, 0.15f, 0.15f, 0.16f);
    boxB(0, 0.6f, -0.15f, 0.42f, 0.1f, 0.5f, 0.85f, 0.85f, 0.85f);
    glPopMatrix();
    boxB(0, 0.05f, -1.5f, 0.75f, 0.95f, 0.6f, 0.92f, 0.92f, 0.90f);           // console
    boxB(0, 1.0f, -1.25f, 0.72f, 0.38f, 0.05f, 0.55f, 0.70f, 0.80f);
    boxB(0, 0.05f, -2.05f, 0.08f, 2.3f, 0.08f, 0.6f, 0.6f, 0.62f);             // mast
    boxB(0, 2.35f, -2.05f, 0.9f, 0.12f, 0.22f, 0.15f, 0.15f, 0.17f);
    bool blink = fmodf(rt * 3.0f, 1.0f) < 0.5f;
    glDisable(GL_LIGHTING);
    float rOn = (b.siren && blink) ? 1.0f : 0.3f, bOn = (b.siren && !blink) ? 1.0f : 0.3f;
    glColor3f(rOn, 0.06f, 0.05f); boxC(-0.24f, 2.55f, -2.05f, 0.32f, 0.16f, 0.18f);
    glColor3f(0.05f, 0.15f * bOn, bOn); boxC(0.24f, 2.55f, -2.05f, 0.32f, 0.16f, 0.18f);
    glEnable(GL_LIGHTING);
    if (b.siren) {
        if (blink) addGlow(-0.24f, 2.55f, -2.05f, 1.0f, 0.12f, 0.08f, 0.45f, 1.0f);
        else       addGlow(0.24f, 2.55f, -2.05f, 0.2f, 0.35f, 1.0f, 0.45f, 1.0f);
    }
    boxB(0, 2.05f, -1.85f, 0.26f, 0.24f, 0.3f, 0.3f, 0.3f, 0.32f);              // search light
    if (night > 0.25f) addGlow(0, 2.17f, -1.68f, 1.0f, 0.96f, 0.82f, 0.28f, night);
    glColor3f(1.0f, 0.35f, 0.1f);                                                // life ring on the console
    glPushMatrix(); glTranslatef(0.39f, 0.6f, -1.5f); glRotatef(90, 0, 1, 0); glutSolidTorus(0.06, 0.24, 6, 14); glPopMatrix();

    // crew: driver + rescuer at the bow (megaphone when the siren is on)
    static const float CS[3] = { 0.15f, 0.25f, 0.45f }, CP[3] = { 0.12f, 0.12f, 0.16f }, CH[3] = { 0.1f, 0.08f, 0.06f };
    drawHuman(0, 0.08f, -2.5f, 0, 0, 0, 0, CS, CP, CH, SKIN[2], 1.0f, true);
    drawHuman(0, 0.08f, 2.0f, 0, 0, b.siren ? 2 : 0, rt, CS, CP, CH, SKIN[1], 1.0f, true);
    // rescued passengers
    for (size_t i = 0; i < people.size(); i++) {
        const Person& p = people[i];
        if (p.boat != id || p.state != P_IN_BOAT) continue;
        float sx, sz; seatLocal(p.seat, sx, sz);
        glPushMatrix(); glTranslatef(sx, 0.42f, sz); glRotatef(sx < 0 ? 90.0f : -90.0f, 0, 1, 0);
        drawSeated(p.sh, p.pa, p.ha, p.sk, p.child ? 0.7f : 0.95f, 10.0f * sinf(rt * 2 + p.ph), true);
        glPopMatrix();
    }
    glPopMatrix();
}

// ----------------------------------------------------------------------------
//  Build / reset
// ----------------------------------------------------------------------------
static void makeHouses() {
    float rowZ[4] = { -7.5f, 7.5f, 17.5f, 32.5f };
    float rowAng[4] = { 0, 180, 0, 180 };
    float rowRoad[4] = { 0, 0, 25, 25 };
    for (int row = 0; row < 4; row++) {
        float x = -86 + rr(0, 3);
        while (x < 86) {
            float rp = rnd(); int type = rp < 0.30f ? 0 : (rp < 0.55f ? 1 : (rp < 0.72f ? 2 : 3));
            House H = newHouse(type, rowAng[row]);
            H.x = x + H.w / 2; H.z = rowZ[row];
            bool skip = false;
            for (size_t i = 2; i < roads.size(); i++) {
                float rx = roads[i].x1;
                if (fabsf(H.x - rx) < H.w / 2 + 3.5f) { x = rx + 3.5f; skip = true; break; }
            }
            if (skip) continue;
            if (len2(H.x - SHX, H.z - SHZ) < 26.0f) { x += H.w + 2; continue; }
            if (rnd() < 0.08f) { x += H.w + rr(2, 5); continue; }
            setHouseY(H);
            houses.push_back(H);
            int side = (rowZ[row] < rowRoad[row]) ? -1 : 1;
            makePeopleFor((int)houses.size() - 1, rowRoad[row], side);
            x = H.x + H.w / 2 + rr(2.5f, 6.0f);
        }
    }
    for (int i = 0; i < 70 && houses.size() < 90; i++) {
        float z = (i % 2) ? rr(-80, -50) : rr(46, 70), x = rr(-85, 85);
        if (len2(x - SHX, z - SHZ) < 28.0f) continue;
        float rp = rnd(); int type = rp < 0.4f ? 0 : (rp < 0.7f ? 1 : 3);
        House H = newHouse(type, 90.0f * (int)(rnd() * 3.99f));
        H.x = x; H.z = z;
        if (!spotFree(x, z, 5.0f) || terrainH(x, z) < 0.6f || terrainH(x, z) > 8.0f) continue;
        setHouseY(H);
        houses.push_back(H);
    }
}

static void buildScene() {
    winLights.clear();
    sceneList = glGenLists(1);
    glNewList(sceneList, GL_COMPILE);
    drawTerrainMesh();
    drawOuterTerrain();
    glEnable(GL_POLYGON_OFFSET_FILL);
    glPolygonOffset(-1.0f, -1.0f);
    for (size_t i = 0; i < roads.size(); i++) drawRoadStrip(roads[i], 0.10f + i * 0.012f);
    for (size_t i = 0; i < extRoads.size(); i++) drawRoadStrip(extRoads[i], 0.45f);
    glDisable(GL_POLYGON_OFFSET_FILL);
    drawLampPosts();
    for (size_t i = 0; i < houses.size(); i++) drawHouse(houses[i]);
    for (size_t i = 0; i < outerHouses.size(); i++) drawHouse(outerHouses[i]);
    for (size_t i = 0; i < outerTrees.size(); i++) drawTree(outerTrees[i], 0);
    for (size_t i = 0; i < rocks.size(); i++) drawRock(rocks[i]);
    drawShelterStatic();
    glEndList();
}

static void initBoats() {
    for (int i = 0; i < NBOAT; i++) {
        Boat& b = boats[i];
        b.x0 = -70.0f + i * 35.0f; b.z0 = riverZ(b.x0); b.h0 = (i % 2) ? -PI / 2 : PI / 2;
    }
}
static void resetBoats() {
    for (int i = 0; i < NBOAT; i++) {
        Boat& b = boats[i];
        b.x = b.x0; b.z = b.z0; b.head = b.h0; b.spd = 0; b.roll = 0; b.pitch = 0;
        b.state = B_PATROL; b.path.clear(); b.pi = 0; b.load = 0; b.tx = b.x; b.tz = b.z;
        b.think = 0.1f * i; b.timer = 0; b.wakeT = 0; b.siren = false;
        for (int s = 0; s < BOAT_CAP; s++) b.seatUsed[s] = 0;
    }
    wakes.clear();
}
static void resetSim() {
    waterLevel = WATER_START; started = false; running = false; sheltered = 0; boatRescued = 0;
    simT = 0; peakT = -1; lastStage = 0; powerOn = true; shelterSirenT = 0;
    for (size_t i = 0; i < people.size(); i++) {
        Person& p = people[i];
        p.x = p.sx; p.z = p.sz; p.y = 0; p.seg = 0; p.np = 4; p.state = P_HOME;
        p.boat = -1; p.seat = -1; p.onRoof = false; p.rescued = false; p.anim = 0;
        for (int k = 0; k < 4; k++) { p.px[k] = p.rx[k]; p.pz[k] = p.rz[k]; }
    }
    for (size_t i = 0; i < cars.size(); i++) { cars[i].t = cars[i].t0; cars[i].stuck = false; }
    resetBoats();
    setMsg("Simulation reset. Press START (ENTER) to begin.");
}
static void startSim() {
    if (!started) setMsg("Cyclone approaching! Heavy rain begins - the river will overflow.");
    started = true; running = true;
}

// ----------------------------------------------------------------------------
//  Update (simulation time)
// ----------------------------------------------------------------------------
static int stageNo() { return waterLevel < 0.3f ? 0 : (waterLevel < 1.2f ? 1 : (waterLevel < 2.2f ? 2 : (waterLevel < 3.0f ? 3 : 4))); }

static void updatePeople(float dt) {
    for (size_t i = 0; i < people.size(); i++) {
        Person& p = people[i];
        switch (p.state) {
        case P_HOME:
            if (houses[p.house].y + 0.25f < waterLevel) {           // house flooded -> climb onto the roof
                p.state = P_STRANDED; p.onRoof = true; p.x = p.roofX; p.z = p.roofZ; p.y = p.roofY;
                break;
            }
            if (waterLevel > p.trig) { p.state = P_WALK; p.seg = 0; }
            break;
        case P_WALK: {
            float tx = p.px[p.seg], tz = p.pz[p.seg];
            float dx = tx - p.x, dz = tz - p.z, dist = len2(dx, dz);
            float dep = depthAt(p.x, p.z);
            if (!p.rescued && dep > 1.0f) { p.state = P_STRANDED; p.onRoof = false; break; }
            float f = dep < 0.15f ? 1.0f : (dep < 0.5f ? 0.65f : 0.4f);
            float step = p.speed * dt * f;
            p.anim += step;
            if (dist <= step) {
                p.x = tx; p.z = tz; p.seg++;
                if (p.seg >= p.np) { p.state = P_SAFE; sheltered++; }
            } else { p.x += dx / dist * step; p.z += dz / dist * step; p.yaw = atan2f(dx, dz) / DEG; }
        } break;
        case P_STRANDED: p.anim += dt; break;
        case P_TO_BOAT: {
            if (p.boat < 0) { p.state = P_STRANDED; break; }
            Boat& b = boats[p.boat];
            float dx = b.x - p.x, dz = b.z - p.z, dist = len2(dx, dz);
            if (p.onRoof) { p.y -= 1.6f * dt; if (p.y <= waterLevel + 0.3f) p.onRoof = false; }
            if (dist < 1.8f) {
                int seat = -1;
                for (int s = 0; s < BOAT_CAP; s++) if (!b.seatUsed[s]) { seat = s; break; }
                if (seat < 0) { p.state = P_STRANDED; p.boat = -1; break; }
                b.seatUsed[seat] = 1; b.load++;
                p.seat = seat; p.state = P_IN_BOAT; p.onRoof = false; p.rescued = true;
            } else {
                float step = (p.child ? 0.9f : 1.2f) * dt;
                p.x += dx / dist * step; p.z += dz / dist * step; p.yaw = atan2f(dx, dz) / DEG; p.anim += step;
            }
        } break;
        case P_IN_BOAT: {
            const Boat& b = boats[p.boat];
            float sx, sz; seatLocal(p.seat, sx, sz); boatLocalToWorld(b, sx, sz, p.x, p.z);
        } break;
        default: break;
        }
    }
}

static void update(float dt) {
    simT += dt;
    if (waterLevel < WATER_MAX) {
        waterLevel += RISE_RATE * (0.6f + 0.8f * rainAmt) * dt;
        if (waterLevel >= WATER_MAX) { waterLevel = WATER_MAX; peakT = simT; setMsg("Peak flood reached. Rescue boats keep searching for stranded people."); }
    }
    int st = stageNo();
    if (st > lastStage) {
        lastStage = st;
        if (st == 1) setMsg("Stage 1: the river is overflowing its banks. Signal No. 3.");
        if (st == 2) { setMsg("Stage 2 WARNING: shelter siren! Danger signal No. 7 - evacuate to the cyclone shelter now!"); shelterSirenT = 14.0f; }
        if (st == 3) { setMsg("Stage 3 DANGER: power grid shut down for safety. Signal No. 9. Rescue boats in the streets."); powerOn = false; shelterSirenT = 10.0f; }
        if (st == 4) setMsg("Stage 4 SEVERE: Great danger signal No. 10. Boats are rescuing people from roofs.");
    }
    updatePeople(dt);
    for (size_t i = 0; i < cars.size(); i++) {
        Car& c = cars[i]; if (c.stuck) continue;
        const Road& R = roads[c.road];
        float sgn = c.speed > 0 ? 1.0f : -1.0f, x, z, ax, az;
        roadPoint(R, c.t, x, z);
        roadPoint(R, clampf(c.t + sgn * 4.0f, 0, R.len), ax, az);
        if (terrainH(x, z) + 0.1f < waterLevel || terrainH(ax, az) + 0.1f < waterLevel) { c.stuck = true; continue; }
        c.t += c.speed * dt;
        if (c.t > R.len) c.t -= R.len;
        if (c.t < 0) c.t += R.len;
    }
    updateBoats(dt);
}

// ============================================================================
//  SOUND  -  everything is synthesised in real time (no audio files)
// ============================================================================
static const int SRATE = 22050, AFRAMES = 1024, NABUF = 6;
struct AudioTargets {
    float master, rain, wind, slosh, birds, crick;
    float engL[NBOAT], engR[NBOAT], engThr[NBOAT];
    float sirL[NBOAT + 1], sirR[NBOAT + 1];        // last one = shelter siren
};
static AudioTargets AT;
struct ThunderV { bool on; float delay, gain, pan, t, lp1, lp2; };
static ThunderV thunder[4];
static void queueThunder(float delay, float gain, float pan) {
    for (int i = 0; i < 4; i++)
        if (!thunder[i].on) {
            thunder[i].on = true; thunder[i].delay = delay; thunder[i].gain = gain; thunder[i].pan = pan;
            thunder[i].t = 0; thunder[i].lp1 = thunder[i].lp2 = 0; return;
        }
}
struct SynthState {
    unsigned int ns;
    float master, rain, wind, slosh, birds, crick;
    float rf[2][3], wf[2][2], sf[3];
    float engL[NBOAT], engR[NBOAT], engThr[NBOAT], engPh[NBOAT], engLp[NBOAT], engNz[NBOAT], engDc[NBOAT];
    float sirL[NBOAT + 1], sirR[NBOAT + 1], sirPh[NBOAT + 1], sirT[NBOAT + 1], sirLp[NBOAT + 1];
    float dPh[8], dF[8], dEnv[8], dPan[8]; int dNext;
    bool cOn[3]; float cT[3], cDur[3], cF0[3], cF1[3], cPh[3], cPan[3]; int cReps[3];
    float crT, crPh, crPh2, crGate;
    float tsec;
};
static SynthState SY;
static inline float snoise() { SY.ns = SY.ns * 1664525u + 1013904223u; return (float)((SY.ns >> 9) & 0x7FFF) / 16383.5f - 1.0f; }
static inline float unoise() { return 0.5f + 0.5f * snoise(); }
static inline float sclip(float x) { x = clampf(x, -3.0f, 3.0f); return x * (27.0f + x * x) / (27.0f + 9.0f * x * x); }

static void synthBlock(short* out, int frames) {
    const float inv = 1.0f / SRATE, k = 0.0012f, TP = 2.0f * PI;
    for (int n = 0; n < frames; n++) {
        SY.master += (AT.master - SY.master) * k;
        SY.rain += (AT.rain - SY.rain) * k;   SY.wind += (AT.wind - SY.wind) * k;
        SY.slosh += (AT.slosh - SY.slosh) * k; SY.birds += (AT.birds - SY.birds) * k; SY.crick += (AT.crick - SY.crick) * k;
        float L = 0, R = 0;
        // --- rain: band-limited hiss + low rumble, two independent channels + droplets
        if (SY.rain > 0.0005f) {
            for (int c = 0; c < 2; c++) {
                float w = snoise();
                SY.rf[c][0] += 0.5f * (w - SY.rf[c][0]);
                SY.rf[c][1] += 0.035f * (SY.rf[c][0] - SY.rf[c][1]);
                SY.rf[c][2] += 0.012f * (w - SY.rf[c][2]);
                float s = ((SY.rf[c][0] - SY.rf[c][1]) * 0.55f + SY.rf[c][2] * 2.2f) * SY.rain;
                if (c == 0) L += s; else R += s;
            }
            if (unoise() < SY.rain * 0.0035f) {
                int d = SY.dNext; SY.dNext = (SY.dNext + 1) % 8;
                SY.dPh[d] = 0; SY.dF[d] = (1500.0f + 3700.0f * unoise()) * inv; SY.dEnv[d] = (0.06f + 0.22f * unoise()) * SY.rain; SY.dPan[d] = unoise();
            }
        }
        for (int d = 0; d < 8; d++)
            if (SY.dEnv[d] > 0.0005f) {
                float s = sinf(TP * SY.dPh[d]) * SY.dEnv[d];
                SY.dPh[d] += SY.dF[d]; if (SY.dPh[d] > 1) SY.dPh[d] -= 1;
                SY.dF[d] *= 0.99985f; SY.dEnv[d] *= 0.9972f;
                L += s * (1 - SY.dPan[d]); R += s * SY.dPan[d];
            }
        // --- wind: slowly modulated low noise with gusts
        if (SY.wind > 0.0005f) {
            float gust = 0.55f + 0.45f * sinf(SY.tsec * 0.41f) * sinf(SY.tsec * 0.173f + 1.1f);
            float c = 0.004f + 0.02f * gust;
            for (int ch = 0; ch < 2; ch++) {
                float w = snoise();
                SY.wf[ch][0] += c * (w - SY.wf[ch][0]); SY.wf[ch][1] += c * (SY.wf[ch][0] - SY.wf[ch][1]);
                float s = SY.wf[ch][1] * 14.0f * gust * SY.wind;
                if (ch == 0) L += s; else R += s;
            }
        }
        // --- flood water lapping / flowing
        if (SY.slosh > 0.0005f) {
            float w = snoise();
            SY.sf[0] += 0.008f * (w - SY.sf[0]); SY.sf[1] += 0.06f * (w - SY.sf[1]);
            float env = 0.45f + 0.55f * fabsf(sinf(SY.tsec * 1.1f + sinf(SY.tsec * 0.37f) * 2.0f));
            float s = (SY.sf[0] * 5.0f + (SY.sf[1] - SY.sf[0]) * 0.35f) * env * SY.slosh;
            L += s; R += s * 0.92f;
        }
        // --- boat engines (outboard motor "putt" pulses + hull splash)
        for (int b = 0; b < NBOAT; b++) {
            SY.engL[b] += (AT.engL[b] - SY.engL[b]) * k; SY.engR[b] += (AT.engR[b] - SY.engR[b]) * k;
            SY.engThr[b] += (AT.engThr[b] - SY.engThr[b]) * 0.0004f;
            if (SY.engL[b] + SY.engR[b] < 0.0008f) continue;
            float f = 22.0f + b * 1.7f + SY.engThr[b] * 40.0f;
            SY.engPh[b] += f * inv; if (SY.engPh[b] >= 1) SY.engPh[b] -= 1;
            float ph = SY.engPh[b];
            float pulse = ph < 0.32f ? sinf(PI * ph / 0.32f) : 0.0f;
            float s = pulse * pulse * 0.9f + 0.2f * sinf(TP * ph * 3.0f) + snoise() * 0.3f * pulse;
            SY.engLp[b] += 0.18f * (s - SY.engLp[b]);
            SY.engNz[b] += 0.05f * (snoise() - SY.engNz[b]);
            float o = SY.engLp[b] * 0.6f + SY.engNz[b] * 1.6f * SY.engThr[b];
            SY.engDc[b] += 0.002f * (o - SY.engDc[b]);
            o -= SY.engDc[b];
            L += o * SY.engL[b]; R += o * SY.engR[b];
        }
        // --- sirens: rescue boats (fast wail) and the shelter (slow wail)
        for (int s = 0; s <= NBOAT; s++) {
            SY.sirL[s] += (AT.sirL[s] - SY.sirL[s]) * k; SY.sirR[s] += (AT.sirR[s] - SY.sirR[s]) * k;
            if (SY.sirL[s] + SY.sirR[s] < 0.0008f) { SY.sirT[s] = 0; continue; }
            SY.sirT[s] += inv;
            float per = (s == NBOAT) ? 7.0f : 3.0f;
            float u = 0.5f - 0.5f * cosf(TP * SY.sirT[s] / per);
            float f = (s == NBOAT) ? 380.0f + 520.0f * u : 640.0f + 560.0f * u;
            SY.sirPh[s] += f * inv; if (SY.sirPh[s] >= 1) SY.sirPh[s] -= 1;
            float ph = SY.sirPh[s];
            float w = sinf(TP * ph) + 0.28f * sinf(3 * TP * ph) + 0.12f * sinf(5 * TP * ph);
            SY.sirLp[s] += 0.35f * (w - SY.sirLp[s]);
            L += SY.sirLp[s] * 0.17f * SY.sirL[s]; R += SY.sirLp[s] * 0.17f * SY.sirR[s];
        }
        // --- thunder (arrives later than the flash - speed of sound)
        for (int t = 0; t < 4; t++) {
            ThunderV& th = thunder[t];
            if (!th.on) continue;
            if (th.delay > 0) { th.delay -= inv; continue; }
            th.t += inv;
            float env = th.t < 0.06f ? th.t / 0.06f : expf(-(th.t - 0.06f) / 1.5f);
            float w = snoise();
            th.lp1 += 0.03f * (w - th.lp1); th.lp2 += 0.25f * (w - th.lp2);
            float mod = 0.6f + 0.4f * sinf(th.t * 9.0f + sinf(th.t * 3.0f) * 3.0f);
            float s = (th.lp1 * 5.0f + (th.t < 0.5f ? th.lp2 * 0.5f * (1 - th.t * 2) : 0.0f)) * env * mod * th.gain;
            L += s * sqrtf(0.5f * (1 - th.pan)); R += s * sqrtf(0.5f * (1 + th.pan));
            if (th.t > 6.5f) th.on = false;
        }
        // --- birds (calm day) and crickets (calm night)
        if (SY.birds > 0.003f) {
            for (int c = 0; c < 3; c++) {
                if (!SY.cOn[c]) {
                    if (unoise() < 0.00003f) {
                        SY.cOn[c] = true; SY.cT[c] = 0; SY.cReps[c] = 2 + (int)(unoise() * 3.99f);
                        SY.cF0[c] = 2600.0f + 1200.0f * unoise(); SY.cF1[c] = SY.cF0[c] + (unoise() - 0.4f) * 2000.0f;
                        SY.cDur[c] = 0.05f + 0.06f * unoise(); SY.cPan[c] = unoise();
                    }
                    continue;
                }
                float t = SY.cT[c];
                if (t < SY.cDur[c]) {
                    float u = t / SY.cDur[c];
                    SY.cPh[c] += mixf(SY.cF0[c], SY.cF1[c], u) * inv; if (SY.cPh[c] > 1) SY.cPh[c] -= 1;
                    float s = sinf(TP * SY.cPh[c]) * sinf(PI * u) * 0.10f * SY.birds;
                    L += s * (1 - SY.cPan[c]); R += s * SY.cPan[c];
                } else if (t > SY.cDur[c] + 0.06f) {
                    SY.cT[c] = -inv; if (--SY.cReps[c] <= 0) SY.cOn[c] = false;
                }
                SY.cT[c] += inv;
            }
        }
        if (SY.crick > 0.003f) {
            SY.crT += inv;
            float on = (fmodf(SY.crT * 30.0f, 1.0f) < 0.45f && fmodf(SY.crT * 0.9f, 1.0f) < 0.6f) ? 1.0f : 0.0f;
            SY.crGate += (on - SY.crGate) * 0.02f;
            SY.crPh += 4300.0f * inv; if (SY.crPh > 1) SY.crPh -= 1;
            SY.crPh2 += 4720.0f * inv; if (SY.crPh2 > 1) SY.crPh2 -= 1;
            float on2 = fmodf(SY.crT * 1.3f + 0.4f, 1.0f) < 0.5f ? 1.0f : 0.0f;
            float s1 = sinf(TP * SY.crPh) * SY.crGate * 0.045f * SY.crick;
            float s2 = sinf(TP * SY.crPh2) * SY.crGate * on2 * 0.03f * SY.crick;
            L += s1 * 0.8f + s2 * 0.3f; R += s1 * 0.4f + s2 * 0.9f;
        }
        SY.tsec += inv; if (SY.tsec > 10000.0f) SY.tsec -= 10000.0f;
        L = sclip(L * SY.master); R = sclip(R * SY.master);
        out[2 * n] = (short)(L * 30000.0f); out[2 * n + 1] = (short)(R * 30000.0f);
    }
}

#ifdef _WIN32
static HWAVEOUT g_hwo = 0;
static WAVEHDR  g_hdr[NABUF];
static short    g_abuf[NABUF][AFRAMES * 2];
static int      g_nextBuf = 0;
static bool     g_audioOK = false;
static void initAudio() {
    WAVEFORMATEX wf; memset(&wf, 0, sizeof wf);
    wf.wFormatTag = WAVE_FORMAT_PCM; wf.nChannels = 2; wf.nSamplesPerSec = SRATE; wf.wBitsPerSample = 16;
    wf.nBlockAlign = 4; wf.nAvgBytesPerSec = SRATE * 4;
    if (waveOutOpen(&g_hwo, WAVE_MAPPER, &wf, 0, 0, CALLBACK_NULL) != MMSYSERR_NOERROR) return;
    for (int i = 0; i < NABUF; i++) {
        memset(&g_hdr[i], 0, sizeof(WAVEHDR));
        g_hdr[i].lpData = (LPSTR)g_abuf[i]; g_hdr[i].dwBufferLength = AFRAMES * 4;
        waveOutPrepareHeader(g_hwo, &g_hdr[i], sizeof(WAVEHDR));
        synthBlock(g_abuf[i], AFRAMES);
        waveOutWrite(g_hwo, &g_hdr[i], sizeof(WAVEHDR));
    }
    g_audioOK = true;
}
static void pumpAudio() {
    if (!g_audioOK) return;
    for (int guard = 0; guard < NABUF; guard++) {
        volatile DWORD* fl = &g_hdr[g_nextBuf].dwFlags;
        if (!(*fl & WHDR_DONE)) break;
        synthBlock(g_abuf[g_nextBuf], AFRAMES);
        *fl &= ~WHDR_DONE;
        waveOutWrite(g_hwo, &g_hdr[g_nextBuf], sizeof(WAVEHDR));
        g_nextBuf = (g_nextBuf + 1) % NABUF;
    }
}
static void closeAudio() {
    if (!g_audioOK) return;
    waveOutReset(g_hwo);
    for (int i = 0; i < NABUF; i++) waveOutUnprepareHeader(g_hwo, &g_hdr[i], sizeof(WAVEHDR));
    waveOutClose(g_hwo);
    g_audioOK = false;
}
#else
static void initAudio() {}
static void pumpAudio() {}
static void closeAudio() {}
#endif

// distance attenuation + stereo panning of a sound source for the listener
static void attn(float sx, float sy, float sz, float base, float& gl, float& gr) {
    float dx = sx - lisX, dy = sy - lisY, dz = sz - lisZ, d = sqrtf(dx * dx + dy * dy + dz * dz);
    float a = 16.0f / (d + 16.0f) * clamp01(1.0f - d / 380.0f) * base;
    float pn = d > 0.5f ? clampf((dx * lisRX + dz * lisRZ) / d, -1.0f, 1.0f) * 0.85f : 0.0f;
    gl = a * sqrtf(0.5f * (1 - pn)); gr = a * sqrtf(0.5f * (1 + pn));
}
static void computeAudioTargets() {
    AT.master = soundOn ? 0.9f : 0.0f;
    bool close = (viewMode == V_PERSON || viewMode == V_BOAT);
    AT.rain = rainAmt * (close ? 0.85f : 0.55f);
    AT.wind = windAmt * windAmt * (close ? 0.9f : 0.6f);
    float dep = depthAt(lisX, lisZ);
    if (viewMode == V_PERSON)    AT.slosh = dep > 0.05f ? clampf(0.35f + dep * 0.4f, 0, 1) : 0.0f;
    else if (viewMode == V_BOAT) AT.slosh = 0.55f;
    else                         AT.slosh = clamp01((waterLevel - WATER_START) / 2.0f) * 0.25f;
    float calm = 1.0f - clamp01(rainAmt * 3.0f);
    AT.birds = (1 - night) * calm * 0.8f;
    AT.crick = night * calm * 0.7f;
    for (int i = 0; i < NBOAT; i++) {
        const Boat& b = boats[i];
        float thr = running ? clamp01(fabsf(b.spd) / 7.0f) : 0.0f;
        float base = started ? (0.45f + 0.55f * thr) : 0.3f;
        if (started && !running) base = 0.3f;
        attn(b.x, waterLevel + 0.5f, b.z, base * 0.8f, AT.engL[i], AT.engR[i]);
        AT.engThr[i] = thr;
        if (running && b.siren) attn(b.x, waterLevel + 2.5f, b.z, 1.0f, AT.sirL[i], AT.sirR[i]);
        else AT.sirL[i] = AT.sirR[i] = 0;
    }
    if (shelterSirenT > 0) attn(SHX, PAD + 18.0f, SHZ, 1.4f, AT.sirL[NBOAT], AT.sirR[NBOAT]);
    else AT.sirL[NBOAT] = AT.sirR[NBOAT] = 0;
}

// ============================================================================
//  Weather (real time): rain, wind, storm sky, lightning, rain particles
// ============================================================================
struct Drop { float x, y, z; };
static const int NDROP = 2200;
static Drop drops[NDROP];
struct Ripple { float x, z, t; };
static const int NRIP = 90;
static Ripple ripples[NRIP];
static float focX = 0, focY = 0, focZ = 0;       // centre of the rain volume (in front of the camera)

static void respawnDrop(Drop& d, bool anyHeight) {
    d.x = focX + rr(-35, 35); d.z = focZ + rr(-35, 35);
    d.y = anyHeight ? focY + rr(-20, 28) : focY + rr(20, 28);
}
static void weatherUpdate(float dt) {
    if (!started) rainTarget = 0.0f;
    else if (waterLevel < WATER_MAX) rainTarget = clamp01(0.35f + simT * 0.025f);
    else rainTarget = std::max(0.3f, 1.0f - (simT - peakT) / 80.0f);
    rainAmt += (rainTarget - rainAmt) * std::min(1.0f, dt * 0.5f);
    float wt = started ? 0.15f + 0.85f * rainTarget : 0.12f;
    windAmt += (wt - windAmt) * std::min(1.0f, dt * 0.4f);
    storm = clamp01(0.08f + rainAmt * 0.92f);
    float nt = nightMode ? 1.0f : 0.0f;
    night += (nt - night) * std::min(1.0f, dt * 1.2f);
    if (fabsf(nt - night) < 0.003f) night = nt;
    if (hudMsgT > 0) hudMsgT -= dt;
    if (shelterSirenT > 0 && running) shelterSirenT -= dt;

    // lightning + thunder
    if (rainAmt > 0.55f) {
        nextBolt -= dt;
        if (nextBolt <= 0) {
            nextBolt = rr(6, 16);
            float a = rr(0, 2 * PI), dist = rr(150, 380);
            float bx = lisX + cosf(a) * dist, bz = lisZ + sinf(a) * dist;
            boltN = 14;
            float px = bx, pz = bz;
            for (int i = 0; i < boltN; i++) {
                float t = i / (float)(boltN - 1);
                boltP[i][0] = px; boltP[i][2] = pz; boltP[i][1] = mixf(190.0f, terrainH(bx, bz), t);
                px += rr(-6, 6); pz += rr(-6, 6);
            }
            boltLife = 0.35f; flash = 1.0f;
            float dx = bx - lisX, dz = bz - lisZ;
            float pan = clampf((dx * lisRX + dz * lisRZ) / dist, -1, 1) * 0.7f;
            queueThunder(dist / 340.0f, clampf(160.0f / dist, 0.3f, 1.0f), pan);
        }
    }
    if (boltLife > 0) { boltLife -= dt; flash = (fmodf(boltLife * 23.0f, 1.0f) < 0.6f) ? 1.0f : 0.35f; }
    else flash *= expf(-dt * 9.0f);

    // rain particles
    int active = (int)(NDROP * rainAmt);
    for (int i = 0; i < active; i++) {
        Drop& d = drops[i];
        d.y -= 15.0f * dt; d.x += windX * windAmt * 9.0f * dt; d.z += windZ * windAmt * 9.0f * dt;
        if (d.x - focX > 35) d.x -= 70;
        if (d.x - focX < -35) d.x += 70;
        if (d.z - focZ > 35) d.z -= 70;
        if (d.z - focZ < -35) d.z += 70;
        if (d.y < focY - 22 || d.y < std::max(waterLevel, terrainH(d.x, d.z))) respawnDrop(d, false);
        if (d.y > focY + 30) respawnDrop(d, true);
    }
    for (int i = 0; i < NRIP; i++) {
        Ripple& r = ripples[i];
        r.t += dt;
        if (r.t > 0.7f) { r.t = rr(-0.3f, 0.0f); r.x = lisX + rr(-24, 24); r.z = lisZ + rr(-24, 24); }
    }
}

// ============================================================================
//  Sky
// ============================================================================
static float starP[700][3], starPh[700];
struct Cloud { float x, y, z, s; };
static Cloud clouds[34];
static const float SUN_D[3] = { 0.45f, 0.62f, -0.55f };
static const float MOON_D[3] = { -0.40f, 0.60f, -0.50f };

static void skyColors(float* hor, float* zen) {
    const float dz[3] = { 0.22f, 0.46f, 0.86f }, dh[3] = { 0.72f, 0.84f, 0.96f };
    const float nz[3] = { 0.008f, 0.012f, 0.05f }, nh[3] = { 0.06f, 0.08f, 0.16f };
    const float sdz[3] = { 0.34f, 0.37f, 0.41f }, sdh[3] = { 0.55f, 0.58f, 0.60f };
    const float snz[3] = { 0.025f, 0.03f, 0.04f }, snh[3] = { 0.07f, 0.08f, 0.10f };
    float dusk = sinf(PI * night);
    for (int i = 0; i < 3; i++) {
        float zd = mixf(dz[i], sdz[i], storm), hd = mixf(dh[i], sdh[i], storm);
        float zn = mixf(nz[i], snz[i], storm), hn = mixf(nh[i], snh[i], storm);
        zen[i] = mixf(zd, zn, night); hor[i] = mixf(hd, hn, night);
    }
    hor[0] += 0.40f * dusk * (1 - storm); hor[1] += 0.15f * dusk * (1 - storm);
    for (int i = 0; i < 3; i++) {
        hor[i] = clamp01(hor[i] + flash * 0.45f * (i == 2 ? 1.1f : 0.9f));
        zen[i] = clamp01(zen[i] + flash * 0.30f);
    }
}
static void drawBody(const float* d, float rad, float r, float g, float b, float alpha, bool moon) {
    float L = sqrtf(d[0] * d[0] + d[1] * d[1] + d[2] * d[2]);
    float dx = d[0] / L, dy = d[1] / L, dz = d[2] / L;
    glPushMatrix(); glTranslatef(dx * 700, dy * 700, dz * 700);
    glBlendFunc(GL_SRC_ALPHA, GL_ONE);
    for (int i = 0; i < 10; i++) { float t = i / 9.0f; glColor4f(r, g, b, 0.025f * alpha * (0.4f + t)); glutSolidSphere(rad * (3.6f - 2.5f * t), 20, 14); }
    glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
    glColor4f(r, g, b, alpha); glutSolidSphere(rad, 24, 16);
    if (moon) {
        glRotatef(atan2f(dx, dz) / DEG, 0, 1, 0); glRotatef(-asinf(dy) / DEG, 1, 0, 0);
        static const float cr[5][3] = { {-0.3f, 0.25f, 0.2f}, {0.35f, 0.1f, 0.15f}, {0.05f, -0.35f, 0.25f}, {-0.45f, -0.2f, 0.12f}, {0.1f, 0.5f, 0.12f} };
        glColor4f(0.72f, 0.74f, 0.80f, alpha);
        for (int i = 0; i < 5; i++) {
            float cx = cr[i][0] * rad, cy = cr[i][1] * rad, cs = cr[i][2] * rad;
            float cz = -sqrtf(std::max(0.0f, rad * rad - cx * cx - cy * cy)) * 0.985f;
            glPushMatrix(); glTranslatef(cx, cy, cz); glScalef(1, 1, 0.25f); glutSolidSphere(cs, 10, 6); glPopMatrix();
        }
    }
    glPopMatrix();
}
static void drawSky(const float* hor, const float* zen) {
    glDisable(GL_LIGHTING); glDisable(GL_FOG); glDisable(GL_DEPTH_TEST); glDepthMask(GL_FALSE);
    glPushMatrix(); glTranslatef(eyeX, eyeY, eyeZ);
    const int SL = 14, SG = 36; const float R = 900;
    for (int i = 0; i < SL; i++) {
        float lat0 = -15 + i * 105.0f / SL, lat1 = -15 + (i + 1) * 105.0f / SL;
        glBegin(GL_QUAD_STRIP);
        for (int j = 0; j <= SG; j++) {
            float lon = j * 2 * PI / SG;
            for (int k = 0; k < 2; k++) {
                float lat = (k == 0 ? lat1 : lat0) * DEG;
                float t = powf(std::max(0.0f, sinf(lat)), 0.45f);
                glColor3f(mixf(hor[0], zen[0], t), mixf(hor[1], zen[1], t), mixf(hor[2], zen[2], t));
                glVertex3f(R * cosf(lat) * sinf(lon), R * sinf(lat), -R * cosf(lat) * cosf(lon));
            }
        }
        glEnd();
    }
    glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
    float clear = 1.0f - smooth01(storm * 1.15f);
    if (night > 0.03f && clear > 0.02f) {
        for (int pass = 0; pass < 2; pass++) {
            glPointSize(pass ? 2.6f : 1.5f);
            glBegin(GL_POINTS);
            for (int i = 0; i < 700; i++) {
                if ((i % 9 == 0) != (pass == 1)) continue;
                float tw = 0.65f + 0.35f * sinf(rt * (1.0f + (i % 5) * 0.4f) + starPh[i]);
                float a = night * clear * tw * clamp01(starP[i][1] / 150.0f + 0.1f);
                glColor4f(0.85f + 0.15f * (i % 3 == 0), 0.9f, 1.0f - 0.2f * (i % 4 == 0), a);
                glVertex3f(starP[i][0], starP[i][1], starP[i][2]);
            }
            glEnd();
        }
    }
    if (night > 0.03f) drawBody(MOON_D, 26, 0.96f, 0.96f, 0.88f, smooth01(night) * (0.15f + 0.85f * clear), true);
    if (night < 0.97f) drawBody(SUN_D, 30, 1.0f, 0.93f, 0.6f, smooth01(1 - night) * (0.1f + 0.9f * clear), false);
    glPopMatrix();
    // clouds (white fair-weather clouds -> dark cyclone clouds)
    glEnable(GL_DEPTH_TEST);
    int nc = 10 + (int)(storm * 24.0f);
    float cr = mixf(mixf(0.97f, 0.36f, storm), mixf(0.10f, 0.05f, storm), night) + flash * 0.5f;
    float cg = mixf(mixf(0.97f, 0.38f, storm), mixf(0.11f, 0.06f, storm), night) + flash * 0.5f;
    float cb = mixf(mixf(0.99f, 0.42f, storm), mixf(0.14f, 0.07f, storm), night) + flash * 0.6f;
    float ca = mixf(0.85f, 0.93f, storm) * (night > 0.5f ? 0.85f : 1.0f);
    static const float off[6][4] = { {0, 0, 0, 1.0f}, {1.2f, 0.2f, 0.3f, 0.8f}, {-1.3f, 0.1f, -0.2f, 0.85f},
                                     {0.4f, 0.4f, -0.5f, 0.7f}, {2.2f, -0.1f, 0.1f, 0.6f}, {-2.3f, -0.1f, 0.2f, 0.6f} };
    for (int c = 0; c < nc && c < 34; c++) {
        float cx = fmodf(clouds[c].x + rt * (2.0f + 10.0f * windAmt) + 2000.0f, 1400.0f) - 700.0f;
        float y = clouds[c].y - storm * 40.0f;
        for (int p = 0; p < 6; p++) {
            float sh = 0.9f + 0.1f * off[p][1] * 4;
            glColor4f(cr * sh, cg * sh, cb * sh, ca);
            glPushMatrix();
            glTranslatef(cx + off[p][0] * clouds[c].s, y + off[p][1] * clouds[c].s, clouds[c].z + off[p][2] * clouds[c].s);
            glScalef(1.0f, 0.42f, 0.7f); glutSolidSphere(clouds[c].s * off[p][3], 12, 8);
            glPopMatrix();
        }
    }
    glDisable(GL_BLEND); glDepthMask(GL_TRUE);
}

// ============================================================================
//  Dynamic drawing
// ============================================================================
static void drawDashed(float ax, float az, float bx, float bz) {
    float L = len2(bx - ax, bz - az), dx = (bx - ax) / L, dz = (bz - az) / L, px = -dz, pz = dx;
    float phase = fmodf(rt * 3.0f, 4.0f);
    for (float t = phase - 4.0f; t < L; t += 4.0f) {
        float t0 = std::max(0.0f, t), t1 = std::min(L, t + 2.0f);
        if (t1 <= t0) continue;
        float x0 = ax + dx * t0, z0 = az + dz * t0, x1 = ax + dx * t1, z1 = az + dz * t1;
        float h0 = std::max(terrainH(x0, z0), waterLevel) + 0.5f, h1 = std::max(terrainH(x1, z1), waterLevel) + 0.5f;
        bool wet = terrainH((x0 + x1) / 2, (z0 + z1) / 2) + 0.1f < waterLevel;
        if (wet) glColor4f(0.95f, 0.15f, 0.1f, 0.85f); else glColor4f(0.1f, 0.95f, 0.3f, 0.85f);
        float c = 0.4f;
        glBegin(GL_QUADS);
        glVertex3f(x0 + px * c, h0, z0 + pz * c); glVertex3f(x1 + px * c, h1, z1 + pz * c);
        glVertex3f(x1 - px * c, h1, z1 - pz * c); glVertex3f(x0 - px * c, h0, z0 - pz * c);
        glEnd();
    }
}
static void drawBarrier(const Road& R, float t) {
    float x, z; roadPoint(R, t, x, z);
    float dx = (R.x2 - R.x1) / R.len, dz = (R.z2 - R.z1) / R.len;
    float y = terrainH(x, z) + 0.12f;
    glPushMatrix();
    glTranslatef(x, y, z);
    glRotatef(atan2f(dx, dz) / DEG, 0, 1, 0);
    boxB(0, 0.6f, 0, R.w, 0.5f, 0.15f, 0.9f, 0.1f, 0.1f);
    for (int k = -2; k <= 2; k++) boxB(k * R.w * 0.18f, 0.6f, 0.02f, R.w * 0.09f, 0.5f, 0.17f, 1, 1, 1);
    boxB(-R.w / 2 + 0.2f, 0, 0, 0.15f, 0.8f, 0.15f, 0.3f, 0.3f, 0.3f);
    boxB(R.w / 2 - 0.2f, 0, 0, 0.15f, 0.8f, 0.15f, 0.3f, 0.3f, 0.3f);
    if (night > 0.2f && fmodf(rt * 1.5f, 1.0f) < 0.5f) addGlow(0, 1.2f, 0, 1.0f, 0.5f, 0.1f, 0.15f, night);
    glPopMatrix();
}
static void drawShelterDynamic() {
    float roofY = shelterFloorY(4);
    glPushMatrix(); glTranslatef(SHX, roofY + 1.2f, SHZ + 0.22f);
    signText("CYCLONE SHELTER", 11.5f, 1.3f, 1.0f, 1.0f, 1.0f);
    glPopMatrix();
    // generator powered lights on every floor (always on at night)
    if (night > 0.05f) {
        glDisable(GL_LIGHTING);
        for (int f = 0; f < 4; f++)
            for (int k = 0; k < 6; k++) {
                float x = SHX - 11 + k * 4.4f, y = shelterFloorY(f) + 2.9f, z = SHZ + SH_D / 2 - 0.4f;
                glColor3f(0.95f * night + 0.05f, 0.95f * night + 0.05f, 0.85f * night + 0.05f);
                boxC(x, y, z, 0.6f, 0.1f, 0.2f);
                addGlow(x, y, z + 0.2f, 0.95f, 0.95f, 0.85f, 0.35f, night);
            }
        glEnable(GL_LIGHTING);
    }
    // danger signal flags (one per flood stage)
    int st = stageNo();
    float fx = SHX - SH_W / 2 - 3.0f, fz = SHZ + SH_D / 2 + 2.0f, top = PAD + 12.6f;
    glColor3f(0.9f, 0.1f, 0.1f);
    glDisable(GL_CULL_FACE);
    for (int i = 0; i < st; i++) {
        float y = top - i * 1.6f, wv = sinf(rt * (3.0f + 4.0f * windAmt) + i) * 0.5f * (0.3f + windAmt);
        glBegin(GL_TRIANGLES); glNormal3f(0, 0, 1);
        glVertex3f(fx, y, fz); glVertex3f(fx, y - 1.2f, fz); glVertex3f(fx + 2.0f, y - 0.6f, fz + wv);
        glEnd();
    }
}
static void drawLampLights() {
    if (night < 0.05f || !powerOn) return;
    glDisable(GL_LIGHTING);
    glColor3f(1.0f, 0.88f, 0.55f);
    for (size_t i = 0; i < lamps.size(); i++) {
        const Lamp& L = lamps[i];
        if (L.y < waterLevel) continue;
        boxC(L.x, L.y - 0.05f, L.z, 0.6f, 0.08f, 0.6f);
        addGlow(L.x, L.y - 0.2f, L.z, 1.0f, 0.82f, 0.5f, 0.5f, night);
    }
    glEnable(GL_LIGHTING);
}
static void drawWindowLights() {
    if (night < 0.05f) return;
    glDisable(GL_LIGHTING);
    glBegin(GL_QUADS);
    for (size_t i = 0; i < winLights.size(); i++) {
        const WinL& w = winLights[i];
        if (w.y - w.hh < waterLevel + 0.05f) continue;
        float r, g, b, k;
        if (powerOn) { if (w.seed > 0.72f) continue; r = 1.0f; g = 0.82f; b = 0.50f; k = night * (0.7f + 0.3f * w.seed); }
        else {
            if (w.seed > 0.12f) continue;                         // a few candles / lanterns
            float fl = 0.7f + 0.3f * sinf(rt * 9.0f + w.seed * 50.0f) * sinf(rt * 5.3f + w.seed * 20.0f);
            r = 1.0f; g = 0.55f; b = 0.2f; k = night * 0.6f * fl;
        }
        glColor3f(r * k, g * k, b * k);
        glVertex3f(w.x - w.ax, w.y - w.hh, w.z - w.az); glVertex3f(w.x + w.ax, w.y - w.hh, w.z + w.az);
        glVertex3f(w.x + w.ax, w.y + w.hh, w.z + w.az); glVertex3f(w.x - w.ax, w.y + w.hh, w.z - w.az);
    }
    glEnd();
    glEnable(GL_LIGHTING);
}

static void drawPeople() {
    for (size_t i = 0; i < people.size(); i++) {
        const Person& p = people[i];
        if (p.state == P_SAFE || p.state == P_IN_BOAT) continue;
        float ground = terrainH(p.x, p.z), dep = waterLevel - ground;
        float y = p.onRoof ? p.y : (dep > 1.25f ? waterLevel - 1.25f + 0.05f * sinf(rt * 2 + p.ph) : ground);
        float sc = p.child ? 0.65f : 1.0f;
        int arms = 0; float swing = 0;
        if (p.state == P_STRANDED) arms = 1;
        else if (p.state == P_WALK || p.state == P_TO_BOAT) {
            swing = sinf(p.anim * 3.2f) * (dep > 0.5f ? 0.45f : 1.0f);
            if (dep > 0.5f) arms = 3;
        } else swing = 0.0f;
        float yaw = p.yaw;
        if (p.state == P_STRANDED) yaw = p.yaw + 25.0f * sinf(rt * 0.7f + p.ph);
        drawHuman(p.x, y, p.z, yaw, swing, arms, rt + p.ph, p.sh, p.pa, p.ha, p.sk, sc, p.state == P_TO_BOAT && p.rescued);
    }
    int n = std::min(sheltered, (int)spots.size());
    for (int i = 0; i < n; i++) {
        const Spot& s = spots[i];
        drawHuman(s.x, s.y, s.z, s.yaw, 0.05f * sinf(rt + s.ph), 0, 0, s.sh, s.pa, s.ha, s.sk, s.child ? 0.65f : 1.0f, false);
    }
}

static void drawDynamic() {
    float sway0 = windAmt * windAmt;
    for (size_t i = 0; i < trees.size(); i++) {
        const Tree& T = trees[i];
        float sw = sway0 * (7.0f + 5.0f * sinf(rt * (1.6f + windAmt) + T.ph)) * (T.kind == 1 ? 0.6f : 1.0f);
        drawTree(T, sw);
    }
    for (size_t i = 0; i < cars.size(); i++) drawCar(cars[i]);
    drawPeople();
    for (int i = 0; i < NBOAT; i++) drawBoatModel(i);
    for (size_t i = 0; i < roads.size(); i++) {
        const Road& R = roads[i];
        int n2 = (int)(R.len / 2.0f), first = -1, last = -1;
        for (int s = 0; s <= n2; s++) {
            float x, z; roadPoint(R, s * 2.0f, x, z);
            if (terrainH(x, z) + 0.1f < waterLevel) { if (first < 0) first = s; last = s; }
        }
        if (first >= 0) {
            if (first > 0) drawBarrier(R, (first - 1) * 2.0f);
            if (last < n2) drawBarrier(R, (last + 1) * 2.0f);
        }
    }
    drawShelterDynamic();
    drawLampLights();
    drawWindowLights();
}

// ----------------------------------------------------------------------------
//  Water (animated waves, depth-based transparency, shore foam, specular)
// ----------------------------------------------------------------------------
static void waterVert(float x, float z, float amp, const float* wc, bool depthA) {
    float t = rt;
    float a1 = x * 0.31f + t * 1.5f, a2 = z * 0.27f - t * 1.1f, a3 = (x + z) * 0.55f + t * 2.2f;
    float y = waterLevel + amp * (sinf(a1) + 0.7f * sinf(a2) + 0.35f * sinf(a3));
    float gx = amp * (0.31f * cosf(a1) + 0.35f * 0.55f * cosf(a3)), gz = amp * (0.7f * 0.27f * cosf(a2) + 0.35f * 0.55f * cosf(a3));
    float alpha = 0.84f, fo = 0.0f;
    if (depthA) {
        float dep = waterLevel - terrainH(x, z);
        alpha = clampf(0.30f + dep * 0.45f, 0.30f, 0.88f);
        fo = clamp01(1.0f - dep / 0.25f) * 0.45f;
    }
    glColor4f(mixf(wc[0], 0.85f, fo), mixf(wc[1], 0.85f, fo), mixf(wc[2], 0.82f, fo), alpha);
    glNormal3f(-gx * 3.0f, 1.0f, -gz * 3.0f);
    glVertex3f(x, y, z);
}
static void drawWater() {
    glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
    glDepthMask(GL_FALSE);
    GLfloat spec[4] = { 0.55f, 0.55f, 0.5f, 1 }, nospec[4] = { 0, 0, 0, 1 };
    glMaterialfv(GL_FRONT_AND_BACK, GL_SPECULAR, spec); glMaterialf(GL_FRONT_AND_BACK, GL_SHININESS, 48);
    float ff = clamp01((waterLevel - WATER_START) / 1.6f);
    float wc[3] = { mixf(0.10f, 0.36f, ff), mixf(0.30f, 0.30f, ff), mixf(0.34f, 0.19f, ff) };   // clear river -> muddy flood
    float amp = 0.025f + 0.10f * windAmt;
    const float st = 4.0f;
    int n = (int)(2 * WORLD / st);
    for (int i = 0; i < n; i++) {
        float x0 = -WORLD + i * st, x1 = x0 + st;
        glBegin(GL_TRIANGLE_STRIP);
        for (int j = 0; j <= n; j++) { float z = -WORLD + j * st; waterVert(x1, z, amp, wc, true); waterVert(x0, z, amp, wc, true); }
        glEnd();
    }
    glBegin(GL_QUADS);
    const float big = 40.0f, ext = 800.0f;
    for (float x = -ext; x < ext; x += big)
        for (float z = -ext; z < ext; z += big) {
            if (x >= -WORLD && x + big <= WORLD && z >= -WORLD && z + big <= WORLD) continue;
            waterVert(x, z, amp * 0.6f, wc, false); waterVert(x, z + big, amp * 0.6f, wc, false);
            waterVert(x + big, z + big, amp * 0.6f, wc, false); waterVert(x + big, z, amp * 0.6f, wc, false);
        }
    glEnd();
    glMaterialfv(GL_FRONT_AND_BACK, GL_SPECULAR, nospec);
    glDepthMask(GL_TRUE);
    glDisable(GL_BLEND);
}
static void drawWakesAndRipples() {
    glDisable(GL_LIGHTING);
    glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
    glDepthMask(GL_FALSE);
    float lum = mixf(0.92f, 0.35f, night);
    glBegin(GL_QUADS);
    for (size_t i = 0; i < wakes.size(); i++) {
        const Wake& w = wakes[i];
        float a = (1.0f - w.age / 3.2f) * 0.5f, s = w.s, y = waterLevel + 0.06f;
        glColor4f(lum, lum, lum * 0.98f, a);
        glVertex3f(w.x - s, y, w.z - s); glVertex3f(w.x + s, y, w.z - s);
        glVertex3f(w.x + s, y, w.z + s); glVertex3f(w.x - s, y, w.z + s);
    }
    glEnd();
    if (rainAmt > 0.05f) {
        for (int i = 0; i < NRIP; i++) {
            const Ripple& r = ripples[i];
            if (r.t < 0 || depthAt(r.x, r.z) < 0.05f) continue;
            float rad = 0.08f + r.t * 1.1f, a = (1.0f - r.t / 0.7f) * 0.35f * rainAmt;
            glColor4f(lum, lum, lum, a);
            glBegin(GL_LINE_LOOP);
            for (int k = 0; k < 12; k++) glVertex3f(r.x + rad * cosf(k * PI / 6), waterLevel + 0.07f, r.z + rad * sinf(k * PI / 6));
            glEnd();
        }
    }
    glDepthMask(GL_TRUE); glDisable(GL_BLEND); glEnable(GL_LIGHTING);
}
// boat search-lights at night (additive light cones and a pool of light on the water)
static void drawSearchlights() {
    if (night < 0.25f) return;
    glDisable(GL_LIGHTING); glDisable(GL_FOG);
    glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA, GL_ONE); glDepthMask(GL_FALSE);
    float k = (night - 0.25f) / 0.75f;
    for (int id = 0; id < NBOAT; id++) {
        const Boat& b = boats[id];
        float sweep = (b.state == B_WAIT || b.state == B_GO) ? sinf(rt * 0.6f + id) * 0.6f : sinf(rt * 0.3f + id) * 0.2f;
        float ox, oz; boatLocalToWorld(b, 0, -1.6f, ox, oz);
        float oy = waterLevel + 2.2f;
        float ang = b.head + sweep;
        float tx = b.x + sinf(ang) * 16.0f, tz = b.z + cosf(ang) * 16.0f, ty = waterLevel + 0.1f;
        float dx = tx - ox, dy = ty - oy, dz = tz - oz, L = sqrtf(dx * dx + dy * dy + dz * dz);
        dx /= L; dy /= L; dz /= L;
        float ux = -dz, uz = dx, ul = len2(ux, uz); ux /= ul; uz /= ul;    // horizontal side vector
        float vx = dy * uz, vy = dz * ux - dx * uz, vz = -dy * ux;          // third axis
        glBegin(GL_TRIANGLE_FAN);
        glColor4f(1.0f, 0.95f, 0.8f, 0.22f * k); glVertex3f(ox, oy, oz);
        for (int s = 0; s <= 16; s++) {
            float a = s * 2 * PI / 16, cr = 2.8f * cosf(a), sr = 2.8f * sinf(a);
            glColor4f(1.0f, 0.95f, 0.8f, 0.0f);
            glVertex3f(tx + ux * cr + vx * sr, ty + vy * sr, tz + uz * cr + vz * sr);
        }
        glEnd();
        glBegin(GL_TRIANGLE_FAN);
        glColor4f(1.0f, 0.95f, 0.8f, 0.28f * k); glVertex3f(tx, ty + 0.02f, tz);
        for (int s = 0; s <= 20; s++) {
            float a = s * 2 * PI / 20;
            glColor4f(1.0f, 0.95f, 0.8f, 0.0f);
            glVertex3f(tx + 4.0f * cosf(a), ty + 0.02f, tz + 4.0f * sinf(a));
        }
        glEnd();
    }
    glDepthMask(GL_TRUE); glDisable(GL_BLEND); glEnable(GL_FOG); glEnable(GL_LIGHTING);
}
static void drawOverlays() {
    glDisable(GL_LIGHTING);
    glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
    if (viewMode == V_OVER || viewMode == V_TOP) {
        float pulse = 0.18f + 0.07f * sinf(rt * 2.5f);
        glColor4f(0.1f, 0.9f, 0.35f, pulse);
        glBegin(GL_TRIANGLE_FAN);
        glVertex3f(SHX, PAD + 0.12f, SHZ);
        for (int i = 0; i <= 40; i++) glVertex3f(SHX + 13.5f * cosf(i * PI / 20), PAD + 0.12f, SHZ + 13.5f * sinf(i * PI / 20));
        glEnd();
        glLineWidth(3.0f);
        glColor4f(0.1f, 1.0f, 0.4f, 0.9f);
        glBegin(GL_LINE_LOOP);
        for (int i = 0; i < 40; i++) glVertex3f(SHX + 13.5f * cosf(i * PI / 20), PAD + 0.14f, SHZ + 13.5f * sinf(i * PI / 20));
        glEnd();
        glLineWidth(1.0f);
        glPushMatrix();
        glTranslatef(SHX, PAD + 25.0f + sinf(rt * 3) * 0.8f, SHZ);
        glRotatef(90, 1, 0, 0);
        glColor4f(0.1f, 0.95f, 0.35f, 0.85f);
        glutSolidCone(2.2, 5.0, 4, 1);
        glPopMatrix();
    }
    if (started) {
        drawDashed(-88, 0, 40, 0); drawDashed(88, 0, 40, 0);
        drawDashed(-88, 25, 40, 25); drawDashed(88, 25, 40, 25);
        drawDashed(40, 0, 40, 40);
    }
    glDisable(GL_BLEND);
    glEnable(GL_LIGHTING);
}
static void drawRain() {
    if (rainAmt < 0.02f) return;
    int active = (int)(NDROP * rainAmt);
    glDisable(GL_LIGHTING);
    glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
    glDepthMask(GL_FALSE);
    float lum = mixf(0.78f, 0.35f, night) + flash * 0.5f;
    float a = (viewMode == V_PERSON || viewMode == V_BOAT) ? 0.32f : 0.22f;
    float sx = windX * windAmt * 9.0f * 0.05f, sz = windZ * windAmt * 9.0f * 0.05f, sy = 15.0f * 0.05f;
    glBegin(GL_LINES);
    for (int i = 0; i < active; i++) {
        const Drop& d = drops[i];
        glColor4f(lum, lum, lum * 1.05f, 0.0f); glVertex3f(d.x - sx, d.y + sy, d.z - sz);
        glColor4f(lum, lum, lum * 1.05f, a);    glVertex3f(d.x, d.y, d.z);
    }
    glEnd();
    glDepthMask(GL_TRUE); glDisable(GL_BLEND); glEnable(GL_LIGHTING);
}
static void drawBolt() {
    if (boltLife <= 0 || boltN < 2) return;
    glDisable(GL_LIGHTING); glDisable(GL_FOG);
    glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA, GL_ONE);
    for (int pass = 0; pass < 2; pass++) {
        glLineWidth(pass ? 2.0f : 6.0f);
        glColor4f(0.75f, 0.82f, 1.0f, pass ? 0.95f : 0.3f);
        glBegin(GL_LINE_STRIP);
        for (int i = 0; i < boltN; i++) glVertex3f(boltP[i][0], boltP[i][1], boltP[i][2]);
        glEnd();
    }
    glLineWidth(1.0f);
    glDisable(GL_BLEND); glEnable(GL_FOG); glEnable(GL_LIGHTING);
}

// ============================================================================
//  HUD (status panel, buttons, minimap, messages)
// ============================================================================
struct Btn { int x, y, w, h; const char* label; float r, g, b; };
static Btn btns[8] = {
    { 18, 50, 70, 26, "Start",  0.15f, 0.60f, 0.25f }, { 94, 50, 70, 26, "Pause",  0.85f, 0.55f, 0.10f },
    { 170, 50, 70, 26, "Resume", 0.15f, 0.45f, 0.80f }, { 246, 50, 70, 26, "Reset",  0.75f, 0.20f, 0.20f },
    { 18, 82, 70, 26, "Day/Night", 0.35f, 0.30f, 0.60f }, { 94, 82, 70, 26, "View", 0.20f, 0.50f, 0.55f },
    { 170, 82, 70, 26, "Sound", 0.45f, 0.45f, 0.48f }, { 246, 82, 70, 26, "Speed", 0.50f, 0.35f, 0.25f } };

static void rect2(float x, float y, float w, float h, float r, float g, float b, float a) {
    glColor4f(r, g, b, a);
    glBegin(GL_QUADS); glVertex2f(x, y); glVertex2f(x + w, y); glVertex2f(x + w, y + h); glVertex2f(x, y + h); glEnd();
}
static void frame2(float x, float y, float w, float h, float r, float g, float b, float a) {
    glColor4f(r, g, b, a);
    glBegin(GL_LINE_LOOP); glVertex2f(x, y); glVertex2f(x + w, y); glVertex2f(x + w, y + h); glVertex2f(x, y + h); glEnd();
}
static void hudText(float x, float y, const char* s, void* font = GLUT_BITMAP_HELVETICA_12) {
    glRasterPos2f(x, y);
    glutBitmapString(font, (const unsigned char*)s);
}
static void hudTextC(float cx, float y, const char* s, void* font) {
    int w = glutBitmapLength(font, (const unsigned char*)s);
    hudText(cx - w * 0.5f, y, s, font);
}
static const char* boatStatus(const Boat& b) {
    switch (b.state) {
    case B_GO: return "Going to stranded people";
    case B_WAIT: return "SIREN - people boarding";
    case B_RETURN: return "Taking people to shelter";
    case B_UNLOAD: return "Unloading at shelter";
    default: return b.load > 0 ? "Searching (with people)" : (started ? "Patrolling" : "Standby on the river");
    }
}
static void setView(int m);

static void drawMinimap() {
    float S = 210, x0 = winW - S - 14, y0 = winH - 24 - S - 14;
    rect2(x0 - 4, y0 - 20, S + 8, S + 24, 0.04f, 0.06f, 0.10f, 0.82f);
    frame2(x0 - 4, y0 - 20, S + 8, S + 24, 0.4f, 0.7f, 1.0f, 0.6f);
    glColor3f(0.85f, 0.92f, 1.0f); hudText(x0, y0 - 6, "MAP  (blue = flood water)");
    rect2(x0, y0, S, S, 0.18f, 0.30f, 0.16f, 1.0f);
    const int MG = 40; float cs = S / MG;
    for (int i = 0; i < MG; i++)
        for (int j = 0; j < MG; j++) {
            float wx = -WORLD + (i + 0.5f) * 200.0f / MG, wz = -WORLD + (j + 0.5f) * 200.0f / MG;
            float dep = waterLevel - terrainH(wx, wz);
            if (dep <= 0) continue;
            float a = clampf(0.35f + dep * 0.25f, 0.35f, 0.95f);
            rect2(x0 + i * cs, y0 + j * cs, cs + 0.5f, cs + 0.5f, 0.15f, 0.40f, 0.85f, a);
        }
    glLineWidth(2.0f);
    for (size_t i = 0; i < roads.size(); i++) {
        bool bl = waterLevel > roads[i].thr;
        if (bl) glColor4f(1.0f, 0.3f, 0.25f, 0.9f); else glColor4f(0.85f, 0.85f, 0.85f, 0.9f);
        glBegin(GL_LINES);
        glVertex2f(x0 + (roads[i].x1 + WORLD) / 200 * S, y0 + (roads[i].z1 + WORLD) / 200 * S);
        glVertex2f(x0 + (roads[i].x2 + WORLD) / 200 * S, y0 + (roads[i].z2 + WORLD) / 200 * S);
        glEnd();
    }
    glLineWidth(1.0f);
    float sx = x0 + (SHX + WORLD) / 200 * S, sz = y0 + (SHZ + WORLD) / 200 * S;
    rect2(sx - 7, sz - 4, 14, 8, 0.2f, 1.0f, 0.4f, 1.0f);
    glPointSize(3.0f);
    glBegin(GL_POINTS);
    for (size_t i = 0; i < people.size(); i++) {
        const Person& p = people[i];
        if (p.state == P_STRANDED || p.state == P_TO_BOAT) glColor3f(1.0f, 0.2f, 0.2f);
        else if (p.state == P_WALK) glColor3f(1.0f, 0.9f, 0.2f);
        else continue;
        glVertex2f(x0 + (p.x + WORLD) / 200 * S, y0 + (p.z + WORLD) / 200 * S);
    }
    glEnd();
    for (int i = 0; i < NBOAT; i++) {
        const Boat& b = boats[i];
        float bx = x0 + (b.x + WORLD) / 200 * S, bz = y0 + (b.z + WORLD) / 200 * S;
        float fx = sinf(b.head), fz = cosf(b.head);
        if (b.siren && fmodf(rt * 3, 1) < 0.5f) glColor3f(1.0f, 0.3f, 0.3f); else glColor3f(1.0f, 0.6f, 0.15f);
        glBegin(GL_TRIANGLES);
        glVertex2f(bx + fx * 6, bz + fz * 6); glVertex2f(bx - fz * 3.5f - fx * 3, bz + fx * 3.5f - fz * 3); glVertex2f(bx + fz * 3.5f - fx * 3, bz - fx * 3.5f - fz * 3);
        glEnd();
    }
    float cx = x0 + (lisX + WORLD) / 200 * S, cz = y0 + (lisZ + WORLD) / 200 * S;
    if (cx > x0 && cx < x0 + S && cz > y0 && cz < y0 + S) {
        glColor3f(1, 1, 1);
        glBegin(GL_LINE_LOOP); for (int k = 0; k < 12; k++) glVertex2f(cx + 4 * cosf(k * PI / 6), cz + 4 * sinf(k * PI / 6)); glEnd();
        glBegin(GL_LINES); glVertex2f(cx, cz); glVertex2f(cx + fwdX * 12, cz + fwdZ * 12); glEnd();
    }
    frame2(x0, y0, S, S, 0.7f, 0.8f, 0.9f, 0.8f);
}

static void drawHUD() {
    glMatrixMode(GL_PROJECTION); glPushMatrix(); glLoadIdentity(); gluOrtho2D(0, winW, winH, 0);
    glMatrixMode(GL_MODELVIEW);  glPushMatrix(); glLoadIdentity();
    glDisable(GL_LIGHTING); glDisable(GL_DEPTH_TEST); glDisable(GL_FOG);
    glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
    char buf[200];
    static const char* stageNames[5] = { "Stage 0 - Normal", "Stage 1 - Rising", "Stage 2 - Warning", "Stage 3 - Danger", "Stage 4 - Severe" };
    static const char* signals[5] = { "-", "Signal 3", "Signal 7", "Signal 9", "Signal 10" };
    float sr[5] = { 0.3f, 0.9f, 1.0f, 1.0f, 0.95f }, sg[5] = { 0.9f, 0.9f, 0.7f, 0.45f, 0.15f }, sb[5] = { 0.4f, 0.3f, 0.2f, 0.15f, 0.15f };
    int st = stageNo();
    int evac = 0, wait = 0, strand = 0, inBoat = 0;
    for (size_t i = 0; i < people.size(); i++) {
        int s = people[i].state;
        if (s == P_WALK) evac++; else if (s == P_HOME) wait++;
        else if (s == P_STRANDED || s == P_TO_BOAT) strand++; else if (s == P_IN_BOAT) inBoat++;
    }
    const char* state = !started ? "READY (press Start)" : (running ? (waterLevel >= WATER_MAX ? "PEAK FLOOD" : "RUNNING") : "PAUSED");

    if (showHUD) {
        float PH = 560;
        rect2(10, 10, 316, PH, 0.04f, 0.06f, 0.11f, 0.80f);
        rect2(10, 10, 316, 30, 0.10f, 0.35f, 0.65f, 0.95f);
        frame2(10, 10, 316, PH, 0.4f, 0.7f, 1.0f, 0.5f);
        glColor3f(1, 1, 1);
        hudText(20, 30, "FLOOD ESCAPE & CYCLONE SHELTER RESCUE", GLUT_BITMAP_HELVETICA_12);
        for (int i = 0; i < 8; i++) {
            const Btn& B = btns[i];
            rect2((float)B.x, (float)B.y, (float)B.w, (float)B.h, B.r, B.g, B.b, 1.0f);
            frame2((float)B.x, (float)B.y, (float)B.w, (float)B.h, 1, 1, 1, 0.35f);
            const char* lb = B.label;
            if (i == 4) lb = nightMode ? "Day" : "Night";
            if (i == 6) lb = soundOn ? "Sound ON" : "Sound OFF";
            if (i == 7) { snprintf(buf, sizeof buf, "Speed x%d", speedMul); lb = buf; }
            glColor3f(1, 1, 1);
            hudTextC(B.x + B.w * 0.5f, (float)B.y + 17, lb, GLUT_BITMAP_HELVETICA_12);
        }
        float y = 130;
        glColor3f(0.9f, 0.95f, 1);
        snprintf(buf, sizeof buf, "Status : %s", state); hudText(20, y, buf); y += 17;
        snprintf(buf, sizeof buf, "View   : %s", VIEW_NAMES[viewMode]); hudText(20, y, buf); y += 17;
        glColor3f(sr[st], sg[st], sb[st]);
        snprintf(buf, sizeof buf, "Flood stage : %s  (%s)", stageNames[st], signals[st]); hudText(20, y, buf); y += 17;
        glColor3f(0.9f, 0.95f, 1);
        snprintf(buf, sizeof buf, "Water level : %.2f m", waterLevel); hudText(20, y, buf); y += 7;
        float frac = clamp01((waterLevel - WATER_START) / (WATER_MAX - WATER_START));
        rect2(20, y, 296, 9, 0.2f, 0.2f, 0.25f, 1); rect2(20, y, 296 * frac, 9, sr[st], sg[st], sb[st], 1); y += 24;
        const char* rainTxt = rainAmt < 0.05f ? "No rain" : (rainAmt < 0.4f ? "Light rain" : (rainAmt < 0.75f ? "Heavy rain" : "Cyclone storm"));
        snprintf(buf, sizeof buf, "Weather : %s, wind %d km/h, %s", rainTxt, (int)(10 + windAmt * 110), night > 0.5f ? "night" : "day");
        hudText(20, y, buf); y += 17;
        if (powerOn) glColor3f(0.5f, 1.0f, 0.6f); else glColor3f(1.0f, 0.45f, 0.35f);
        hudText(20, y, powerOn ? "Electricity : ON" : "Electricity : CUT OFF (safety)"); y += 22;

        int blocked = 0;
        for (size_t i = 0; i < roads.size(); i++) if (waterLevel > roads[i].thr) blocked++;
        glColor3f(1, 1, 1);
        snprintf(buf, sizeof buf, "Blocked roads : %d / %d", blocked, (int)roads.size()); hudText(20, y, buf); y += 16;
        for (size_t i = 0; i < roads.size(); i++) {
            bool bl = waterLevel > roads[i].thr;
            if (bl) glColor3f(1.0f, 0.4f, 0.35f); else glColor3f(0.45f, 1.0f, 0.55f);
            snprintf(buf, sizeof buf, "   %-14s %s", roads[i].name, bl ? "BLOCKED" : "OPEN"); hudText(20, y, buf); y += 14;
        }
        y += 8;
        glColor3f(1, 1, 1);
        snprintf(buf, sizeof buf, "Sheltered (safe)   : %d / %d", sheltered, (int)people.size()); hudText(20, y, buf); y += 15;
        snprintf(buf, sizeof buf, "Walking to shelter : %d", evac); hudText(20, y, buf); y += 15;
        snprintf(buf, sizeof buf, "At home            : %d", wait); hudText(20, y, buf); y += 15;
        if (strand) glColor3f(1.0f, 0.45f, 0.4f); else glColor3f(1, 1, 1);
        snprintf(buf, sizeof buf, "Stranded (need help): %d", strand); hudText(20, y, buf); y += 15;
        glColor3f(1, 1, 1);
        snprintf(buf, sizeof buf, "In rescue boats     : %d   rescued by boat: %d", inBoat, boatRescued); hudText(20, y, buf); y += 20;
        glColor3f(1.0f, 0.75f, 0.35f);
        hudText(20, y, "RESCUE BOATS"); y += 15;
        for (int i = 0; i < NBOAT; i++) {
            const Boat& b = boats[i];
            if (b.siren) glColor3f(1.0f, 0.5f, 0.45f); else glColor3f(0.85f, 0.9f, 1.0f);
            snprintf(buf, sizeof buf, " Boat %d [%d/%d] %s", i + 1, b.load, BOAT_CAP, boatStatus(b)); hudText(20, y, buf); y += 14;
        }
    } else {
        rect2(10, 10, 430, 24, 0.04f, 0.06f, 0.11f, 0.75f);
        glColor3f(0.9f, 0.95f, 1);
        snprintf(buf, sizeof buf, "%s | %s | water %.2f m | safe %d/%d   (H = panel)", state, VIEW_NAMES[viewMode], waterLevel, sheltered, (int)people.size());
        hudText(18, 27, buf);
    }

    // message banner
    if (hudMsgT > 0) {
        float a = clamp01(hudMsgT);
        int w = glutBitmapLength(GLUT_BITMAP_HELVETICA_18, (const unsigned char*)hudMsg);
        float cx = winW * 0.5f + (showHUD ? 160.0f : 0.0f);
        rect2(cx - w * 0.5f - 14, 14, w + 28, 32, 0.05f, 0.07f, 0.12f, 0.75f * a);
        glColor4f(1.0f, 0.9f, 0.45f, a);
        hudTextC(cx, 36, hudMsg, GLUT_BITMAP_HELVETICA_18);
    }

    // view specific info
    if (viewMode == V_PERSON) {
        glColor4f(1, 1, 1, 0.8f);
        glBegin(GL_LINES);
        glVertex2f(winW * 0.5f - 8, winH * 0.5f); glVertex2f(winW * 0.5f + 8, winH * 0.5f);
        glVertex2f(winW * 0.5f, winH * 0.5f - 8); glVertex2f(winW * 0.5f, winH * 0.5f + 8);
        glEnd();
        float dep = depthAt(pX, pZ);
        if (pLift > 0.5f) snprintf(buf, sizeof buf, "Looking from %.0f m above the ground", pLift);
        else if (dep <= 0.05f) snprintf(buf, sizeof buf, "On dry ground");
        else if (dep < 0.6f) snprintf(buf, sizeof buf, "Wading - water %.1f m deep", dep);
        else if (dep < 1.25f) snprintf(buf, sizeof buf, "DANGER - water %.1f m deep, hard to walk", dep);
        else snprintf(buf, sizeof buf, "SWIMMING - water %.1f m deep! Find a boat or high ground", dep);
        float w = (float)glutBitmapLength(GLUT_BITMAP_HELVETICA_18, (const unsigned char*)buf);
        rect2(winW * 0.5f - w * 0.5f - 12, winH - 78, w + 24, 30, 0.05f, 0.07f, 0.12f, 0.7f);
        if (dep > 0.6f && pLift < 0.5f) glColor3f(1.0f, 0.5f, 0.4f); else glColor3f(0.8f, 1.0f, 0.85f);
        hudTextC(winW * 0.5f, winH - 57, buf, GLUT_BITMAP_HELVETICA_18);
    } else if (viewMode == V_BOAT) {
        const Boat& b = boats[boatCam];
        snprintf(buf, sizeof buf, "On board Rescue Boat %d  -  %s  (%d/%d people)   B = next boat", boatCam + 1, boatStatus(b), b.load, BOAT_CAP);
        float w = (float)glutBitmapLength(GLUT_BITMAP_HELVETICA_18, (const unsigned char*)buf);
        rect2(winW * 0.5f - w * 0.5f - 12, winH - 78, w + 24, 30, 0.05f, 0.07f, 0.12f, 0.7f);
        glColor3f(1.0f, 0.8f, 0.45f);
        hudTextC(winW * 0.5f, winH - 57, buf, GLUT_BITMAP_HELVETICA_18);
    }
    if (started && !running) {
        glColor3f(1, 0.85f, 0.3f);
        hudTextC(winW * 0.5f, winH * 0.5f - 60, "|| PAUSED  (SPACE / P to resume)", GLUT_BITMAP_HELVETICA_18);
    }

    drawMinimap();

    rect2(0, (float)winH - 24, (float)winW, 24, 0.04f, 0.06f, 0.11f, 0.85f);
    glColor3f(0.9f, 0.95f, 1);
    const char* help =
        viewMode == V_PERSON ? "PERSON: W A S D walk (SHIFT run) | mouse drag / arrows look | Q E down/up | 1-4 view | N day/night | SPACE pause | R reset | M sound | F speed | F11 full" :
        viewMode == V_BOAT   ? "BOAT: mouse drag / arrows look around | B next boat | 1-4 view | N day/night | SPACE pause | R reset | M sound | F speed | H panel | F11 full" :
        viewMode == V_TOP    ? "TOP: W A S D / R-drag move | L-drag / arrows rotate | wheel, Q E zoom | 1-4 view | N day/night | ENTER start | SPACE pause | R reset | M sound" :
                               "OVERVIEW: L-drag / arrows rotate | W A S D / R-drag move | wheel, Q E zoom | 1-4 view | N day/night | ENTER start | SPACE pause | R reset | M sound";
    hudText(10, (float)winH - 8, help);

    glEnable(GL_DEPTH_TEST); glEnable(GL_LIGHTING); glDisable(GL_BLEND);
    glMatrixMode(GL_PROJECTION); glPopMatrix();
    glMatrixMode(GL_MODELVIEW);  glPopMatrix();
}

// ============================================================================
//  Camera
// ============================================================================
static void setupCamera() {
    float tx, ty, tz, ux = 0, uy = 1, uz = 0, nearP = 1.0f;
    switch (viewMode) {
    case V_PERSON: {
        float ground = terrainH(pX, pZ);
        eyeX = pX; eyeZ = pZ; eyeY = std::max(ground, waterLevel - 1.25f) + 1.65f + pLift;
        float py = pYaw * DEG, pp = pPitch * DEG;
        fwdX = cosf(pp) * sinf(py); fwdY = sinf(pp); fwdZ = -cosf(pp) * cosf(py);
        tx = eyeX + fwdX; ty = eyeY + fwdY; tz = eyeZ + fwdZ;
        fovDeg = 62; nearP = 0.25f;
        lisX = eyeX; lisY = eyeY; lisZ = eyeZ;
        float fl = len2(fwdX, fwdZ); lisRX = -fwdZ / fl; lisRZ = fwdX / fl;
    } break;
    case V_BOAT: {
        const Boat& b = boats[boatCam];
        float lx, lz; boatLocalToWorld(b, 0.55f, -2.25f, lx, lz);
        eyeX = lx; eyeZ = lz; eyeY = waterLevel + 0.12f + 1.55f + 0.07f * sinf(rt * 1.9f + boatCam * 1.3f);
        float a = b.head + bLookYaw * DEG, pp = bLookPitch * DEG;
        fwdX = cosf(pp) * sinf(a); fwdY = sinf(pp); fwdZ = cosf(pp) * cosf(a);
        tx = eyeX + fwdX; ty = eyeY + fwdY; tz = eyeZ + fwdZ;
        float rl = (b.roll + 2.5f * windAmt * sinf(rt * 1.3f + boatCam)) * DEG * 0.6f;
        ux = -sinf(rl) * cosf(a); uy = cosf(rl); uz = sinf(rl) * sinf(a);   // tilt the horizon with the boat roll
        fovDeg = 62; nearP = 0.25f;
        lisX = eyeX; lisY = eyeY; lisZ = eyeZ; lisRX = -fwdZ; lisRZ = fwdX;
        { float l = len2(lisRX, lisRZ); lisRX /= l; lisRZ /= l; }
    } break;
    case V_TOP: {
        float yr = camYaw * DEG;
        eyeX = tgx; eyeY = topH; eyeZ = tgz;
        tx = tgx; ty = 0; tz = tgz;
        ux = -sinf(yr); uy = 0; uz = -cosf(yr);
        fwdX = ux; fwdY = 0; fwdZ = uz;
        fovDeg = 45; nearP = 2.0f;
        lisX = tgx; lisY = std::max(terrainH(tgx, tgz), waterLevel); lisZ = tgz; lisRX = cosf(yr); lisRZ = -sinf(yr);
    } break;
    default: {
        float yr = camYaw * DEG, pr = camPitch * DEG;
        eyeX = tgx + camDist * cosf(pr) * sinf(yr); eyeY = tgy + camDist * sinf(pr); eyeZ = tgz + camDist * cosf(pr) * cosf(yr);
        float minY = std::max(terrainH(eyeX, eyeZ), waterLevel) + 2.0f;
        if (eyeY < minY) eyeY = minY;
        tx = tgx; ty = tgy; tz = tgz;
        fwdX = -sinf(yr); fwdY = 0; fwdZ = -cosf(yr);
        fovDeg = 45; nearP = 1.0f;
        lisX = tgx; lisY = std::max(terrainH(tgx, tgz), waterLevel); lisZ = tgz; lisRX = cosf(yr); lisRZ = -sinf(yr);
    } break;
    }
    glMatrixMode(GL_PROJECTION); glLoadIdentity();
    gluPerspective(fovDeg, (double)winW / winH, nearP, 2500.0);
    glMatrixMode(GL_MODELVIEW); glLoadIdentity();
    gluLookAt(eyeX, eyeY, eyeZ, tx, ty, tz, ux, uy, uz);
    // rain volume sits a little in front of the camera
    float fl = std::max(0.2f, len2(fwdX, fwdZ));
    focX = eyeX + fwdX / fl * 18.0f; focZ = eyeZ + fwdZ / fl * 18.0f;
    focY = (viewMode == V_OVER || viewMode == V_TOP) ? std::max(terrainH(tgx, tgz), waterLevel) + 15.0f : eyeY;
    if (viewMode == V_OVER || viewMode == V_TOP) { focX = tgx; focZ = tgz; }
}

static bool personSolid(float x, float z) {
    for (size_t i = 0; i < houses.size(); i++) {
        float hx, hz; houseHalf(houses[i], hx, hz);
        if (fabsf(x - houses[i].x) < hx + 0.3f && fabsf(z - houses[i].z) < hz + 0.3f) return true;
    }
    if (x > SHX - SH_W / 2 - 0.3f && x < SHX + SH_W / 2 + 5.0f && fabsf(z - SHZ) < SH_D / 2 + 0.3f) return true;
    return false;
}
static void panCam(float fwd, float right) {
    float yr = camYaw * DEG;
    tgx += -sinf(yr) * fwd + cosf(yr) * right;
    tgz += -cosf(yr) * fwd - sinf(yr) * right;
    tgx = clampf(tgx, -300, 300); tgz = clampf(tgz, -300, 300);
}
static void zoom(float f) {
    if (viewMode == V_TOP) topH = clampf(topH * f, 25.0f, 420.0f);
    else camDist = clampf(camDist * f, 12.0f, 420.0f);
}
static void moveCamera(float dt) {
    float fwd = 0, right = 0;
    if (keys['w']) fwd += 1;
    if (keys['s']) fwd -= 1;
    if (keys['d']) right += 1;
    if (keys['a']) right -= 1;
    switch (viewMode) {
    case V_OVER: case V_TOP: {
        float sp = (viewMode == V_TOP ? topH : camDist) * 0.6f * dt * (shiftHeld ? 2.5f : 1.0f);
        if (fwd != 0 || right != 0) panCam(fwd * sp, right * sp);
        if (sKeys[0]) camYaw += 60 * dt;
        if (sKeys[1]) camYaw -= 60 * dt;
        if (viewMode == V_OVER) {
            if (sKeys[2]) camPitch = clampf(camPitch + 40 * dt, 6, 88);
            if (sKeys[3]) camPitch = clampf(camPitch - 40 * dt, 6, 88);
        } else {
            if (sKeys[2]) panCam(topH * 0.6f * dt, 0);
            if (sKeys[3]) panCam(-topH * 0.6f * dt, 0);
        }
        if (keys['q']) zoom(1.0f + dt);
        if (keys['e']) zoom(1.0f - dt * 0.8f);
        tgy = std::max(terrainH(tgx, tgz), waterLevel) * 0.5f;
    } break;
    case V_PERSON: {
        if (sKeys[0]) pYaw -= 90 * dt;
        if (sKeys[1]) pYaw += 90 * dt;
        if (sKeys[2]) pPitch = clampf(pPitch + 60 * dt, -85, 85);
        if (sKeys[3]) pPitch = clampf(pPitch - 60 * dt, -85, 85);
        if (keys['e']) pLift = clampf(pLift + 6 * dt, 0, 45);
        if (keys['q']) pLift = clampf(pLift - 6 * dt, 0, 45);
        if (fwd == 0 && right == 0) break;
        float py = pYaw * DEG, fx = sinf(py), fz = -cosf(py), rx = cosf(py), rz = sinf(py);
        float mx = fwd * fx + right * rx, mz = fwd * fz + right * rz, ml = len2(mx, mz);
        mx /= ml; mz /= ml;
        float dep = depthAt(pX, pZ);
        float sp = (shiftHeld ? 8.5f : 4.2f) * (pLift > 3 ? 2.0f : (dep < 0.2f ? 1.0f : (dep < 1.25f ? 0.55f : 0.4f)));
        float nx = clampf(pX + mx * sp * dt, -500, 500), nz = clampf(pZ + mz * sp * dt, -500, 500);
        bool ghost = pLift > 3.0f;
        if (ghost || !personSolid(nx, pZ)) pX = nx;
        if (ghost || !personSolid(pX, nz)) pZ = nz;
    } break;
    case V_BOAT:
        if (sKeys[0]) bLookYaw -= 90 * dt;
        if (sKeys[1]) bLookYaw += 90 * dt;
        if (sKeys[2]) bLookPitch = clampf(bLookPitch + 60 * dt, -60, 60);
        if (sKeys[3]) bLookPitch = clampf(bLookPitch - 60 * dt, -60, 60);
        break;
    }
}
static void setView(int m) {
    if (m == viewMode) return;
    if (m == V_PERSON) {                       // drop the person where the camera was looking
        float x = (viewMode == V_BOAT) ? eyeX : tgx, z = (viewMode == V_BOAT) ? eyeZ : tgz;
        x = clampf(x, -95, 95); z = clampf(z, -95, 95);
        for (int k = 0; k < 60 && personSolid(x, z); k++) { x += 1.5f * cosf(k * 0.7f) * (1 + k * 0.2f); z += 1.5f * sinf(k * 0.7f) * (1 + k * 0.2f); }
        pX = x; pZ = z; pYaw = (viewMode == V_OVER || viewMode == V_TOP) ? -camYaw : pYaw; pPitch = -4; pLift = 0;
    } else if (m == V_OVER || m == V_TOP) {
        if (viewMode == V_PERSON) { tgx = pX; tgz = pZ; camYaw = -pYaw; }
        if (viewMode == V_BOAT) { tgx = boats[boatCam].x; tgz = boats[boatCam].z; }
    } else if (m == V_BOAT) { bLookYaw = 0; bLookPitch = -6; }
    viewMode = m;
    char b[120]; snprintf(b, sizeof b, "View: %s", VIEW_NAMES[m]); setMsg(b);
}

// ============================================================================
//  GLUT callbacks
// ============================================================================
static void display() {
    float hor[3], zen[3]; skyColors(hor, zen);
    glClearColor(hor[0], hor[1], hor[2], 1.0f);
    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
    setupCamera();
    drawSky(hor, zen);

    // lighting: sun by day, moon by night, darker under storm clouds, lightning flashes
    float L[3]; for (int i = 0; i < 3; i++) L[i] = mixf(SUN_D[i], MOON_D[i], night);
    float ln = sqrtf(L[0] * L[0] + L[1] * L[1] + L[2] * L[2]);
    GLfloat lp[4] = { L[0] / ln, L[1] / ln, L[2] / ln, 0 };
    float dk = mixf(1.0f - 0.5f * storm, 1.0f - 0.35f * storm, night);
    GLfloat dif[4] = { mixf(1.0f, 0.24f, night) * dk + flash * 0.9f, mixf(0.95f, 0.28f, night) * dk + flash * 0.9f, mixf(0.86f, 0.42f, night) * dk + flash, 1 };
    GLfloat amb[4] = { mixf(0.40f, 0.09f, night) * (1 - 0.25f * storm) + flash * 0.4f, mixf(0.42f, 0.11f, night) * (1 - 0.25f * storm) + flash * 0.4f,
                       mixf(0.48f, 0.17f, night) * (1 - 0.2f * storm) + flash * 0.5f, 1 };
    GLfloat spc[4] = { dif[0], dif[1], dif[2], 1 };
    glEnable(GL_LIGHTING); glEnable(GL_LIGHT0);
    glLightfv(GL_LIGHT0, GL_POSITION, lp); glLightfv(GL_LIGHT0, GL_DIFFUSE, dif); glLightfv(GL_LIGHT0, GL_AMBIENT, amb);
    glLightfv(GL_LIGHT0, GL_SPECULAR, spc);
    GLfloat gam[4] = { amb[0] * 0.5f, amb[1] * 0.5f, amb[2] * 0.5f, 1 };
    glLightModelfv(GL_LIGHT_MODEL_AMBIENT, gam);

    // fog / haze = horizon colour; heavy rain shortens the visibility
    glEnable(GL_FOG); glFogi(GL_FOG_MODE, GL_LINEAR);
    glFogf(GL_FOG_START, mixf(170.0f, 45.0f, storm) * (night > 0.5f ? 0.8f : 1.0f));
    glFogf(GL_FOG_END, mixf(820.0f, 330.0f, storm) * (night > 0.5f ? 0.85f : 1.0f));
    GLfloat fc[4] = { hor[0], hor[1], hor[2], 1 }; glFogfv(GL_FOG_COLOR, fc);

    glows.clear();
    glCallList(sceneList);
    drawDynamic();
    drawWater();
    drawWakesAndRipples();
    drawSearchlights();
    drawOverlays();
    drawRain();
    drawBolt();
    drawGlows();
    drawHUD();
    glutSwapBuffers();
}

static void reshape(int w, int h) {
    winW = std::max(w, 1); winH = std::max(h, 1);
    glViewport(0, 0, winW, winH);
}

static void idle() {
    int now = glutGet(GLUT_ELAPSED_TIME);
    float dt = (now - lastT) / 1000.0f; lastT = now;
    if (dt > 0.05f) dt = 0.05f;
    if (dt < 0) dt = 0;
    rt = now / 1000.0f;
    weatherUpdate(dt);
    moveCamera(dt);
    if (running) for (int k = 0; k < speedMul; k++) update(dt);
    computeAudioTargets();
    pumpAudio();
    glutPostRedisplay();
}

static void quitApp() { closeAudio(); exit(0); }

static void doButton(int i) {
    switch (i) {
    case 0: startSim(); break;
    case 1: if (started) running = false; break;
    case 2: if (started) running = true; break;
    case 3: resetSim(); break;
    case 4: nightMode = !nightMode; setMsg(nightMode ? "Night mode" : "Day mode"); break;
    case 5: setView((viewMode + 1) % 4); break;
    case 6: soundOn = !soundOn; setMsg(soundOn ? "Sound ON" : "Sound OFF"); break;
    case 7: speedMul = (speedMul == 1) ? 2 : (speedMul == 2 ? 4 : 1); break;
    }
}
static void keyboard(unsigned char k, int, int) {
    shiftHeld = (glutGetModifiers() & GLUT_ACTIVE_SHIFT) != 0;
    int c = tolower(k);
    keys[c] = true;
    switch (c) {
    case 13: startSim(); break;
    case ' ': if (!started) startSim(); else running = !running; break;
    case 'p': if (started) running = !running; break;
    case 'c': if (started) running = true; break;
    case 'r': resetSim(); break;
    case 'f': doButton(7); { char b[60]; snprintf(b, sizeof b, "Simulation speed x%d", speedMul); setMsg(b); } break;
    case 'n': doButton(4); break;
    case 'm': doButton(6); break;
    case 'h': showHUD = !showHUD; break;
    case 'v': setView((viewMode + 1) % 4); break;
    case '1': setView(V_OVER); break;
    case '2': setView(V_PERSON); break;
    case '3': setView(V_TOP); break;
    case '4': setView(V_BOAT); break;
    case 'b':
        if (viewMode == V_BOAT) { boatCam = (boatCam + 1) % NBOAT; char b[60]; snprintf(b, sizeof b, "Riding Rescue Boat %d", boatCam + 1); setMsg(b); }
        else setView(V_BOAT);
        break;
    case '+': case '=': zoom(0.9f); break;
    case '-': case '_': zoom(1.1f); break;
    case 27: quitApp(); break;
    }
}
static void keyboardUp(unsigned char k, int, int) {
    shiftHeld = (glutGetModifiers() & GLUT_ACTIVE_SHIFT) != 0;
    keys[tolower(k)] = false;
    keys[k] = false;
}
static void special(int k, int, int) {
    shiftHeld = (glutGetModifiers() & GLUT_ACTIVE_SHIFT) != 0;
    if (k == GLUT_KEY_LEFT)  sKeys[0] = true;
    if (k == GLUT_KEY_RIGHT) sKeys[1] = true;
    if (k == GLUT_KEY_UP)    sKeys[2] = true;
    if (k == GLUT_KEY_DOWN)  sKeys[3] = true;
    if (k == GLUT_KEY_PAGE_UP) zoom(0.9f);
    if (k == GLUT_KEY_PAGE_DOWN) zoom(1.1f);
    if (k == GLUT_KEY_F11) {
        fullScr = !fullScr;
        if (fullScr) glutFullScreen(); else { glutReshapeWindow(1280, 720); glutPositionWindow(60, 40); }
    }
}
static void specialUp(int k, int, int) {
    shiftHeld = (glutGetModifiers() & GLUT_ACTIVE_SHIFT) != 0;
    if (k == GLUT_KEY_LEFT)  sKeys[0] = false;
    if (k == GLUT_KEY_RIGHT) sKeys[1] = false;
    if (k == GLUT_KEY_UP)    sKeys[2] = false;
    if (k == GLUT_KEY_DOWN)  sKeys[3] = false;
}

static int dragBtn = -1, lastX = 0, lastY = 0;
static bool hudClick(int x, int y) {
    if (!showHUD) return false;
    for (int i = 0; i < 8; i++)
        if (x >= btns[i].x && x <= btns[i].x + btns[i].w && y >= btns[i].y && y <= btns[i].y + btns[i].h) { doButton(i); return true; }
    return false;
}
static void mouse(int b, int s, int x, int y) {
    if (s == GLUT_DOWN) {
        if (b == GLUT_LEFT_BUTTON && hudClick(x, y)) return;
        dragBtn = b; lastX = x; lastY = y;
    } else dragBtn = -1;
}
static void motion(int x, int y) {
    int dx = x - lastX, dy = y - lastY; lastX = x; lastY = y;
    if (dragBtn == GLUT_LEFT_BUTTON) {
        switch (viewMode) {
        case V_OVER: camYaw -= dx * 0.4f; camPitch = clampf(camPitch + dy * 0.4f, 6.0f, 88.0f); break;
        case V_TOP: camYaw -= dx * 0.4f; break;
        case V_PERSON: pYaw += dx * 0.25f; pPitch = clampf(pPitch - dy * 0.25f, -85, 85); break;
        case V_BOAT: bLookYaw += dx * 0.25f; bLookPitch = clampf(bLookPitch - dy * 0.25f, -60, 60); break;
        }
    } else if (dragBtn == GLUT_RIGHT_BUTTON || dragBtn == GLUT_MIDDLE_BUTTON) {
        if (viewMode == V_OVER || viewMode == V_TOP) {
            float s = (viewMode == V_TOP ? topH : camDist) * 0.0018f;
            panCam(dy * s, -dx * s);
        } else if (viewMode == V_PERSON) { pYaw += dx * 0.25f; pPitch = clampf(pPitch - dy * 0.25f, -85, 85); }
    }
}
static void wheel(int, int dir, int, int) {
    if (viewMode == V_PERSON) pLift = clampf(pLift + (dir > 0 ? 1.5f : -1.5f), 0, 45);
    else if (viewMode != V_BOAT) zoom(dir > 0 ? 0.9f : 1.1f);
}

static void initGL() {
    glEnable(GL_DEPTH_TEST);
    glEnable(GL_LIGHTING); glEnable(GL_LIGHT0);
    glEnable(GL_COLOR_MATERIAL);
    glColorMaterial(GL_FRONT_AND_BACK, GL_AMBIENT_AND_DIFFUSE);
    glEnable(GL_NORMALIZE);
    glShadeModel(GL_SMOOTH);
    glLightModeli(GL_LIGHT_MODEL_TWO_SIDE, GL_TRUE);
    GLfloat nospec[4] = { 0, 0, 0, 1 };
    glMaterialfv(GL_FRONT_AND_BACK, GL_SPECULAR, nospec);
    glHint(GL_FOG_HINT, GL_NICEST);
    glHint(GL_POINT_SMOOTH_HINT, GL_NICEST);
    glHint(GL_LINE_SMOOTH_HINT, GL_NICEST);
}
static void initSkyAndWeather() {
    for (int i = 0; i < 700; i++) {
        float x, y, z, l;
        do { x = rr(-1, 1); y = rr(0.02f, 1); z = rr(-1, 1); l = sqrtf(x * x + y * y + z * z); } while (l > 1 || l < 0.2f);
        starP[i][0] = x / l * 850; starP[i][1] = y / l * 850; starP[i][2] = z / l * 850; starPh[i] = rr(0, 6.28f);
    }
    for (int i = 0; i < 34; i++) { clouds[i].x = rr(-700, 700); clouds[i].y = rr(150, 220); clouds[i].z = rr(-650, 650); clouds[i].s = rr(28, 60); }
    for (int i = 0; i < NDROP; i++) respawnDrop(drops[i], true);
    for (int i = 0; i < NRIP; i++) { ripples[i].t = rr(-0.7f, 0.7f); ripples[i].x = rr(-20, 20); ripples[i].z = rr(-20, 20); }
}

int main(int argc, char** argv) {
    glutInit(&argc, argv);
    glutInitDisplayMode(GLUT_DOUBLE | GLUT_RGB | GLUT_DEPTH | GLUT_MULTISAMPLE);
    glutInitWindowSize(winW, winH);
    glutCreateWindow("Flood Escape and Cyclone Shelter Rescue Simulator");
    if (fullScr) glutFullScreen();
    initGL();

    initRoads();
    makeHouses();
    makeTrees();
    makeOuterWorld();
    makeSpots();
    initCars();
    initNav();
    initBoats();
    initSkyAndWeather();
    buildScene();
    resetSim();
    setMsg("Press START (or ENTER) to begin the cyclone.  1-4 = views,  N = day / night.");
    initAudio();

    glutDisplayFunc(display);
    glutReshapeFunc(reshape);
    glutIdleFunc(idle);
    glutKeyboardFunc(keyboard);
    glutKeyboardUpFunc(keyboardUp);
    glutSpecialFunc(special);
    glutSpecialUpFunc(specialUp);
    glutMouseFunc(mouse);
    glutMotionFunc(motion);
    glutMouseWheelFunc(wheel);
    glutIgnoreKeyRepeat(1);
    lastT = glutGet(GLUT_ELAPSED_TIME);
    glutMainLoop();
    closeAudio();
    return 0;
}