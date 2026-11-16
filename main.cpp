#include <iostream>
#include <graphics.h>
#include <conio.h>

using namespace std;

int main()
{
    initwindow(1000, 700, "Flood Escape Simulator");

    setbkcolor(LIGHTCYAN);
    cleardevice();

    setcolor(BLACK);
    settextstyle(DEFAULT_FONT, HORIZ_DIR, 2);

    outtextxy(250, 100, "FLOOD ESCAPE SIMULATOR");

    setfillstyle(SOLID_FILL, GREEN);
    bar(100, 200, 900, 600);

    setcolor(BLACK);
    rectangle(100, 200, 900, 600);

    outtextxy(300, 630, "Town Map - Project Started");

    getch();
    closegraph();

    return 0;
}