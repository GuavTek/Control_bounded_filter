#include "system.h"

TOP *top = NULL;


extern void esc_elaborate()
{
    top = new TOP("top");
}

extern void  esc_cleanup()
{
    delete top;
}

int sc_main(int argc, char *argv[])
{
    esc_initialize(argc, argv);
    esc_elaborate();
    sc_start();
    return 0;
}

