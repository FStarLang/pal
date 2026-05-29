#include "pal.h"

struct foo {
    int x;
    int y;
};

struct foo2 {
    int left;
    struct xy {
        int x;
        int y;
    };
};

struct xy foo() {
    return (struct xy) { .x = 42, .y = 67 };
}