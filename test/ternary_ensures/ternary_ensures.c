#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

typedef struct View {
    uint32_t Size;
} View;

typedef struct Parser {
    View BaseView;
    uint32_t Offset;
} Parser;

uint32_t FieldArm(View *view)
    _ensures(return == 11)
{
    return 11;
}

uint32_t WholeArm(Parser *parser)
    _ensures(return == 22)
{
    return 22;
}

uint32_t choose_assign(bool use_view)
    _ensures(return == 11 || return == 22)
{
    Parser storage = { 0 };
    Parser *parser = &storage;
    uint32_t bound = 0;
    _ternary_ensures(_live(storage) && _live(parser) && _live(use_view) && _live(bound) &&
        (bound == 11 || bound == 22));
    bound = use_view ? FieldArm(&parser->BaseView) : WholeArm(parser);
    return bound;
}

uint32_t choose_initializer(bool use_view)
    _ensures(return == 11 || return == 22)
{
    Parser storage = { 0 };
    Parser *parser = &storage;
    _ternary_ensures(_live(storage) && _live(parser) && _live(use_view) && _live(bound) &&
        (bound == 11 || bound == 22));
    uint32_t bound = use_view ? FieldArm(&parser->BaseView) : WholeArm(parser);
    return bound;
}

uint32_t choose_return(bool use_view)
    _ensures(true)
{
    Parser storage = { 0 };
    Parser *parser = &storage;
    _ternary_ensures(_live(storage) && _live(parser) && _live(use_view));
    return use_view ? FieldArm(&parser->BaseView) : WholeArm(parser);
}

uint32_t choose_bad_post(bool use_view)
    _ensures(true)
{
    Parser storage = { 0 };
    Parser *parser = &storage;
    uint32_t bound = 0;
    _ternary_ensures(_live(storage) && _live(parser) && _live(use_view) && _live(bound) && bound == 42);
    bound = use_view ? FieldArm(&parser->BaseView) : WholeArm(parser);
    return bound;
}
