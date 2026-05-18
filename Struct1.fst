module Struct
open Pulse
#lang-pulse

noeq type foo = {
  x: ref int;
  y: ref int;
}

[@@erasable] noeq type foo_spec = {
  x': int;
  y': int;
}

// let foo_pred ([@@@mkey]x: foo) (y: foo_spec) : slprop =
//   pts_to x.x y.x' ** pts_to x.y y.y'

let foo_pred ([@@@mkey]x: foo) (y: foo_spec) : slprop =
  exists* vx vy.
  pts_to x.x vx ** pts_to x.y vy **
    pure (y == {x'=vx;y'=vy})
    // pure (y.x' == (!x.x)) ** pure (y.y' == (!x.y))

fn read_x (x: foo)
  preserves foo_pred x 'vx
  returns _: int
{
  unfold foo_pred x;
  let result = !x.x;
  fold foo_pred x;
  result
}

let foo_value (x: foo) #y = observe (foo_pred x) #y

fn write_x (x: foo)
  preserves exists* vx. foo_pred x vx
  ensures pure ((foo_value x).x' == 10)
{
  with vx0. assert foo_pred x vx0;
  unfold foo_pred x;
  x.x := 10;
  // admit ();
  fold foo_pred x;
  // admit ();
  ()
}
