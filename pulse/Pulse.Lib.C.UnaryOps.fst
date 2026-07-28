module Pulse.Lib.C.UnaryOps
#lang-pulse
open Pulse

fn pluspluspost_int8 (i : ref Int8.t) (#_i: erased Int8.t)
  requires i |-> _i
  requires pure FStar.Int8.(fits (v _i + 1))
  returns Int8.t
  ensures exists* k. (i |-> k) ** pure FStar.Int8.((v k <: int) == v _i + 1) 
{
  let j = !i;
  i := Int8.add j 1y;
  j;
}

fn pluspluspost_int16 (i : ref Int16.t) (#_i: erased Int16.t)
  requires i |-> _i
  requires pure FStar.Int16.(fits (v _i + 1))
  returns Int16.t
  ensures exists* k. (i |-> k) ** pure FStar.Int16.((v k <: int) == v _i + 1)
{
  let j = !i;
  i := Int16.add j 1s;
  j;
}

fn pluspluspost_int32 (i : ref Int32.t) (#_i: erased Int32.t)
  requires i |-> _i
  requires pure FStar.Int32.(fits (v _i + 1))
  returns Int32.t
  ensures exists* k. (i |-> k) ** pure FStar.Int32.((v k <: int) == v _i + 1)
{
  let j = !i;
  i := Int32.add j 1l;
  j;
}


fn pluspluspost_int64 (i : ref Int64.t) (#_i: erased Int64.t)
  requires i |-> _i
  requires pure FStar.Int64.(fits (v _i + 1))
  returns Int64.t
  ensures exists* k. (i |-> k) ** pure FStar.Int64.((v k <: int) == v _i + 1)
{
  let j = !i;
  i := Int64.add j 1L;
  j;
}


fn pluspluspost_uint8 (i : ref UInt8.t) (#_i: erased UInt8.t)
  requires i |-> _i
  returns UInt8.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt8.v _i + 1) FStar.UInt8.n
      then FStar.UInt8.v k == FStar.UInt8.v _i + 1
      else FStar.UInt8.v k == FStar.UInt.add_mod (FStar.UInt8.v _i) 1)
{
  let j = !i;
  i := UInt8.add_mod j 1uy;
  j;
}

fn pluspluspost_uint16 (i : ref UInt16.t) (#_i: erased UInt16.t)
  requires i |-> _i
  returns UInt16.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt16.v _i + 1) FStar.UInt16.n
      then FStar.UInt16.v k == FStar.UInt16.v _i + 1
      else FStar.UInt16.v k == FStar.UInt.add_mod (FStar.UInt16.v _i) 1)
{
  let j = !i;
  i := UInt16.add_mod j 1us;
  j;
}

fn pluspluspost_uint32 (i : ref UInt32.t) (#_i: erased UInt32.t)
  requires i |-> _i
  returns UInt32.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt32.v _i + 1) FStar.UInt32.n
      then FStar.UInt32.v k == FStar.UInt32.v _i + 1
      else FStar.UInt32.v k == FStar.UInt.add_mod (FStar.UInt32.v _i) 1)
{
  let j = !i;
  i := UInt32.add_mod j 1ul;
  j;
}


fn pluspluspost_uint64 (i : ref UInt64.t) (#_i: erased UInt64.t)
  requires i |-> _i
  returns UInt64.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt64.v _i + 1) FStar.UInt64.n
      then FStar.UInt64.v k == FStar.UInt64.v _i + 1
      else FStar.UInt64.v k == FStar.UInt.add_mod (FStar.UInt64.v _i) 1)
{
  let j = !i;
  i := UInt64.add_mod j 1UL;
  j;
}


fn pluspluspost_sizet (i : ref SizeT.t) (#_i: erased SizeT.t)
  requires i |-> _i
  requires pure FStar.SizeT.(fits (v _i + 1))
  returns SizeT.t
  ensures exists* k. (i |-> k) ** pure FStar.SizeT.((v k <: int) == v _i + 1)
{
  let j = !i;
  i := SizeT.add j 1sz;
  j;
}

fn pluspluspre_int8 (i : ref Int8.t) (#_i: erased Int8.t)
  requires i |-> _i
  requires pure FStar.Int8.(fits (v _i + 1))
  returns Int8.t
  ensures exists* k. (i |-> k) ** pure FStar.Int8.((v k <: int) == v _i + 1)
{
  i := Int8.add !i 1y;
  !i;
}

fn pluspluspre_int16 (i : ref Int16.t) (#_i: erased Int16.t)
  requires i |-> _i
  requires pure FStar.Int16.(fits (v _i + 1))
  returns Int16.t
  ensures exists* k. (i |-> k) ** pure FStar.Int16.((v k <: int) == v _i + 1)
{
  i := Int16.add !i 1s;
  !i;
}

fn pluspluspre_int32 (i : ref Int32.t) (#_i: erased Int32.t)
  requires i |-> _i
  requires pure FStar.Int32.(fits (v _i + 1))
  returns Int32.t
  ensures exists* k. (i |-> k) ** pure FStar.Int32.((v k <: int) == v _i + 1)
{
  i := Int32.add !i 1l;
  !i;
}


fn pluspluspre_int64 (i : ref Int64.t) (#_i: erased Int64.t)
  requires i |-> _i
  requires pure FStar.Int64.(fits (v _i + 1))
  returns Int64.t
  ensures exists* k. (i |-> k) ** pure FStar.Int64.((v k <: int) == v _i + 1)
{
  i := Int64.add !i 1L;
  !i;
}


fn pluspluspre_uint8 (i : ref UInt8.t) (#_i: erased UInt8.t)
  requires i |-> _i
  returns UInt8.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt8.v _i + 1) FStar.UInt8.n
      then FStar.UInt8.v k == FStar.UInt8.v _i + 1
      else FStar.UInt8.v k == FStar.UInt.add_mod (FStar.UInt8.v _i) 1)
{
  i := UInt8.add_mod !i 1uy;
  !i;
}

fn pluspluspre_uint16 (i : ref UInt16.t) (#_i: erased UInt16.t)
  requires i |-> _i
  returns UInt16.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt16.v _i + 1) FStar.UInt16.n
      then FStar.UInt16.v k == FStar.UInt16.v _i + 1
      else FStar.UInt16.v k == FStar.UInt.add_mod (FStar.UInt16.v _i) 1)
{
  i := UInt16.add_mod !i 1us;
  !i;
}

fn pluspluspre_uint32 (i : ref UInt32.t) (#_i: erased UInt32.t)
  requires i |-> _i
  returns UInt32.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt32.v _i + 1) FStar.UInt32.n
      then FStar.UInt32.v k == FStar.UInt32.v _i + 1
      else FStar.UInt32.v k == FStar.UInt.add_mod (FStar.UInt32.v _i) 1)
{
  i := UInt32.add_mod !i 1ul;
  !i;
}


fn pluspluspre_uint64 (i : ref UInt64.t) (#_i: erased UInt64.t)
  requires i |-> _i
  returns UInt64.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt64.v _i + 1) FStar.UInt64.n
      then FStar.UInt64.v k == FStar.UInt64.v _i + 1
      else FStar.UInt64.v k == FStar.UInt.add_mod (FStar.UInt64.v _i) 1)
{
  i := UInt64.add_mod !i 1UL;
  !i;
}

fn pluspluspre_sizet (i : ref SizeT.t) (#_i: erased SizeT.t)
  requires i |-> _i
  requires pure FStar.SizeT.(fits (v _i + 1))
  returns SizeT.t
  ensures exists* k. (i |-> k) ** pure FStar.SizeT.((v k <: int) == v _i + 1)
{
  i := SizeT.add !i 1sz;
  !i;
}


//Decrement functions

fn minusminuspost_int8 (i : ref Int8.t) (#_i: erased Int8.t)
  requires i |-> _i
  requires pure FStar.Int8.(fits (v _i - 1))
  returns Int8.t
  ensures exists* k. (i |-> k) ** pure FStar.Int8.((v k <: int) == v _i - 1) 
{
  let j = !i;
  i := Int8.sub j 1y;
  j;
}

fn minusminuspost_int16 (i : ref Int16.t) (#_i: erased Int16.t)
  requires i |-> _i
  requires pure FStar.Int16.(fits (v _i - 1))
  returns Int16.t
  ensures exists* k. (i |-> k) ** pure FStar.Int16.((v k <: int) == v _i - 1)
{
  let j = !i;
  i := Int16.sub j 1s;
  j;
}

fn minusminuspost_int32 (i : ref Int32.t) (#_i: erased Int32.t)
  requires i |-> _i
  requires pure FStar.Int32.(fits (v _i - 1))
  returns Int32.t
  ensures exists* k. (i |-> k) ** pure FStar.Int32.((v k <: int) == v _i - 1)
{
  let j = !i;
  i := Int32.sub j 1l;
  j;
}


fn minusminuspost_int64 (i : ref Int64.t) (#_i: erased Int64.t)
  requires i |-> _i
  requires pure FStar.Int64.(fits (v _i - 1))
  returns Int64.t
  ensures exists* k. (i |-> k) ** pure FStar.Int64.((v k <: int) == v _i - 1)
{
  let j = !i;
  i := Int64.sub j 1L;
  j;
}


fn minusminuspost_uint8 (i : ref UInt8.t) (#_i: erased UInt8.t)
  requires i |-> _i
  returns UInt8.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt8.v _i - 1) FStar.UInt8.n
      then FStar.UInt8.v k == FStar.UInt8.v _i - 1
      else FStar.UInt8.v k == FStar.UInt.sub_mod (FStar.UInt8.v _i) 1)
{
  let j = !i;
  i := UInt8.sub_mod j 1uy;
  j;
}

fn minusminuspost_uint16 (i : ref UInt16.t) (#_i: erased UInt16.t)
  requires i |-> _i
  returns UInt16.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt16.v _i - 1) FStar.UInt16.n
      then FStar.UInt16.v k == FStar.UInt16.v _i - 1
      else FStar.UInt16.v k == FStar.UInt.sub_mod (FStar.UInt16.v _i) 1)
{
  let j = !i;
  i := UInt16.sub_mod j 1us;
  j;
}

fn minusminuspost_uint32 (i : ref UInt32.t) (#_i: erased UInt32.t)
  requires i |-> _i
  returns UInt32.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt32.v _i - 1) FStar.UInt32.n
      then FStar.UInt32.v k == FStar.UInt32.v _i - 1
      else FStar.UInt32.v k == FStar.UInt.sub_mod (FStar.UInt32.v _i) 1)
{
  let j = !i;
  i := UInt32.sub_mod j 1ul;
  j;
}


fn minusminuspost_uint64 (i : ref UInt64.t) (#_i: erased UInt64.t)
  requires i |-> _i
  returns UInt64.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt64.v _i - 1) FStar.UInt64.n
      then FStar.UInt64.v k == FStar.UInt64.v _i - 1
      else FStar.UInt64.v k == FStar.UInt.sub_mod (FStar.UInt64.v _i) 1)
{
  let j = !i;
  i := UInt64.sub_mod j 1UL;
  j;
}


fn minusminuspost_sizet (i : ref SizeT.t) (#_i: erased SizeT.t)
  requires i |-> _i
  requires pure (SizeT.v _i > 0) 
  returns SizeT.t
  ensures exists* k. (i |-> k) ** pure FStar.SizeT.((v k <: int) == v _i - 1)
{
  let j = !i;
  i := SizeT.sub j 1sz;
  j;
}

fn minusminuspre_int8 (i : ref Int8.t) (#_i: erased Int8.t)
  requires i |-> _i
  requires pure FStar.Int8.(fits (v _i - 1))
  returns Int8.t
  ensures exists* k. (i |-> k) ** pure FStar.Int8.((v k <: int) == v _i - 1)
{
  i := Int8.sub !i 1y;
  !i;
}

fn minusminuspre_int16 (i : ref Int16.t) (#_i: erased Int16.t)
  requires i |-> _i
  requires pure FStar.Int16.(fits (v _i - 1))
  returns Int16.t
  ensures exists* k. (i |-> k) ** pure FStar.Int16.((v k <: int) == v _i - 1)
{
  i := Int16.sub !i 1s;
  !i;
}

fn minusminuspre_int32 (i : ref Int32.t) (#_i: erased Int32.t)
  requires i |-> _i
  requires pure FStar.Int32.(fits (v _i - 1))
  returns Int32.t
  ensures exists* k. (i |-> k) ** pure FStar.Int32.((v k <: int) == v _i - 1)
{
  i := Int32.sub !i 1l;
  !i;
}


fn minusminuspre_int64 (i : ref Int64.t) (#_i: erased Int64.t)
  requires i |-> _i
  requires pure FStar.Int64.(fits (v _i - 1))
  returns Int64.t
  ensures exists* k. (i |-> k) ** pure FStar.Int64.((v k <: int) == v _i - 1)
{
  i := Int64.sub !i 1L;
  !i;
}


fn minusminuspre_uint8 (i : ref UInt8.t) (#_i: erased UInt8.t)
  requires i |-> _i
  returns UInt8.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt8.v _i - 1) FStar.UInt8.n
      then FStar.UInt8.v k == FStar.UInt8.v _i - 1
      else FStar.UInt8.v k == FStar.UInt.sub_mod (FStar.UInt8.v _i) 1)
{
  i := UInt8.sub_mod !i 1uy;
  !i;
}

fn minusminuspre_uint16 (i : ref UInt16.t) (#_i: erased UInt16.t)
  requires i |-> _i
  returns UInt16.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt16.v _i - 1) FStar.UInt16.n
      then FStar.UInt16.v k == FStar.UInt16.v _i - 1
      else FStar.UInt16.v k == FStar.UInt.sub_mod (FStar.UInt16.v _i) 1)
{
  i := UInt16.sub_mod !i 1us;
  !i;
}

fn minusminuspre_uint32 (i : ref UInt32.t) (#_i: erased UInt32.t)
  requires i |-> _i
  returns UInt32.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt32.v _i - 1) FStar.UInt32.n
      then FStar.UInt32.v k == FStar.UInt32.v _i - 1
      else FStar.UInt32.v k == FStar.UInt.sub_mod (FStar.UInt32.v _i) 1)
{
  i := UInt32.sub_mod !i 1ul;
  !i;
}


fn minusminuspre_uint64 (i : ref UInt64.t) (#_i: erased UInt64.t)
  requires i |-> _i
  returns UInt64.t
  ensures exists* k. (i |-> k) **
    pure (
      if FStar.UInt.fits (FStar.UInt64.v _i - 1) FStar.UInt64.n
      then FStar.UInt64.v k == FStar.UInt64.v _i - 1
      else FStar.UInt64.v k == FStar.UInt.sub_mod (FStar.UInt64.v _i) 1)
{
  i := UInt64.sub_mod !i 1UL;
  !i;
}

fn minusminuspre_sizet (i : ref SizeT.t) (#_i: erased SizeT.t)
  requires i |-> _i
  requires pure (SizeT.v _i > 0)
  returns SizeT.t
  ensures exists* k. (i |-> k) ** pure FStar.SizeT.((v k <: int) == v _i - 1)
{
  i := SizeT.sub !i 1sz;
  !i;
}