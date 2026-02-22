(* bats-poc -- proof of concept bats reimplementation *)
(* Step 2: read bats.toml, parse it, print package info *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use result as R
#use file as F
#use toml as T

implement main0 () = let
  (* Build "bats.toml" path *)
  val path = $A.alloc<byte>(9)
  val () = $A.write_byte(path, 0, 98)
  val () = $A.write_byte(path, 1, 97)
  val () = $A.write_byte(path, 2, 116)
  val () = $A.write_byte(path, 3, 115)
  val () = $A.write_byte(path, 4, 46)
  val () = $A.write_byte(path, 5, 116)
  val () = $A.write_byte(path, 6, 111)
  val () = $A.write_byte(path, 7, 109)
  val () = $A.write_byte(path, 8, 108)

  val @(fz, bv) = $A.freeze<byte>(path)
  val open_result = $F.file_open(bv, 9, 0, 0)
  val () = $A.drop<byte>(fz, bv)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in
  case+ open_result of
  | ~$R.ok(fd) => let
      val buf = $A.alloc<byte>(4096)
      val read_result = $F.file_read(fd, buf, 4096)
    in
      case+ read_result of
      | ~$R.ok(n) => let
          val close_r = $F.file_close(fd)
          val () = $R.discard<int><int>(close_r)
          (* Parse the TOML *)
          val @(fz2, bv2) = $A.freeze<byte>(buf)
          val parse_r = $T.parse(bv2, n)
          val () = $A.drop<byte>(fz2, bv2)
          val () = $A.free<byte>($A.thaw<byte>(fz2))
        in
          case+ parse_r of
          | ~$R.ok(doc) => let
              val () = println! ("Parsed bats.toml successfully")
              val () = $T.toml_free(doc)
            in end
          | ~$R.err(e) => let
              val () = println! ("TOML parse error: ", e)
            in end
        end
      | ~$R.err(e) => let
          val close_r = $F.file_close(fd)
          val () = $R.discard<int><int>(close_r)
          val () = $A.free<byte>(buf)
          val () = println! ("Read error: ", e)
        in end
    end
  | ~$R.err(e) => let
      val () = println! ("Cannot open bats.toml: ", e)
    in end
end
