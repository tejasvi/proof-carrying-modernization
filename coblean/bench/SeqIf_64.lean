import Cobol
open Cobol Lean Elab Tactic

elab "hb_count " t:tactic : tactic => do
  let h0 ← IO.getNumHeartbeats
  evalTactic t
  let h1 ← IO.getNumHeartbeats
  logInfo m!"kHB: {(h1 - h0) / 1000}"

/-- Java: `for (int f : fs) if (f > 0) { cnt++; total += f; }` -/
def javaCount (fs : List Int) : Int × Int :=
  fs.foldl (fun acc f => if 0 < f then (acc.1 + 1, acc.2 + f) else acc) (0, 0)

cobol_program SeqIf64 from "seqif_64.ir.json"

open SeqIf64 in
def obs (r : Sem.Res) : Option (Int × Int) :=
  if r.1 = .stop .goback then
    match decodeNum {} CNT.fmt (r.2.mem.field CNT), decodeNum {} TOTAL.fmt (r.2.mem.field TOTAL) with
    | some c, some t => some (c, t)
    | _, _ => none
  else none

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
open SeqIf64 in
theorem seqif (m : Mem) (hm : m.size = 200) (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 : Int)
    (h1 : decodeNum {} F_1.fmt (m.field F_1) = some f1)
    (h2 : decodeNum {} F_2.fmt (m.field F_2) = some f2)
    (h3 : decodeNum {} F_3.fmt (m.field F_3) = some f3)
    (h4 : decodeNum {} F_4.fmt (m.field F_4) = some f4)
    (h5 : decodeNum {} F_5.fmt (m.field F_5) = some f5)
    (h6 : decodeNum {} F_6.fmt (m.field F_6) = some f6)
    (h7 : decodeNum {} F_7.fmt (m.field F_7) = some f7)
    (h8 : decodeNum {} F_8.fmt (m.field F_8) = some f8)
    (h9 : decodeNum {} F_9.fmt (m.field F_9) = some f9)
    (h10 : decodeNum {} F_10.fmt (m.field F_10) = some f10)
    (h11 : decodeNum {} F_11.fmt (m.field F_11) = some f11)
    (h12 : decodeNum {} F_12.fmt (m.field F_12) = some f12)
    (h13 : decodeNum {} F_13.fmt (m.field F_13) = some f13)
    (h14 : decodeNum {} F_14.fmt (m.field F_14) = some f14)
    (h15 : decodeNum {} F_15.fmt (m.field F_15) = some f15)
    (h16 : decodeNum {} F_16.fmt (m.field F_16) = some f16)
    (h17 : decodeNum {} F_17.fmt (m.field F_17) = some f17)
    (h18 : decodeNum {} F_18.fmt (m.field F_18) = some f18)
    (h19 : decodeNum {} F_19.fmt (m.field F_19) = some f19)
    (h20 : decodeNum {} F_20.fmt (m.field F_20) = some f20)
    (h21 : decodeNum {} F_21.fmt (m.field F_21) = some f21)
    (h22 : decodeNum {} F_22.fmt (m.field F_22) = some f22)
    (h23 : decodeNum {} F_23.fmt (m.field F_23) = some f23)
    (h24 : decodeNum {} F_24.fmt (m.field F_24) = some f24)
    (h25 : decodeNum {} F_25.fmt (m.field F_25) = some f25)
    (h26 : decodeNum {} F_26.fmt (m.field F_26) = some f26)
    (h27 : decodeNum {} F_27.fmt (m.field F_27) = some f27)
    (h28 : decodeNum {} F_28.fmt (m.field F_28) = some f28)
    (h29 : decodeNum {} F_29.fmt (m.field F_29) = some f29)
    (h30 : decodeNum {} F_30.fmt (m.field F_30) = some f30)
    (h31 : decodeNum {} F_31.fmt (m.field F_31) = some f31)
    (h32 : decodeNum {} F_32.fmt (m.field F_32) = some f32)
    (h33 : decodeNum {} F_33.fmt (m.field F_33) = some f33)
    (h34 : decodeNum {} F_34.fmt (m.field F_34) = some f34)
    (h35 : decodeNum {} F_35.fmt (m.field F_35) = some f35)
    (h36 : decodeNum {} F_36.fmt (m.field F_36) = some f36)
    (h37 : decodeNum {} F_37.fmt (m.field F_37) = some f37)
    (h38 : decodeNum {} F_38.fmt (m.field F_38) = some f38)
    (h39 : decodeNum {} F_39.fmt (m.field F_39) = some f39)
    (h40 : decodeNum {} F_40.fmt (m.field F_40) = some f40)
    (h41 : decodeNum {} F_41.fmt (m.field F_41) = some f41)
    (h42 : decodeNum {} F_42.fmt (m.field F_42) = some f42)
    (h43 : decodeNum {} F_43.fmt (m.field F_43) = some f43)
    (h44 : decodeNum {} F_44.fmt (m.field F_44) = some f44)
    (h45 : decodeNum {} F_45.fmt (m.field F_45) = some f45)
    (h46 : decodeNum {} F_46.fmt (m.field F_46) = some f46)
    (h47 : decodeNum {} F_47.fmt (m.field F_47) = some f47)
    (h48 : decodeNum {} F_48.fmt (m.field F_48) = some f48)
    (h49 : decodeNum {} F_49.fmt (m.field F_49) = some f49)
    (h50 : decodeNum {} F_50.fmt (m.field F_50) = some f50)
    (h51 : decodeNum {} F_51.fmt (m.field F_51) = some f51)
    (h52 : decodeNum {} F_52.fmt (m.field F_52) = some f52)
    (h53 : decodeNum {} F_53.fmt (m.field F_53) = some f53)
    (h54 : decodeNum {} F_54.fmt (m.field F_54) = some f54)
    (h55 : decodeNum {} F_55.fmt (m.field F_55) = some f55)
    (h56 : decodeNum {} F_56.fmt (m.field F_56) = some f56)
    (h57 : decodeNum {} F_57.fmt (m.field F_57) = some f57)
    (h58 : decodeNum {} F_58.fmt (m.field F_58) = some f58)
    (h59 : decodeNum {} F_59.fmt (m.field F_59) = some f59)
    (h60 : decodeNum {} F_60.fmt (m.field F_60) = some f60)
    (h61 : decodeNum {} F_61.fmt (m.field F_61) = some f61)
    (h62 : decodeNum {} F_62.fmt (m.field F_62) = some f62)
    (h63 : decodeNum {} F_63.fmt (m.field F_63) = some f63)
    (h64 : decodeNum {} F_64.fmt (m.field F_64) = some f64) :
    obs (SeqIf64.run {} 10 (SeqIf64.initState m)) = some (javaCount [f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56, f57, f58, f59, f60, f61, f62, f63, f64]) := by
  cobol_ranges
  hb_count cobol_equiv [obs, javaCount, hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64]
