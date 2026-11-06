import EquivLean.Modernize.Cbstm03a.Java.Cs.Cut

/-!
# CBSTM03A → Java: `createStatement`, the paths through the calls of `stmt` and `html`

One theorem per call (`o<pc>`, statement `pc`): from the cut point right before the call to the cut point right
after it (`cut_html_lit`, `cut_html_loc`, `cut_stmt_loc`); the statement, the next cut point and the line written
are checked by evaluation (`rfl`). The last call, with the return, is `cut_last`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

set_option maxRecDepth 20000 in
theorem o19 (g : G) : CutVC g 19 0 0 LA19 true :=
  fun _ _ _ => cut_stmt_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o20 (g : G) : CutVC g 20 1 0 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o21 (g : G) : CutVC g 21 1 1 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o22 (g : G) : CutVC g 22 1 2 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o23 (g : G) : CutVC g 23 1 3 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o24 (g : G) : CutVC g 24 1 4 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o25 (g : G) : CutVC g 25 1 5 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o26 (g : G) : CutVC g 26 1 6 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o27 (g : G) : CutVC g 27 1 7 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o28 (g : G) : CutVC g 28 1 8 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o29 (g : G) : CutVC g 29 1 9 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o32 (g : G) : CutVC g 32 1 10 LA32 true :=
  fun _ _ _ => cut_html_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o33 (g : G) : CutVC g 33 1 11 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o34 (g : G) : CutVC g 34 1 12 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o35 (g : G) : CutVC g 35 1 13 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o36 (g : G) : CutVC g 36 1 14 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o37 (g : G) : CutVC g 37 1 15 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o38 (g : G) : CutVC g 38 1 16 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o39 (g : G) : CutVC g 39 1 17 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o40 (g : G) : CutVC g 40 1 18 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o41 (g : G) : CutVC g 41 1 19 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o42 (g : G) : CutVC g 42 1 20 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o43 (g : G) : CutVC g 43 1 21 LA true :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o71 (g : G) : CutVC g 71 1 22 LD71 false :=
  fun _ _ _ => cut_html_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o73 (g : G) : CutVC g 73 1 23 LD73 false :=
  fun _ _ _ => cut_html_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o75 (g : G) : CutVC g 75 1 24 LD75 false :=
  fun _ _ _ => cut_html_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o77 (g : G) : CutVC g 77 1 25 LD77 false :=
  fun _ _ _ => cut_html_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o78 (g : G) : CutVC g 78 1 26 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o79 (g : G) : CutVC g 79 1 27 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o80 (g : G) : CutVC g 80 1 28 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o81 (g : G) : CutVC g 81 1 29 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o82 (g : G) : CutVC g 82 1 30 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o83 (g : G) : CutVC g 83 1 31 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o84 (g : G) : CutVC g 84 1 32 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o85 (g : G) : CutVC g 85 1 33 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o86 (g : G) : CutVC g 86 1 34 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o88 (g : G) : CutVC g 88 1 35 LD88 false :=
  fun _ _ _ => cut_html_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o90 (g : G) : CutVC g 90 1 36 LD90 false :=
  fun _ _ _ => cut_html_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o92 (g : G) : CutVC g 92 1 37 LD92 false :=
  fun _ _ _ => cut_html_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o93 (g : G) : CutVC g 93 1 38 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o94 (g : G) : CutVC g 94 1 39 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o95 (g : G) : CutVC g 95 1 40 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o96 (g : G) : CutVC g 96 1 41 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o97 (g : G) : CutVC g 97 1 42 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o98 (g : G) : CutVC g 98 1 43 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o99 (g : G) : CutVC g 99 1 44 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o100 (g : G) : CutVC g 100 1 45 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o101 (g : G) : CutVC g 101 1 46 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o102 (g : G) : CutVC g 102 1 47 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o103 (g : G) : CutVC g 103 1 48 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o104 (g : G) : CutVC g 104 1 49 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o105 (g : G) : CutVC g 105 1 50 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o106 (g : G) : CutVC g 106 1 51 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o107 (g : G) : CutVC g 107 1 52 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o108 (g : G) : CutVC g 108 1 53 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o109 (g : G) : CutVC g 109 1 54 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o110 (g : G) : CutVC g 110 1 55 LD false :=
  fun _ _ _ => cut_html_lit rfl rfl rfl (by decide +kernel) (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o114 (g : G) : CutVC g 114 1 56 LE114 false :=
  fun _ _ _ => cut_stmt_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o117 (g : G) : CutVC g 117 2 56 LF117 false :=
  fun _ _ _ => cut_stmt_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o120 (g : G) : CutVC g 120 3 56 LG120 false :=
  fun _ _ _ => cut_stmt_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o121 (g : G) : CutVC g 121 4 56 LG false :=
  fun _ _ _ => cut_stmt_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o122 (g : G) : CutVC g 122 5 56 LH false :=
  fun _ _ _ => cut_stmt_loc rfl rfl rfl rfl (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o126 (g : G) : CutVC g 126 6 56 LH126 false :=
  fun _ _ _ => cut_stmt_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o127 (g : G) : CutVC g 127 7 56 LH false :=
  fun _ _ _ => cut_stmt_loc rfl rfl rfl rfl (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o130 (g : G) : CutVC g 130 8 56 LH130 false :=
  fun _ _ _ => cut_stmt_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o133 (g : G) : CutVC g 133 9 56 LI133 false :=
  fun _ _ _ => cut_stmt_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o136 (g : G) : CutVC g 136 10 56 LJ136 false :=
  fun _ _ _ => cut_stmt_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o137 (g : G) : CutVC g 137 11 56 LK false :=
  fun _ _ _ => cut_stmt_loc rfl rfl rfl rfl (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o141 (g : G) : CutVC g 141 12 56 LK141 false :=
  fun _ _ _ => cut_stmt_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

set_option maxRecDepth 20000 in
theorem o142 (g : G) : CutVC g 142 13 56 LK false :=
  fun _ _ _ => cut_stmt_loc rfl rfl rfl rfl (fun _ _ h => h) id

set_option maxRecDepth 20000 in
theorem o145 (g : G) : CutVC g 145 14 56 LK145 false :=
  fun _ _ _ => cut_stmt_loc rfl rfl rfl rfl (fun _ _ h => h.2) id

end EquivLean.Modernize.Cbstm03a.Java.Cs
