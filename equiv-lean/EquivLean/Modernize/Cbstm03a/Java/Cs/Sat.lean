import EquivLean.Modernize.Cbstm03a.Java.Cs.Out
import EquivLean.Modernize.Cbstm03a.Java.Cs.S1
import EquivLean.Modernize.Cbstm03a.Java.Cs.S2
import EquivLean.Modernize.Cbstm03a.Java.Cs.S3
import EquivLean.Modernize.Cbstm03a.Java.Cs.S2b
import EquivLean.Modernize.Cbstm03a.Java.Cs.S44
import EquivLean.Modernize.Cbstm03a.Java.Cs.S54
import EquivLean.Modernize.Cbstm03a.Java.Cs.S66
import EquivLean.Modernize.Cbstm03a.Java.Cs.Entry

/-!
# CBSTM03A → Java: `createStatement` satisfies `createStatementSpec`

The verification conditions of `createStatement` against `specG g` (`cs_vc`) from its segments: the entry path
(`entry_vc`), the 72 calls of `stmt`/`html` (`o<pc>`, `cut_last`) and the 19 computations between them
(`s<pc>`). The contract follows for every choice of the ghost values (`createStatement_sat`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

set_option maxRecDepth 40000 in
theorem cuts_vc (g : G) : ∀ p ∈ inv g, ∀ args σ0, (specG g).pre args σ0 → ∀ fr σ, p.2 args σ0 fr σ →
    wp g args σ0 p.1 fr σ := by
  intro p hp
  simp only [inv, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact o19 g
  · exact o20 g
  · exact o21 g
  · exact o22 g
  · exact o23 g
  · exact o24 g
  · exact o25 g
  · exact o26 g
  · exact o27 g
  · exact o28 g
  · exact o29 g
  · exact s30 g
  · exact o32 g
  · exact o33 g
  · exact o34 g
  · exact o35 g
  · exact o36 g
  · exact o37 g
  · exact o38 g
  · exact o39 g
  · exact o40 g
  · exact o41 g
  · exact o42 g
  · exact o43 g
  · exact s44 g
  · exact s54 g
  · exact s66 g
  · exact o71 g
  · exact s72 g
  · exact o73 g
  · exact s74 g
  · exact o75 g
  · exact s76 g
  · exact o77 g
  · exact o78 g
  · exact o79 g
  · exact o80 g
  · exact o81 g
  · exact o82 g
  · exact o83 g
  · exact o84 g
  · exact o85 g
  · exact o86 g
  · exact s87 g
  · exact o88 g
  · exact s89 g
  · exact o90 g
  · exact s91 g
  · exact o92 g
  · exact o93 g
  · exact o94 g
  · exact o95 g
  · exact o96 g
  · exact o97 g
  · exact o98 g
  · exact o99 g
  · exact o100 g
  · exact o101 g
  · exact o102 g
  · exact o103 g
  · exact o104 g
  · exact o105 g
  · exact o106 g
  · exact o107 g
  · exact o108 g
  · exact o109 g
  · exact o110 g
  · exact s111 g
  · exact o114 g
  · exact s115 g
  · exact o117 g
  · exact s118 g
  · exact o120 g
  · exact o121 g
  · exact o122 g
  · exact s123 g
  · exact o126 g
  · exact o127 g
  · exact s128 g
  · exact o130 g
  · exact s131 g
  · exact o133 g
  · exact s134 g
  · exact o136 g
  · exact o137 g
  · exact s138 g
  · exact o141 g
  · exact o142 g
  · exact s143 g
  · exact o145 g
  · exact cut_last g

set_option maxRecDepth 40000 in
theorem cs_vc (g : G) : MethodVC Gen.prog csCallees.env 1 createStatementRef (specG g) (inv g) 60 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · have e := entry_vc g args σ0 hpre
    unfold wp at e
    have h0 : ((inv g).inst args σ0).lookup 0 = none := rfl
    rw [h0]
    exact e
  · intro p hp fr σ hI
    simp only [Invariants.inst, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have e := cuts_vc g q hq args σ0 hpre fr σ hI
    unfold wp at e
    exact e

end EquivLean.Modernize.Cbstm03a.Java.Cs

namespace EquivLean.Modernize.Cbstm03a.Java

open Cs in
/-- **`createStatement` satisfies its contract**, given the contracts of its callees (`csCallees`). -/
theorem createStatement_sat (hV : Valid Gen.prog csCallees.env) :
    Sat Gen.prog createStatementRef createStatementSpec := by
  intro args σ o hpre hm
  obtain ⟨res, ld, ls, lh, disp, st, ht, ab, cv, av, c, a, h0, hR, ⟨xc, rfl, hxc⟩, ⟨xa, rfl, hxa⟩, h1, h2, h3, h4,
    hini⟩ := hpre
  have hG := MethodVC.sat_of_valid hV (cs_vc ⟨res, ld, ls, lh, disp, st, ht, ab, xc, xa, c, a⟩) args σ o
    ⟨h0, hR, hxc, hxa, h1, h2, h3, h4, hini⟩ hm
  cases o with
  | normal r σ' =>
    intro res' ld' ls' lh' disp' st' ht' ab' cv' av' g0 g1
    rw [h0] at g0
    obtain ⟨hr, hc, ha⟩ : res = res' ∧ Value.ref xc = cv' ∧ Value.ref xa = av' := by simpa using g0
    subst hr hc ha
    have hG' := MethodVC.sat_of_valid hV (cs_vc ⟨res, ld', ls', lh', disp', st', ht', ab', xc, xa, c, a⟩) args σ
      (.normal r σ') ⟨h0, g1, hxc, hxa, h1, h2, h3, h4, hini⟩ hm
    have ec : argText σ (.ref xc) = c := by simp [argText, strOf, hxc]
    have ea : argText σ (.ref xa) = a := by simp [argText, strOf, hxa]
    rw [ec, ea]
    exact hG'
  | exc e σ' => exact hG.elim
  | wrong m => exact hG.elim

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.createStatement_sat
