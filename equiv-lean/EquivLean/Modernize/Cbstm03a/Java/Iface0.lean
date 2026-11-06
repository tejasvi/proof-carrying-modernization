import EquivLean.Modernize.Cbstm03a.JavaGen
import EquivLean.Modernize.Cbstm03b.Java.Base

/-!
# CBSTM03A → Java: the contracts shared by every part

The string helpers every method uses, with the texts of the CBSTM03B proofs (`fixStr`, `zpadStr`, `argText`,
`StrOk`, `Grows`): `repeat(ch, n)` (`n` copies of `ch`, none for `n ≤ 0`), `spaces(n)`, `fix(s, n)` (`s` cut or
space-padded to `n`, `null` as `""`), `zeroPad(v, n)` (the last `n` decimal digits of `v ≥ 0`). Results are new
objects (for `fix`: or the argument itself), so later updates of other objects cannot reach them.
A contract of a method that calls another method of `Cbstm03a` assumes `σ.initOf "Cbstm03a" = .done` (else the
call runs `<clinit>`); every post keeps `σ'.inits = σ.inits`, so callers thread it.
Convention for every contract of this program: string results `∃ x, r = some (.ref x) ∧ (σ.next ≤ x ∨ …) ∧
σ'.heap x = some (.str …) ∧ Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics`; methods that allocate
nothing: `σ' = σ`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

abbrev repeatRef : MethodRef := Gen.Cbstm03a.«repeat(char,int)».ref
abbrev spacesRef : MethodRef := Gen.Cbstm03a.«spaces(int)».ref
abbrev fixRef : MethodRef := Gen.Cbstm03a.«fix(java.lang.String,int)».ref
abbrev zeroPadRef : MethodRef := Gen.Cbstm03a.«zeroPad(long,int)».ref

def repeatSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "repeat", [.prim .char, .prim .int]⟩
def spacesSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "spaces", [.prim .int]⟩
def fixSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "fix", [.cls "java.lang.String", .prim .int]⟩
def zeroPadSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "zeroPad", [.prim .long, .prim .int]⟩

/-- `repeat(ch, n)`, `n ≤ 2^30` (the doubling loop's lengths stay `int`s): `n` copies of the character `ch` (the `int`
    argument's low 16 bits). -/
def repeatSpec : Spec := Spec.of
  (fun args _ => ∃ (ch n : I32), args = [.int ch, .int n] ∧ n.toInt ≤ 1073741824)
  (fun args σ r σ' => ∀ (ch n : I32), args = [.int ch, .int n] →
     ∃ x, r = some (.ref x) ∧ σ.next ≤ x ∧
       σ'.heap x = some (.str (List.replicate n.toInt.toNat (ch.setWidth 16))) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `spaces(n)`, `n ≤ 2^30`: `n` spaces (none for `n ≤ 0`). -/
def spacesSpec : Spec := Spec.of
  (fun args σ => ∃ n : I32, args = [.int n] ∧ n.toInt ≤ 1073741824 ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ n : I32, args = [.int n] →
     ∃ x, r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.str (List.replicate n.toInt.toNat space)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `fix(s, n)`: `s` (`""` for `null`) cut or space-padded to `0 ≤ n ≤ 2^30` characters. -/
def fixSpec : Spec := Spec.of
  (fun args σ => ∃ sv n, args = [sv, .int n] ∧ StrOk σ sv ∧ 0 ≤ n.toInt ∧ n.toInt ≤ 1073741824 ∧
     σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ sv n, args = [sv, .int n] →
     ∃ x, r = some (.ref x) ∧ (σ.next ≤ x ∨ sv = .ref x) ∧
       σ'.heap x = some (.str (fixStr (argText σ sv) n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `zeroPad(v, n)`: the last `n ≥ 0` decimal digits of `v ≥ 0`. -/
def zeroPadSpec : Spec := Spec.of
  (fun args _ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧ 0 ≤ v.toInt ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.str (zpadStr v.toNat n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

end EquivLean.Modernize.Cbstm03a.Java
