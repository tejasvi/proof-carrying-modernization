/-
# Proof layer: basic lemmas

* `Except` monad normal forms (`pure` = `.ok`, `throw` = `.error`, binds reduce);
* the stored value of a numeric item is always in range (`fitNum_holds`), hence reading
  back what was stored gives the stored value (`decodeNum_encodeNum_fitNum`);
* state-level read/write lemmas lifting `Mem.read_write_*`.
-/
import Cobol.Sem.Exec
import Cobol.Logic.Attr

namespace Cobol

/-! ## `Except` normal forms -/

@[simp, cobol_eval ↓] theorem Except.pure_eq_ok' {ε α : Type _} (x : α) :
    (pure x : Except ε α) = .ok x := rfl
@[simp, cobol_eval ↓] theorem Except.throw_eq_error' {ε α : Type _} (e : ε) :
    (throw e : Except ε α) = .error e := rfl
@[simp, cobol_eval ↓] theorem Except.ok_bind' {ε α β : Type _} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl
@[simp, cobol_eval ↓] theorem Except.error_bind' {ε α β : Type _} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f : Except ε β) = .error e := rfl
@[simp, cobol_eval] theorem Except.map_ok' {ε α β : Type _} (f : α → β) (x : α) :
    (f <$> (Except.ok x : Except ε α)) = .ok (f x) := rfl
@[simp, cobol_eval] theorem Except.map_error' {ε α β : Type _} (f : α → β) (e : ε) :
    (f <$> (Except.error e : Except ε α)) = .error e := rfl

attribute [cobol_eval] Except.pure_eq_ok' Except.throw_eq_error' Except.ok_bind' Except.error_bind'

/-! ## Stored values are in range -/

theorem wrapBin_range {n : Nat} (hn : 0 < n) (signed : Bool) (v : Int) :
    BinRange n signed (Sem.wrapBin n signed v) := by
  have h2 := binMod_eq_two_mul hn
  have hM : (0 : Int) < binMod n := by have := binMod_pos n; omega
  unfold BinRange Sem.wrapBin
  cases signed <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hM⟩
  · have := Int.emod_nonneg (v + binHalf n) (b := (binMod n : Int)) (by omega)
    have := Int.emod_lt_of_pos (v + binHalf n) hM
    constructor <;> omega

theorem fitDec_lt (n : Nat) (v : Int) : (Sem.fitDec n v).2.natAbs < 10 ^ n := by
  unfold Sem.fitDec
  split
  · assumption
  · have h := fitsDigits_truncDigits v n
    unfold FitsDigits at h
    have e : ((10 ^ n : Nat) : Int) = (10 : Int) ^ n := by simp
    simp only
    omega

theorem fitDec_nonneg (n : Nat) {v : Int} (hv : 0 ≤ v) : 0 ≤ (Sem.fitDec n v).2 := by
  unfold Sem.fitDec truncDigits
  have hp : (0 : Int) < 10 ^ n := Int.pow_pos (by decide)
  split
  · exact hv
  · exact Int.emod_nonneg _ (by omega)

theorem fitBin_range {n : Nat} (hn : 0 < n) (signed : Bool) (v : Int) :
    BinRange n signed (Sem.fitBin n signed v).2 := by
  unfold Sem.fitBin
  split
  · rename_i h
    unfold Sem.inBinRange at h
    unfold BinRange
    cases signed <;> simpa using h
  · exact wrapBin_range hn signed v

theorem fitNum_holds (c : Config) (f : NumFmt) (v : Int) :
    f.Holds c (Sem.fitNum c f v).2 := by
  have hpos := binBytes_pos c f.digits
  unfold Sem.fitNum NumFmt.Holds
  cases hfb : f.fullBinary c <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · refine ⟨fitDec_lt _ _, fun hs => ?_⟩
    simp only [hs, Bool.false_eq_true, ↓reduceIte]
    exact fitDec_nonneg _ (by omega)
  · have := fitBin_range hpos f.signed (if f.signed = true then v else (v.natAbs : Int))
    unfold BinRange at this
    exact this

@[simp, cobol_eval] theorem decodeNum_encodeNum_fitNum (c : Config) (f : NumFmt) (v : Int)
    (hd : 0 < f.digits) (hd18 : f.digits ≤ 18) :
    decodeNum c f (encodeNum c f (Sem.fitNum c f v).2) = some (Sem.fitNum c f v).2 :=
  decodeNum_encodeNum c f _ hd hd18 (fitNum_holds c f v)

/-! ## Reading after writing, at the state level -/

@[simp, cobol_eval] theorem State.mem_writeBytes (st : State) (d : FieldDesc) (bs : List UInt8) :
    (Sem.writeBytes st d bs).mem = st.mem.write d.off bs := rfl

attribute [cobol_eval] Mem.size_write Mem.length_read length_encodeNum

/-- Same field: the bytes just written (lengths agree, in bounds). -/
@[cobol_eval] theorem Mem.read_write_same' (m : Mem) (off len : Nat) (bs : List UInt8)
    (hl : bs.length = len) (hs : off + len ≤ m.size) : (m.write off bs).read off len = bs :=
  Mem.read_write_same m off len bs hl hs

/-- Disjoint fields: the write is invisible. -/
@[cobol_eval] theorem Mem.read_write_disjoint' (m : Mem) (off1 off2 len2 : Nat) (bs : List UInt8)
    (h : off2 + len2 ≤ off1 ∨ off1 + bs.length ≤ off2) :
    (m.write off1 bs).read off2 len2 = m.read off2 len2 :=
  Mem.read_write_disjoint m off1 off2 len2 bs h

/-- A field inside the field just written (a `REDEFINES` view of part of it): a slice. -/
@[cobol_eval low] theorem Mem.read_write_within' (m : Mem) (off1 off2 len2 : Nat) (bs : List UInt8)
    (h1 : off1 ≤ off2) (h2 : off2 + len2 ≤ off1 + bs.length) (hs : off1 + bs.length ≤ m.size) :
    (m.write off1 bs).read off2 len2 = (bs.drop (off2 - off1)).take len2 :=
  Mem.read_write_within m off1 off2 len2 bs h1 h2 hs

/-- A group (or record) read that contains the field just written: the bytes before it, the
written bytes, the bytes after it (`WRITE` of a record after `MOVE`s to its fields). -/
@[cobol_eval low] theorem Mem.read_write_inner' (m : Mem) (o1 o2 n : Nat) (bs : List UInt8)
    (h1 : o2 ≤ o1) (h2 : o1 + bs.length ≤ o2 + n) (hs : o1 + bs.length ≤ m.size) :
    (m.write o1 bs).read o2 n =
      m.read o2 (o1 - o2) ++ bs ++ m.read (o1 + bs.length) (o2 + n - (o1 + bs.length)) := by
  have e : n = (o1 - o2) + (bs.length + (o2 + n - (o1 + bs.length))) := by omega
  have h := Mem.read_append (m.write o1 bs) o2 (o1 - o2) (bs.length + (o2 + n - (o1 + bs.length)))
  rw [← e, show o2 + (o1 - o2) = o1 by omega, Mem.read_append] at h
  rw [h, Mem.read_write_disjoint _ _ _ _ _ (Or.inl (by omega)),
    Mem.read_write_same _ _ _ _ rfl hs, Mem.read_write_disjoint _ _ _ _ _ (Or.inr (by omega)),
    List.append_assoc]

@[cobol_eval] theorem Mem.read_zero (m : Mem) (o : Nat) : m.read o 0 = [] := rfl

/-- A read inside a region whose contents are known: the slice.  `Mem.read_of_read_sub h`
with `h : m.read o n = bs` (say, a whole record in a loop invariant) answers every read of a
field of the region during symbolic execution (its range side conditions are literal). -/
theorem Mem.read_of_read_sub {m : Mem} {o n : Nat} {bs : List UInt8} (h : m.read o n = bs)
    {o' n' : Nat} (h1 : o ≤ o') (h2 : o' + n' ≤ o + n) :
    m.read o' n' = (bs.drop (o' - o)).take n' := by
  subst h
  apply List.ext_getElem
  · simp; omega
  · intro i h3 h4
    simp only [Mem.length_read] at h3
    simp only [List.getElem_take, List.getElem_drop, Mem.getElem_read]
    congr 1
    omega

end Cobol
