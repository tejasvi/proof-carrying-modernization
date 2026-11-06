import EquivLean.Modernize.Cbtrn02c.Any.JavaRunLib

/-!
# CBTRN02C → Java: `ebcdic`, `compareEbcdic`

`ebcdic(c)`: the EBCDIC byte of the CP037 character `c` (its index in the constant `CP037`,
which javac inlines).  `compareEbcdic(a, b)`: EBCDIC order of two strings of CP037 characters of
the same length (`Sem.cmpBytes` of their bytes): `-1`, `0`, `1`.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 100000 in
/-- The text of `CP037`: the CP037 character of each byte, in byte order. -/
theorem cp037Lit_eq : JStr.ofString "\u0000\u0001\u0002\u0003\u009c\u0009\u0086\u007f\u0097\u008d\u008e\u000b\u000c\u000d\u000e\u000f\u0010\u0011\u0012\u0013\u009d\u0085\u0008\u0087\u0018\u0019\u0092\u008f\u001c\u001d\u001e\u001f\u0080\u0081\u0082\u0083\u0084\u000a\u0017\u001b\u0088\u0089\u008a\u008b\u008c\u0005\u0006\u0007\u0090\u0091\u0016\u0093\u0094\u0095\u0096\u0004\u0098\u0099\u009a\u009b\u0014\u0015\u009e\u001a\u0020\u00a0\u00e2\u00e4\u00e0\u00e1\u00e3\u00e5\u00e7\u00f1\u00a2\u002e\u003c\u0028\u002b\u007c\u0026\u00e9\u00ea\u00eb\u00e8\u00ed\u00ee\u00ef\u00ec\u00df\u0021\u0024\u002a\u0029\u003b\u00ac\u002d\u002f\u00c2\u00c4\u00c0\u00c1\u00c3\u00c5\u00c7\u00d1\u00a6\u002c\u0025\u005f\u003e\u003f\u00f8\u00c9\u00ca\u00cb\u00c8\u00cd\u00ce\u00cf\u00cc\u0060\u003a\u0023\u0040\u0027\u003d\u0022\u00d8\u0061\u0062\u0063\u0064\u0065\u0066\u0067\u0068\u0069\u00ab\u00bb\u00f0\u00fd\u00fe\u00b1\u00b0\u006a\u006b\u006c\u006d\u006e\u006f\u0070\u0071\u0072\u00aa\u00ba\u00e6\u00b8\u00c6\u00a4\u00b5\u007e\u0073\u0074\u0075\u0076\u0077\u0078\u0079\u007a\u00a1\u00bf\u00d0\u00dd\u00de\u00ae\u005e\u00a3\u00a5\u00b7\u00a9\u00a7\u00b6\u00bc\u00bd\u00be\u005b\u005d\u00af\u00a8\u00b4\u00d7\u007b\u0041\u0042\u0043\u0044\u0045\u0046\u0047\u0048\u0049\u00ad\u00f4\u00f6\u00f2\u00f3\u00f5\u007d\u004a\u004b\u004c\u004d\u004e\u004f\u0050\u0051\u0052\u00b9\u00fb\u00fc\u00f9\u00fa\u00ff\u005c\u00f7\u0053\u0054\u0055\u0056\u0057\u0058\u0059\u005a\u00b2\u00d4\u00d6\u00d2\u00d3\u00d5\u0030\u0031\u0032\u0033\u0034\u0035\u0036\u0037\u0038\u0039\u00b3\u00db\u00dc\u00d9\u00da\u009f" =
    (List.range 256).map (fun k => cp037Unit (UInt8.ofNat k)) := by
  decide

/-! ### `ebcdic` -/

theorem tab_get (k : Nat) (hk : k < 256) (val : JChar)
    (hd : Option.map (fun k => cp037Unit (UInt8.ofNat k)) (List.range 256)[k]? = some val) :
    val = cp037Unit (UInt8.ofNat k) := by
  rw [List.getElem?_range hk, Option.map_some] at hd
  exact (Option.some.inj hd).symm

theorem ebcdic_found (w : I32) (b : UInt8) (val : JChar) (h0 : 0 ≤ w.toInt) (hk : w.toInt < 256)
    (hd : Option.map (fun k => cp037Unit (UInt8.ofNat k)) (List.range 256)[w.toInt.toNat]? = some val)
    (hc : val.setWidth 32 = (cp037Unit b).setWidth 32) : w = BitVec.ofNat 32 b.toNat := by
  have hk' : w.toInt.toNat < 256 := by omega
  rw [tab_get _ hk' val hd, cp037Unit_setWidth_iff, uint8_ofNat_eq_iff _ _ hk'] at hc
  apply BitVec.eq_of_toNat_eq
  rw [i32_toNat_eq w h0, hc, BitVec.toNat_ofNat]
  have := b.toNat_lt
  omega

theorem ebcdic_next (w : I32) (b : UInt8) (val : JChar) (h0 : 0 ≤ w.toInt) (hle : w.toInt ≤ b.toNat)
    (hk : w.toInt < 256)
    (hd : Option.map (fun k => cp037Unit (UInt8.ofNat k)) (List.range 256)[w.toInt.toNat]? = some val)
    (hc : ¬ val.setWidth 32 = (cp037Unit b).setWidth 32) : w.toInt + 1 ≤ b.toNat := by
  have hk' : w.toInt.toNat < 256 := by omega
  rw [tab_get _ hk' val hd, cp037Unit_setWidth_iff, uint8_ofNat_eq_iff _ _ hk'] at hc
  omega

abbrev ebcdicRef : MethodRef := Gen.Cbtrn02c.«ebcdic(char)».ref

def ebcdicSpec : Spec := Spec.of
  (fun args _ => ∃ b : UInt8, args = [.int ((cp037Unit b).setWidth 32)])
  (fun args σ r σ' => Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
     σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c" ∧ ∃ c : I32, r = some (.int c) ∧
     ∀ b : UInt8, args = [.int ((cp037Unit b).setWidth 32)] → c = BitVec.ofNat 32 b.toNat)

/-- At the loop head (statement 2): the byte of `c` is not below `i`. -/
def ebcdicInv : Invariants := [(2, fun args σ0 fr σ =>
  ∀ b : UInt8, args = [.int ((cp037Unit b).setWidth 32)] →
  ∃ i : I32, fr.get 0 = some (.int i) ∧ fr.get 3 = some (.int ((cp037Unit b).setWidth 32)) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ b.toNat ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧
    σ.statics = σ0.statics ∧ σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c")]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem ebcdic_vc : MethodVC Gen.prog (fun _ => none) 0 ebcdicRef ebcdicSpec ebcdicInv 40 := by
  jverify [ebcdicSpec, ebcdicInv, Grows, cp037Lit_eq]
  all_goals first
    | exact ebcdic_found _ _ _ (by assumption) (by assumption) hd hcond
    | (rename_i b hb
       rw [cp037Unit_setWidth_iff] at hb
       subst hb
       first
         | exact ebcdic_found _ _ _ (by assumption) (by assumption) hd hcond
         | exact ebcdic_next _ _ _ (by assumption) (by assumption) (by assumption) hd hcond)

/-! ### `compareEbcdic` -/

def ebcdicSig : MethodSig := ⟨"Cbtrn02c", .prim .int, "ebcdic", [.prim .char]⟩

theorem ebcdic_sat : Sat Gen.prog ebcdicRef ebcdicSpec := ebcdic_vc.sat

set_option maxHeartbeats 0 in
theorem ebcdic_ok : ContractOK Gen.prog ebcdicSig ebcdicSpec := by
  jcontract_ok [ebcdic_sat]

/-- What `compareEbcdic` returns for an EBCDIC comparison. -/
def cmpJ : Ordering → I32
  | .lt => 4294967295#32
  | .eq => 0#32
  | .gt => 1#32

theorem cmpBytes_drop_lt (xs ys : List UInt8) (i : Nat) (x y : UInt8) (hx : xs[i]? = some x)
    (hy : ys[i]? = some y) (h : x.toNat < y.toNat) :
    Cobol.Sem.cmpBytes (xs.drop i) (ys.drop i) = .lt := by
  have hi : i < xs.length := by
    rcases Nat.lt_or_ge i xs.length with h1 | h1
    · exact h1
    · rw [List.getElem?_eq_none h1] at hx; cases hx
  have hj : i < ys.length := by
    rcases Nat.lt_or_ge i ys.length with h1 | h1
    · exact h1
    · rw [List.getElem?_eq_none h1] at hy; cases hy
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj]
  rw [List.getElem?_eq_getElem hi] at hx; rw [List.getElem?_eq_getElem hj] at hy
  cases hx; cases hy
  simp only [Cobol.Sem.cmpBytes]
  have : xs[i] < ys[i] := UInt8.lt_iff_toNat_lt.mpr h
  simp [this]

theorem cmpBytes_drop_gt (xs ys : List UInt8) (i : Nat) (x y : UInt8) (hx : xs[i]? = some x)
    (hy : ys[i]? = some y) (h : y.toNat < x.toNat) :
    Cobol.Sem.cmpBytes (xs.drop i) (ys.drop i) = .gt := by
  have hi : i < xs.length := by
    rcases Nat.lt_or_ge i xs.length with h1 | h1
    · exact h1
    · rw [List.getElem?_eq_none h1] at hx; cases hx
  have hj : i < ys.length := by
    rcases Nat.lt_or_ge i ys.length with h1 | h1
    · exact h1
    · rw [List.getElem?_eq_none h1] at hy; cases hy
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj]
  rw [List.getElem?_eq_getElem hi] at hx; rw [List.getElem?_eq_getElem hj] at hy
  cases hx; cases hy
  simp only [Cobol.Sem.cmpBytes]
  have h1 : ¬ xs[i] < ys[i] := fun h' => by
    have : xs[i].toNat < ys[i].toNat := UInt8.lt_iff_toNat_lt.mp h'
    omega
  have h2 : ys[i] < xs[i] := UInt8.lt_iff_toNat_lt.mpr h
  simp [h1, h2]

theorem cmpBytes_drop_eq (xs ys : List UInt8) (i : Nat) (x y : UInt8) (hx : xs[i]? = some x)
    (hy : ys[i]? = some y) (h : x.toNat = y.toNat) :
    Cobol.Sem.cmpBytes (xs.drop i) (ys.drop i) = Cobol.Sem.cmpBytes (xs.drop (i + 1)) (ys.drop (i + 1)) := by
  have hi : i < xs.length := by
    rcases Nat.lt_or_ge i xs.length with h1 | h1
    · exact h1
    · rw [List.getElem?_eq_none h1] at hx; cases hx
  have hj : i < ys.length := by
    rcases Nat.lt_or_ge i ys.length with h1 | h1
    · exact h1
    · rw [List.getElem?_eq_none h1] at hy; cases hy
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj]
  rw [List.getElem?_eq_getElem hi] at hx; rw [List.getElem?_eq_getElem hj] at hy
  cases hx; cases hy
  have he : xs[i] = ys[i] := UInt8.toNat_inj.mp h
  have hn : ¬ ys[i] < ys[i] := fun h' => by
    have := UInt8.lt_iff_toNat_lt.mp h'
    omega
  simp only [Cobol.Sem.cmpBytes, he, hn, if_false]

theorem cmpBytes_drop_end (xs ys : List UInt8) (n : Nat) (h : xs.length = n) :
    Cobol.Sem.cmpBytes (xs.drop n) (ys.drop n) = .eq := by
  subst h; rw [List.drop_length]; cases ys.drop xs.length <;> rfl

theorem ce_exit (xs ys : List UInt8) (i n : I32) (hn : n.toInt = xs.length) (hle : i.toInt ≤ n.toInt)
    (hge : (ys.length : Int) ≤ i.toInt) (hl : xs.length = ys.length)
    (hinv : Cobol.Sem.cmpBytes xs ys =
      Cobol.Sem.cmpBytes (xs.drop i.toInt.toNat) (ys.drop i.toInt.toNat)) :
    0#32 = cmpJ (Cobol.Sem.cmpBytes xs ys) := by
  have : i.toInt.toNat = xs.length := by omega
  rw [hinv, this, cmpBytes_drop_end xs ys _ rfl]; rfl

theorem toInt_ofNat_u8 (b : UInt8) : (BitVec.ofNat 32 b.toNat).toInt = (b.toNat : Int) := by
  have := b.toNat_lt
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  split <;> omega

theorem ce_eq (xs ys : List UInt8) (k : Nat) (hk : k < xs.length) (hk' : k < ys.length)
    (hinv : Cobol.Sem.cmpBytes xs ys = Cobol.Sem.cmpBytes (xs.drop k) (ys.drop k))
    (h1 : ys[k].toNat ≤ xs[k].toNat) (h2 : xs[k].toNat ≤ ys[k].toNat) :
    Cobol.Sem.cmpBytes xs ys = Cobol.Sem.cmpBytes (xs.drop (k + 1)) (ys.drop (k + 1)) := by
  rw [hinv]
  exact cmpBytes_drop_eq xs ys k xs[k] ys[k] (List.getElem?_eq_getElem hk)
    (List.getElem?_eq_getElem hk') (by omega)

theorem ce_gt (xs ys : List UInt8) (k : Nat) (hk : k < xs.length) (hk' : k < ys.length)
    (hinv : Cobol.Sem.cmpBytes xs ys = Cobol.Sem.cmpBytes (xs.drop k) (ys.drop k))
    (h : ¬ xs[k].toNat ≤ ys[k].toNat) : 1#32 = cmpJ (Cobol.Sem.cmpBytes xs ys) := by
  rw [hinv, cmpBytes_drop_gt xs ys k xs[k] ys[k] (List.getElem?_eq_getElem hk)
    (List.getElem?_eq_getElem hk') (by omega)]; rfl

theorem ce_lt (xs ys : List UInt8) (k : Nat) (hk : k < xs.length) (hk' : k < ys.length)
    (hinv : Cobol.Sem.cmpBytes xs ys = Cobol.Sem.cmpBytes (xs.drop k) (ys.drop k))
    (h : ¬ ys[k].toNat ≤ xs[k].toNat) : 4294967295#32 = cmpJ (Cobol.Sem.cmpBytes xs ys) := by
  rw [hinv, cmpBytes_drop_lt xs ys k xs[k] ys[k] (List.getElem?_eq_getElem hk)
    (List.getElem?_eq_getElem hk') (by omega)]; rfl

abbrev compareEbcdicRef : MethodRef :=
  Gen.Cbtrn02c.«compareEbcdic(java.lang.String,java.lang.String)».ref

def ceCallees : Contracts := [(ebcdicSig, ebcdicSpec)]

def compareEbcdicSpec : Spec := Spec.of
  (fun args σ => ∃ (a b : Addr) (xs ys : List UInt8), args = [.ref a, .ref b] ∧
     σ.heap a = some (.str (cp037Str xs)) ∧ σ.heap b = some (.str (cp037Str ys)) ∧
     xs.length = ys.length ∧ xs.length < 2147483647 ∧ σ.initOf "Cbtrn02c" = .done)
  (fun args σ r σ' => Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
     σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c" ∧ ∃ c : I32, r = some (.int c) ∧
     ∀ (a b : Addr) (xs ys : List UInt8), args = [.ref a, .ref b] →
       σ.heap a = some (.str (cp037Str xs)) → σ.heap b = some (.str (cp037Str ys)) →
       c = cmpJ (Cobol.Sem.cmpBytes xs ys))

/-- At the loop head (statement 9): the comparison is decided by the bytes from `i` on. -/
def compareEbcdicInv : Invariants := [(9, fun args σ0 fr σ =>
  ∀ (a b : Addr) (xs ys : List UInt8), args = [.ref a, .ref b] →
  σ0.heap a = some (.str (cp037Str xs)) → σ0.heap b = some (.str (cp037Str ys)) →
  ∃ i n : I32, fr.get 2 = some (.int n) ∧ fr.get 3 = some (.int i) ∧ fr.get 6 = some (.ref a) ∧
    fr.get 7 = some (.ref b) ∧ n.toInt = xs.length ∧ 0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧
    xs.length = ys.length ∧ xs.length < 2147483647 ∧
    Cobol.Sem.cmpBytes xs ys = Cobol.Sem.cmpBytes (xs.drop i.toInt.toNat) (ys.drop i.toInt.toNat) ∧
    σ.heap a = some (.str (cp037Str xs)) ∧ σ.heap b = some (.str (cp037Str ys)) ∧
    Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c" ∧ σ.initOf "Cbtrn02c" = .done),
  (22, fun args σ0 fr σ =>
  ∀ (a b : Addr) (xs ys : List UInt8), args = [.ref a, .ref b] →
  σ0.heap a = some (.str (cp037Str xs)) → σ0.heap b = some (.str (cp037Str ys)) →
  ∃ (i n : I32) (hi : i.toInt.toNat < xs.length) (hj : i.toInt.toNat < ys.length),
    fr.get 2 = some (.int n) ∧ fr.get 3 = some (.int i) ∧ fr.get 6 = some (.ref a) ∧
    fr.get 7 = some (.ref b) ∧ fr.get 4 = some (.int (BitVec.ofNat 32 xs[i.toInt.toNat].toNat)) ∧
    fr.get 5 = some (.int (BitVec.ofNat 32 ys[i.toInt.toNat].toNat)) ∧
    n.toInt = xs.length ∧ 0 ≤ i.toInt ∧ i.toInt < n.toInt ∧
    xs.length = ys.length ∧ xs.length < 2147483647 ∧
    Cobol.Sem.cmpBytes xs ys = Cobol.Sem.cmpBytes (xs.drop i.toInt.toNat) (ys.drop i.toInt.toNat) ∧
    σ.heap a = some (.str (cp037Str xs)) ∧ σ.heap b = some (.str (cp037Str ys)) ∧
    Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c" ∧ σ.initOf "Cbtrn02c" = .done)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem compareEbcdic_vc :
    MethodVC Gen.prog ceCallees.env 0 compareEbcdicRef compareEbcdicSpec compareEbcdicInv 60 := by
  jverify [compareEbcdicSpec, compareEbcdicInv, ceCallees, ebcdicSig, ebcdicSpec, Grows, cp037Str,
    toInt_ofNat_u8]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip
  all_goals (try simp only [map_cp037Unit_iff] at *); (try subst_vars)
  all_goals first
    | omega
    | exact ce_exit _ _ _ _ (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption)
    | exact ⟨by omega, rfl⟩
    | (refine ⟨by omega, ?_⟩; apply_assumption; rfl)
    | exact ce_eq _ _ _ (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption)
    | exact ce_gt _ _ _ (by assumption) (by assumption) (by assumption) (by assumption)
    | exact ce_lt _ _ _ (by assumption) (by assumption) (by assumption) (by assumption)
    | skip

end EquivLean.Modernize.Cbtrn02c.Java
