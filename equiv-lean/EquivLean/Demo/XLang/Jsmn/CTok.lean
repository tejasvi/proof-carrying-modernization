import EquivLean.Demo.XLang.Jsmn.CBase

/-!
# jsmn → model, C side: `jsmn_alloc_token` and `jsmn_fill_token`

Partial contracts (`pholds`: every `ok` outcome satisfies the post) for the two token helpers, over
the C memory: the parser is a `jsmn_parser` block holding `parserV pos toknext toksuper`, the tokens
an array block `.arr vs` whose elements are `jsmntok` aggregates (in a run, `tokArr ts n`).

* `jsmn_alloc_token_pspec`: `NULL` when `N ≤ toknext`; otherwise `&tokens[toknext]`, `toknext + 1`,
  and that token gets `start = end = -1`, `size = 0` (its `type` is kept).
* `jsmn_fill_token_pspec`: the token becomes `tokV ⟨type, start, end, 0⟩`.
-/

open CIR EquivLean.Cir
open EquivLean.Demo.XLang.Jsmn (Tok)
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx)

set_option maxHeartbeats 40000000

namespace EquivLean.Demo.XLang.Jsmn.C

/-- `jsmn_fill_token(&tokens[k], type, start, end)`: token `k` becomes `{type, start, end, 0}`. -/
theorem jsmn_fill_token_pspec (m : Mem) (bt k : Nat) (kt : BlockKind) (n : Nat) (vs : List Val)
    (ty st en : Int) (a0 b0 c0 d0 : Val)
    (ht : m.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr vs⟩) (hkt : kt ≠ .readonly)
    (hk : vs[k]? = some (.agg [a0, b0, c0, d0])) (hbt : bt < m.next) :
    pholds (evalCall ctx "jsmn_fill_token" [.ptr (.loc bt [.idx k]), .int ty, .int st, .int en] m)
      (fun a => a.1 = .ret none ∧
        a.2.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (vs.set k (tokV ⟨ty, st, en, 0⟩))⟩ ∧
        (∀ b, b ≠ bt → b < m.next → a.2.blocks b = m.blocks b) ∧ m.next ≤ a.2.next) := by
  intro r hr
  have hs : (evalCall ctx "jsmn_fill_token" [.ptr (.loc bt [.idx k]), .int ty, .int st, .int en]
      m).holds (· = r) := by rw [hr]; rfl
  have cirH_t := ht
  have cirH_kt := hkt
  have cirH_k := hk
  cir_hstep hs
  cir_hrun_c hs
  subst hs
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_same]; rfl
  · intro b hb1 hb2
    simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne]
  · simp only [Mem.endScope]; omega

/-- `jsmn_alloc_token(parser, tokens, N)` with `parser->toknext = tn`: `NULL` when `N ≤ tn`;
otherwise `&tokens[tn]`, `toknext = tn + 1`, and token `tn` gets `start = end = -1`, `size = 0`
(its `type` is kept). -/
theorem jsmn_alloc_token_pspec (m : Mem) (bp bt : Nat) (kp kt : BlockKind) (pos tn : Nat)
    (sup : Int) (N : Nat) (vs : List Val) (a0 b0 c0 d0 : Val)
    (hp : m.blocks bp = some ⟨kp, true, .record "jsmn_parser", parserV pos tn sup⟩)
    (ht : m.blocks bt = some ⟨kt, true, .array (.record "jsmntok") N, .arr vs⟩)
    (hkp : kp ≠ .readonly) (hkt : kt ≠ .readonly) (hpt : bp ≠ bt) (hlen : N ≤ vs.length)
    (hN : N < 2 ^ 32)
    (htok : tn < N → vs[tn]? = some (.agg [a0, b0, c0, d0]))
    (hbp : bp < m.next) (hbt : bt < m.next) :
    pholds (evalCall ctx "jsmn_alloc_token" [.ptr (.loc bp []), .ptr (.loc bt [.idx 0]), .int N] m)
      (fun a => m.next ≤ a.2.next ∧ (∀ b, b ≠ bp → b ≠ bt → b < m.next → a.2.blocks b = m.blocks b) ∧
        if N ≤ tn then a.1 = .ret (some (.ptr .null)) ∧ a.2.blocks bp = m.blocks bp ∧
          a.2.blocks bt = m.blocks bt
        else a.1 = .ret (some (.ptr (.loc bt [.idx tn]))) ∧
          a.2.blocks bp = some ⟨kp, true, .record "jsmn_parser", parserV pos (tn + 1) sup⟩ ∧
          a.2.blocks bt = some ⟨kt, true, .array (.record "jsmntok") N, .arr (vs.set tn (.agg [a0, .int (-1), .int (-1), .int 0]))⟩) := by
  intro r hr
  have hs : (evalCall ctx "jsmn_alloc_token" [.ptr (.loc bp []), .ptr (.loc bt [.idx 0]), .int N]
      m).holds (· = r) := by rw [hr]; rfl
  unfold parserV at hp ⊢
  have cirH_p := hp
  have cirH_t := ht
  have cirH_kp := hkp
  have cirH_kt := hkt
  have cirH_pt := hpt
  by_cases hc : N ≤ tn
  · have cirH_le : (N : Int) ≤ (tn : Int) := by omega
    cir_hstep hs
    cir_hrun_c hs
    all_goals (
      subst hs
      simp only [hc, ↓reduceIte]
      refine ⟨by (try simp only [Mem.endScope]); omega, ?_, trivial, ?_, ?_⟩
      · intro b hb1 hb2 hb3
        simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne]
      · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne]
      · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne])
  · have cirH_lt : ¬((N : Int) ≤ (tn : Int)) := by omega
    have cirH_tok := htok (by omega)
    have cirH_tn : tn < vs.length := by omega
    have cirH_i0 : (0 + (tn : Int)).toNat = tn := by omega
    have cirH_tokE : ∀ h : tn < vs.length, vs[tn] = .agg [a0, b0, c0, d0] := fun h => by
      rw [List.getElem?_eq_getElem h] at cirH_tok; exact Option.some.inj cirH_tok
    cir_hstep hs
    cir_hrun_c hs
    all_goals first
      | omega
      | (subst hs
         simp only [hc, ↓reduceIte]
         have h1 : ((tn + 1 : Nat) : Int) = (tn : Int) + 1 := by omega
         refine ⟨by (try simp only [Mem.endScope]); omega, ?_, trivial, ?_, ?_⟩
         · intro b hb1 hb2 hb3
           simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne]
         · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same, h1]
         · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same])

/-- In a run's token array, `jsmn_alloc_token` then `jsmn_fill_token` at `toknext = ts.length`
append the filled token. -/
theorem tokArr_alloc_fill (ts : List Tok) (n : Nat) (t : Tok) (h : ts.length < n) :
    ((tokArr ts n).set ts.length (.agg [.undef, .int (-1), .int (-1), .int 0])).set ts.length (tokV t) =
      tokArr (ts ++ [t]) n := by
  rw [List.set_set]; exact tokArr_push ts n t h

end EquivLean.Demo.XLang.Jsmn.C
