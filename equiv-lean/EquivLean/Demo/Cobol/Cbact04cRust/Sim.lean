import EquivLean.Demo.Cobol.Cbact04cRust.RunLoop
import EquivLean.Demo.Cobol.Cbact04cRust.Pure
import EquivLean.Bridge.Cobol.Behaves
import EquivLean.Bridge.Aeneas.Behaves
import EquivLean.Repr.Corr

/-!
# COBOL → Rust migration: CardDemo's CBACT04C ≡ `cbact04c::run`, on every input

* **Source**: CBACT04C, the interest calculator of AWS CardDemo, unmodified (coblean's front end;
  the program and coblean's theorem `cbact04c_all` are in `EquivLean.Demo.Cobol.Cbact04c`).  Its
  meaning: `EquivLean.Cobol.run CardDemo.Cbact04c …` (five files, keyed reads, `REWRITE`).
* **Target**: `cbact04c::run(&[Cat], &[Account], &[Disc]) -> (Vec<Account>, u32)` of
  `examples/rust/cbact04c/src/lib.rs`, a port of the program's business logic in which the files
  are arguments and results; its Charon + Aeneas translation (`EquivLean/Demo/Gen/Aeneas/Cbact04c`,
  here `EquivLean.Demo.Gen.Aeneas.Cbact04c`).  Its meaning: `Aeneas.Std.Result` (bridge `EquivLean.Bridge.Aeneas.Behaves`:
  a panic is an outcome, total correctness).
* **Outcome relation** `CbRelR`: the COBOL run ends with `GOBACK`; the Rust function returns (no
  panic) rewritten accounts that are, in order, the COBOL program's `REWRITE` records decoded (id,
  balance, cycle credit and debit, group id as the big-endian value of its bytes: the fields the
  Rust `Account` holds), and a transaction count equal to the number of records the COBOL program
  writes to the transaction file.  Both rewrite every account but the last (the defect reported
  as CardDemo issue #64, kept by the port).

Proof chain:
1. COBOL: `cbact04c_all` (coblean): GOBACK, the rewrites `accs.dropLast.map (·.posted (totalInt …))`,
   `nTxA` transactions.
2. Rust: `run_eq` (`Cbact04cRust/RunLoop.lean`, with the callee specifications of `Cbact04cRust/Lookup.lean`):
   `run` returns `ok`, with the rewrites and the count of `rRun` (the loop as a fold).
3. `rRun_cbact04c` (`Cbact04cRust/Pure.lean`): `rRun` on the input records is coblean's specification.
4. `decodeAcctR_posted`: a posted record decodes to the Rust account's values.
-/

open Aeneas Aeneas.Std Result
open Cobol CardDemo.Cbact04c
open EquivLean (Sim)

namespace EquivLean.Demo.Cbact04cRust

/-! ## A rewritten account record, decoded -/

theorem drop_app {α : Type} (l₁ l₂ : List α) (n : Nat) (h : l₁.length ≤ n) :
    (l₁ ++ l₂).drop n = l₂.drop (n - l₁.length) := by
  induction l₁ generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.cons_append, List.drop_succ_cons, List.length_cons]
      rw [ih n (by simp at h; omega)]
      congr 1
      omega

theorem take_app {α : Type} (l₁ l₂ : List α) (n : Nat) (h : l₁.length = n) :
    (l₁ ++ l₂).take n = l₁ := List.take_left' h

/-- The values a Rust `Account` holds, read from an ACCOUNT-RECORD of 300 bytes (`CVACT01Y.cpy`):
`ACCT-ID` (offset 0), `ACCT-CURR-BAL` (12), `ACCT-CURR-CYC-CREDIT` (78), `ACCT-CURR-CYC-DEBIT`
(90), `ACCT-GROUP-ID` (112, 10 bytes, as a big-endian integer). -/
def decodeAcctR (rec : List UInt8) : Option RAcct := do
  let id ← decodeNum {} ACCT_ID.fmt (rec.take 11)
  let bal ← decodeNum {} ACCT_CURR_BAL.fmt ((rec.drop 12).take 12)
  let cc ← decodeNum {} ACCT_CURR_CYC_CREDIT.fmt ((rec.drop 78).take 12)
  let cd ← decodeNum {} ACCT_CURR_CYC_DEBIT.fmt ((rec.drop 90).take 12)
  some ⟨id, bal, cc, cd, beNat ((rec.drop 112).take 10)⟩

theorem decodeAcctR_posted (a : Acc) (ha : a.valid) (t : Int) :
    decodeAcctR (a.posted t) = some (rposted a t) := by
  obtain ⟨hid, hid0, hs, hbal, hmid, hcc, hcd, hzip, hgrp, haf, -⟩ := ha
  have l1 : (encodeNum {} ACCT_ID.fmt a.id).length = 11 := length_encodeNum _ _ _ (by decide)
  have l2 : ∀ v, (encodeNum {} ACCT_CURR_BAL.fmt v).length = 12 := fun v =>
    length_encodeNum _ _ _ (by decide)
  have l3 : ∀ v, (encodeNum {} ACCT_CURR_CYC_CREDIT.fmt v).length = 12 := fun v =>
    length_encodeNum _ _ _ (by decide)
  have l4 : ∀ v, (encodeNum {} ACCT_CURR_CYC_DEBIT.fmt v).length = 12 := fun v =>
    length_encodeNum _ _ _ (by decide)
  have d1 : decodeNum {} ACCT_ID.fmt (encodeNum {} ACCT_ID.fmt a.id) = some a.id :=
    decodeNum_encodeNum _ _ _ (by decide) (by decide) ⟨hid, fun _ => hid0⟩
  have hfit := fitNum_holds {} ACCT_CURR_BAL.fmt (a.bal + t)
  have d2 : decodeNum {} ACCT_CURR_BAL.fmt (encodeNum {} ACCT_CURR_BAL.fmt
      (Sem.fitNum {} ACCT_CURR_BAL.fmt (a.bal + t)).2) =
        some (Sem.fitNum {} ACCT_CURR_BAL.fmt (a.bal + t)).2 :=
    decodeNum_encodeNum _ _ _ (by decide) (by decide) hfit
  have d3 : decodeNum {} ACCT_CURR_CYC_CREDIT.fmt (encodeNum {} ACCT_CURR_CYC_CREDIT.fmt 0) =
      some 0 :=
    decodeNum_encodeNum _ _ _ (by decide) (by decide) ⟨by decide, fun _ => Int.le_refl _⟩
  have d4 : decodeNum {} ACCT_CURR_CYC_DEBIT.fmt (encodeNum {} ACCT_CURR_CYC_DEBIT.fmt 0) =
      some 0 :=
    decodeNum_encodeNum _ _ _ (by decide) (by decide) ⟨by decide, fun _ => Int.le_refl _⟩
  simp (disch := simp only [l1, l2, l3, l4, hs, hmid, hzip, hgrp]; decide) only [decodeAcctR,
    Acc.posted, List.append_assoc, drop_app, l1, l2, hs, hmid, hzip, Nat.reduceSub, List.drop_zero]
  rw [take_app _ _ _ l1, d1, take_app _ _ _ (l2 _), d2, take_app _ _ _ (l3 _), d3,
    take_app _ _ _ (l4 _), d4, take_app _ _ _ hgrp]
  rfl

/-! ## The Rust inputs -/

/-- The Rust inputs hold the records of the COBOL files: every category record's account and
disclosure group are found by key with the values `acctOf`, `rateOf` (`RunPre` without the field
bounds, which follow from coblean's hypotheses: `runPre_of`). -/
def Lookups (cats : Slice cbact04c.Cat) (accounts : Slice cbact04c.Account)
    (discs : Slice cbact04c.Disc) (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int) : Prop :=
  ∀ c ∈ cats.val,
    (∃ a ∈ accounts.val, a.id = c.acct_id) ∧
    (∀ a ∈ accounts.val, a.id = c.acct_id → RAcct.ofRust a = acctOf c.acct_id.val) ∧
    (∃ d ∈ discs.val, d.group_id.val = (acctOf c.acct_id.val).grp ∧ d.type_cd = c.type_cd ∧
      d.cat_cd = c.cat_cd) ∧
    (∀ d ∈ discs.val, d.group_id.val = (acctOf c.acct_id.val).grp → d.type_cd = c.type_cd →
      d.cat_cd = c.cat_cd → d.rate.val = rateOf (acctOf c.acct_id.val).grp c.type_cd.val c.cat_cd.val)

theorem runPre_of (accs : List Acc) (hval : ∀ a ∈ accs, a.valid)
    (hlen : (items accs).length < 999999) (rate : Acc → Cat → Int)
    (hrb : ∀ a ∈ accs, ∀ c ∈ a.cats, (rate a c).natAbs < 1000000)
    (cats : Slice cbact04c.Cat) (accounts : Slice cbact04c.Account) (discs : Slice cbact04c.Disc)
    (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int)
    (hcats : cats.val.map RCat.ofRust = rcats accs)
    (hlook : Lookups cats accounts discs acctOf rateOf)
    (hracct : ∀ a ∈ accs, acctOf a.id = racct a)
    (hrrate : ∀ a ∈ accs, ∀ c ∈ a.cats, rateOf (beNat a.grp) (beNat c.ty) c.cat = rate a c) :
    RunPre cats accounts discs acctOf rateOf := by
  refine ⟨?_, fun c hc => ?_⟩
  · have := congrArg List.length hcats
    simp only [List.length_map, rcats] at this
    rw [this, U32.max_eq]; omega
  · obtain ⟨hex, hall, hdex, hdall⟩ := hlook c hc
    have hmem : RCat.ofRust c ∈ rcats accs := hcats ▸ List.mem_map_of_mem hc
    simp only [rcats, List.mem_map] at hmem
    obtain ⟨⟨a, cat⟩, hp, hpc⟩ := hmem
    simp only [items, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hp
    obtain ⟨a', ha', cat', hcat', rfl, rfl⟩ := hp
    simp only [rcat, RCat.ofRust, RCat.mk.injEq] at hpc
    obtain ⟨h1, h2, h3, h4⟩ := hpc
    have hav := hval a' ha'
    have hcv : cat'.valid := hav.2.2.2.2.2.2.2.2.2.2.2.2 cat' hcat'
    have hacc : acctOf c.acct_id.val = racct a' := by rw [← h1]; exact hracct a' ha'
    refine ⟨by rw [← h4]; exact hcv.2.2.2.2, hex, hall, by rw [hacc]; exact hav.2.2.2.1, hdex, hdall,
      ?_⟩
    rw [hacc]
    simp only [racct]
    rw [← h2, ← h3, hrrate a' ha' cat' hcat']
    exact hrb a' ha' cat' hcat'

/-! ## The migration theorem -/

/-- The outcome relation (see the module doc). -/
def CbRelR (ot : Except Error (alloc.vec.Vec cbact04c.Account × Std.U32))
    (os : Cobol.Signal × Cobol.State) : Prop :=
  os.1 = .stop .goback ∧
  ∃ rw n, ot = .ok (rw, n) ∧
    EquivLean.ListRel (fun a rec => decodeAcctR rec = some (RAcct.ofRust a)) rw.val
      (acctRewrites os.2) ∧
    n.val = (tranWrites os.2).length

theorem listRel_decode {α β γ : Type} (dec : List UInt8 → Option γ) (f : α → γ) (g : β → γ)
    (h : β → List UInt8) :
    ∀ (l1 : List α) (l2 : List β), l1.map f = l2.map g → (∀ b ∈ l2, dec (h b) = some (g b)) →
      EquivLean.ListRel (fun a rec => dec rec = some (f a)) l1 (l2.map h)
  | [], [], _, _ => .nil
  | a :: l1, b :: l2, he, hd => by
    simp only [List.map_cons, List.cons.injEq] at he
    exact .cons (by rw [hd b (List.mem_cons_self ..), he.1])
      (listRel_decode dec f g h l1 l2 he.2 (fun b' hb' => hd b' (List.mem_cons_of_mem _ hb')))
  | [], _ :: _, he, _ => by simp at he
  | _ :: _, [], he, _ => by simp at he

/-- Both programs on one input: the COBOL run (it ends with `GOBACK`) and the Rust result
(`ok`, no panic), related by `CbRelR`. -/
theorem cbact04c_rust_post (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
    (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧
      0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post)
    (accs : List Acc) (hval : ∀ a ∈ accs, a.valid)
    (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) (hlen : (items accs).length < 999999)
    (accts xrefs discs : List (List UInt8)) (ai xi : Acc → Nat)
    (hacct : ∀ a ∈ accs, Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt a.id)
      accts = some (ai a) ∧ accts.getD (ai a) [] = a.bytes)
    (hxref : ∀ a ∈ accs, Sem.findKey { off := 25, len := 11 }
      (encodeNum {} FD_XREF_ACCT_ID.fmt a.id) xrefs = some (xi a) ∧ xrefs.getD (xi a) [] = a.xrec)
    (rate : Acc → Cat → Int) (di : Acc → Cat → Nat) (dfill : Acc → Cat → List UInt8)
    (hdisc : ∀ a ∈ accs, ∀ c ∈ a.cats, Sem.findKey { off := 0, len := 16 }
        (a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat) discs = some (di a c) ∧
      discs.getD (di a c) [] = a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat ++
        encodeNum {} DIS_INT_RATE.fmt (rate a c) ++ dfill a c ∧
      (dfill a c).length = 28 ∧ (rate a c).natAbs < 1000000)
    (n : Nat) (hn : (items accs).length < n)
    -- the same records as Rust values
    (cats : Slice cbact04c.Cat) (accounts : Slice cbact04c.Account) (rdiscs : Slice cbact04c.Disc)
    (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int)
    (hcats : cats.val.map RCat.ofRust = rcats accs)
    (hlook : Lookups cats accounts rdiscs acctOf rateOf)
    (hracct : ∀ a ∈ accs, acctOf a.id = racct a)
    (hrrate : ∀ a ∈ accs, ∀ c ∈ a.cats, rateOf (beNat a.grp) (beNat c.ty) c.cat = rate a c) :
    ∃ rw k, cbact04c.run cats accounts rdiscs = ok (rw, k) ∧
      CbRelR (.ok (rw, k)) (CardDemo.Cbact04c.run { clock := clk } (n + 60)
        (CardDemo.Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)),
          (2, xrefs), (3, accts), (4, discs)])) := by
  obtain ⟨hstop, hrw, htw⟩ := cbact04c_all m hm clk hclk accs hval hdist hlen accts xrefs discs ai xi
    hacct hxref rate di dfill hdisc n hn
  have hpre := runPre_of accs hval hlen rate (fun a ha c hc => (hdisc a ha c hc).2.2.2) cats
    accounts rdiscs acctOf rateOf hcats hlook hracct hrrate
  obtain ⟨rw, k, hrun, hrwv, hkv⟩ := run_eq cats accounts rdiscs acctOf rateOf hpre
  have hok : ∀ a ∈ accs, AccOk rate acctOf rateOf a := fun a ha =>
    ⟨(hval a ha).2.2.2.2.2.2.2.2.2.2.2.1, hracct a ha, hrrate a ha⟩
  obtain ⟨hsr, hst⟩ := rRun_cbact04c rate acctOf rateOf accs hok hdist
  rw [hcats, hsr] at hrwv
  rw [hcats, hst] at hkv
  refine ⟨rw, k, hrun, hstop, rw, k, rfl, ?_, by rw [hkv, htw]⟩
  rw [hrw]
  exact listRel_decode decodeAcctR RAcct.ofRust (fun a => rposted a (totalInt (rate a) a.cats))
    (fun a => a.posted (totalInt (rate a) a.cats)) rw.val accs.dropLast hrwv (fun a ha =>
      decodeAcctR_posted a (hval a (by rw [List.dropLast_eq_take] at ha; exact List.mem_of_mem_take ha))
        _)

/-- **CardDemo's CBACT04C (COBOL) → `cbact04c::run` (Rust, Charon + Aeneas), on every input**:
for every input of coblean's `cbact04c_all` (any accounts with distinct keys, each with any
category balances, account, cross-reference and disclosure-group records found by key, any rates,
any storage, any clock) and Rust slices holding the same records (`hcats`: the category records
in file order; `hlook`: every lookup of the Rust code finds the account and the rate of the COBOL
input), `Sim CbRelR (Rust) (COBOL)`: the COBOL program ends with `GOBACK`, and the Rust function
returns without panicking, in order, the COBOL program's `REWRITE` records (decoded) and its number
of transaction records. -/
theorem cbact04c_rust_sim (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
    (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧
      0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post)
    (accs : List Acc) (hval : ∀ a ∈ accs, a.valid)
    (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) (hlen : (items accs).length < 999999)
    (accts xrefs discs : List (List UInt8)) (ai xi : Acc → Nat)
    (hacct : ∀ a ∈ accs, Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt a.id)
      accts = some (ai a) ∧ accts.getD (ai a) [] = a.bytes)
    (hxref : ∀ a ∈ accs, Sem.findKey { off := 25, len := 11 }
      (encodeNum {} FD_XREF_ACCT_ID.fmt a.id) xrefs = some (xi a) ∧ xrefs.getD (xi a) [] = a.xrec)
    (rate : Acc → Cat → Int) (di : Acc → Cat → Nat) (dfill : Acc → Cat → List UInt8)
    (hdisc : ∀ a ∈ accs, ∀ c ∈ a.cats, Sem.findKey { off := 0, len := 16 }
        (a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat) discs = some (di a c) ∧
      discs.getD (di a c) [] = a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat ++
        encodeNum {} DIS_INT_RATE.fmt (rate a c) ++ dfill a c ∧
      (dfill a c).length = 28 ∧ (rate a c).natAbs < 1000000)
    (n : Nat) (hn : (items accs).length < n)
    -- the same records as Rust values
    (cats : Slice cbact04c.Cat) (accounts : Slice cbact04c.Account) (rdiscs : Slice cbact04c.Disc)
    (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int)
    (hcats : cats.val.map RCat.ofRust = rcats accs)
    (hlook : Lookups cats accounts rdiscs acctOf rateOf)
    (hracct : ∀ a ∈ accs, acctOf a.id = racct a)
    (hrrate : ∀ a ∈ accs, ∀ c ∈ a.cats, rateOf (beNat a.grp) (beNat c.ty) c.cat = rate a c) :
    Sim CbRelR (cbact04c.run cats accounts rdiscs)
      (EquivLean.Cobol.run CardDemo.Cbact04c { clock := clk } (n + 60)
        (CardDemo.Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)),
          (2, xrefs), (3, accts), (4, discs)])) := by
  obtain ⟨rw, k, hrun, hrel⟩ := cbact04c_rust_post m hm clk hclk accs hval hdist hlen accts xrefs discs ai xi hacct hxref rate di dfill
    hdisc n hn cats accounts rdiscs acctOf rateOf hcats hlook hracct hrrate
  rw [EquivLean.Cobol.run, EquivLean.Cobol.sim_exec_iff]
  intro _
  rw [hrun, EquivLean.Aeneas.wp_ok]
  exact hrel

/-- **The same in both directions** (`Equiv`): the Rust function is total and deterministic, so
the simulation holds both ways (the COBOL run is safe: it ends with `GOBACK`). -/
theorem cbact04c_rust_equiv (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
    (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧
      0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post)
    (accs : List Acc) (hval : ∀ a ∈ accs, a.valid)
    (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) (hlen : (items accs).length < 999999)
    (accts xrefs discs : List (List UInt8)) (ai xi : Acc → Nat)
    (hacct : ∀ a ∈ accs, Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt a.id)
      accts = some (ai a) ∧ accts.getD (ai a) [] = a.bytes)
    (hxref : ∀ a ∈ accs, Sem.findKey { off := 25, len := 11 }
      (encodeNum {} FD_XREF_ACCT_ID.fmt a.id) xrefs = some (xi a) ∧ xrefs.getD (xi a) [] = a.xrec)
    (rate : Acc → Cat → Int) (di : Acc → Cat → Nat) (dfill : Acc → Cat → List UInt8)
    (hdisc : ∀ a ∈ accs, ∀ c ∈ a.cats, Sem.findKey { off := 0, len := 16 }
        (a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat) discs = some (di a c) ∧
      discs.getD (di a c) [] = a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat ++
        encodeNum {} DIS_INT_RATE.fmt (rate a c) ++ dfill a c ∧
      (dfill a c).length = 28 ∧ (rate a c).natAbs < 1000000)
    (n : Nat) (hn : (items accs).length < n)
    -- the same records as Rust values
    (cats : Slice cbact04c.Cat) (accounts : Slice cbact04c.Account) (rdiscs : Slice cbact04c.Disc)
    (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int)
    (hcats : cats.val.map RCat.ofRust = rcats accs)
    (hlook : Lookups cats accounts rdiscs acctOf rateOf)
    (hracct : ∀ a ∈ accs, acctOf a.id = racct a)
    (hrrate : ∀ a ∈ accs, ∀ c ∈ a.cats, rateOf (beNat a.grp) (beNat c.ty) c.cat = rate a c) :
    EquivLean.Equiv CbRelR (cbact04c.run cats accounts rdiscs)
      (EquivLean.Cobol.run CardDemo.Cbact04c { clock := clk } (n + 60)
        (CardDemo.Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)),
          (2, xrefs), (3, accts), (4, discs)])) := by
  obtain ⟨rw, k, hrun, hrel⟩ := cbact04c_rust_post m hm clk hclk accs hval hdist hlen accts xrefs discs ai xi hacct hxref rate di dfill
    hdisc n hn cats accounts rdiscs acctOf rateOf hcats hlook hracct hrrate
  have hsim := cbact04c_rust_sim m hm clk hclk accs hval hdist hlen accts xrefs discs ai xi hacct hxref rate di dfill
    hdisc n hn cats accounts rdiscs acctOf rateOf hcats hlook hracct hrrate
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbact04c.run { clock := clk } (n + 60)
      (CardDemo.Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)),
        (2, xrefs), (3, accts), (4, discs)])) := by
    rw [EquivLean.Cobol.Ok, hrel.1]; rfl
  rw [EquivLean.Cobol.run] at hsim ⊢
  refine ⟨hsim, fun _ => ⟨(EquivLean.Cobol.safe_exec_iff _).2 hok, fun os hos => ⟨.ok (rw, k), ?_, ?_⟩⟩⟩
  · rw [EquivLean.Aeneas.runs_iff, hrun]; rfl
  · obtain ⟨h1, -⟩ := (EquivLean.Cobol.runs_exec_iff _ _).1 hos
    rw [h1]
    exact hrel

end EquivLean.Demo.Cbact04cRust

#print axioms EquivLean.Demo.Cbact04cRust.cbact04c_rust_sim
#print axioms EquivLean.Demo.Cbact04cRust.cbact04c_rust_equiv
