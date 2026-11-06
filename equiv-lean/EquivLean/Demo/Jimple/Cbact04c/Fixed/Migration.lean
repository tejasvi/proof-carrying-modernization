import EquivLean.Demo.Jimple.Cbact04c.Migration
import EquivLean.Demo.Jimple.Cbact04c.PureFix
import EquivLean.Demo.Jimple.Cbact04c.Fixed.JavaRun
import EquivLean.Demo.Jimple.Cbact04c.Fixed.NonVacuous

/-!
# COBOL → Java with the defect fixed: CBACT04C against `Cbact04cFixed.run`, on every input

The port of `Cbact04c/Migration.lean` keeps CardDemo's defect (issue #64: the last account in the
file is never rewritten).  `examples/java/cbact04c_fixed/Cbact04cFixed.java` fixes it: after the
loop it posts the current account.  The fixed port does not simulate the COBOL program under
`CbRel`; it simulates it under `CbRelFix extra`, where the rewritten accounts are the COBOL
program's `REWRITE` records followed by `extra`, and `extra` is `missedRewrite rate accs`: the last
account posted with its interest, by coblean's own `Acc.posted` (the record `1050-UPDATE-ACCOUNT`
would write for it).  So the fix changes exactly the defect and nothing else: the other rewrites,
their order and the transaction count are those of the unmodified COBOL program.

Proof chain: `cbact04c_all` (COBOL); `runFix_sat` (`Cbact04c/Fixed/JavaRun.lean`: every terminating
run returns `jRunFix`); `jRunFix_cbact04c` (`Cbact04c/PureFix.lean`: `jRunFix` posts every
account); `decodeAcct_posted`.  Not vacuous: `cbact04c_fixed_sim_exists` (`runPreF_exists`).
-/

open Cobol CardDemo.Cbact04c Jimple EquivLean.Jimple

namespace EquivLean.Demo.Cbact04c

/-- The record the COBOL program does not write: the last account posted with its interest
(`Acc.posted`); none for an empty file. -/
def missedRewrite (rate : Acc → Cat → Int) (accs : List Acc) : List (List UInt8) :=
  match accs.getLast? with
  | none => []
  | some a => [a.posted (totalInt (rate a) a.cats)]

theorem dropLast_map_append_missed (rate : Acc → Cat → Int) (accs : List Acc) :
    accs.dropLast.map (fun a => a.posted (totalInt (rate a) a.cats)) ++ missedRewrite rate accs =
      accs.map (fun a => a.posted (totalInt (rate a) a.cats)) := by
  by_cases hne : accs = []
  · subst hne; rfl
  · conv => rhs; rw [← List.dropLast_concat_getLast hne]
    simp [missedRewrite, List.getLast?_eq_some_getLast hne]

/-- The outcome relation for the fixed port: `CbRel` with the rewritten accounts the COBOL
program's `REWRITE` records followed by `extra`. -/
def CbRelFix (extra : List (List UInt8)) (ot : Out) (os : Signal × Cobol.State) : Prop :=
  os.1 = .stop .goback ∧
  ∃ σ' res fs l k xs mods, ot = .normal (some (.ref res)) σ' ∧
    σ'.heap res = some (.plain "Cbact04cFixed$Result" fs) ∧
    Fields.get fs ("Cbact04cFixed$Result", "rewrites") = some (.ref l) ∧
    σ'.heap l = some (.list k xs mods) ∧
    Pairs (fun x rec => ∃ ja, AcctAtC "Cbact04cFixed$Account" σ' x ja ∧ decodeAcct rec = some ja)
      xs (acctRewrites os.2 ++ extra) ∧
    Fields.get fs ("Cbact04cFixed$Result", "transactions") =
      some (.int (BitVec.ofNat 32 (tranWrites os.2).length))

theorem pairs_map_dec {R : Jimple.Value → JAcct → Prop} {xs : List Jimple.Value} {L : List Acc}
    {f : Acc → JAcct} {g : Acc → List UInt8} (hdec : ∀ a ∈ L, decodeAcct (g a) = some (f a))
    (h : Pairs R xs (L.map f)) :
    Pairs (fun x rec => ∃ ja, R x ja ∧ decodeAcct rec = some ja) xs (L.map g) := by
  induction L generalizing xs with
  | nil => cases xs <;> simp_all [Pairs]
  | cons a L ih =>
    cases xs with
    | nil => simp [Pairs] at h
    | cons x xs =>
      simp only [List.map_cons, Pairs] at h ⊢
      exact ⟨⟨f a, h.1, hdec a (List.mem_cons_self ..)⟩,
        ih (fun b hb => hdec b (List.mem_cons_of_mem _ hb)) h.2⟩

/-- The run of `run(cats, accounts, discs)` of the fixed port. -/
abbrev runFixRef : MethodRef :=
  GenF.Cbact04cFixed.«run(Cbact04cFixed$Cat[],Cbact04cFixed$Account[],Cbact04cFixed$Disc[])».ref

/-- **CardDemo's CBACT04C (COBOL) → `Cbact04cFixed.run` (Java, defect fixed), on every input**: for
every input of coblean's `cbact04c_all` and every Java heap holding the same records, the COBOL
program ends with `GOBACK` and every terminating run of the fixed port returns the COBOL program's
`REWRITE` records (decoded, in order), then the last account posted (`missedRewrite`), and the
COBOL program's number of transaction records. -/
theorem cbact04c_fixed_sim (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
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
    (σ : Jimple.State) (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (hpre : RunPreF σ ca aa da acctOf rateOf (jcats accs))
    (hjacct : ∀ a ∈ accs, acctOf (BitVec.ofInt 64 a.id) = jacct a)
    (hjrate : ∀ a ∈ accs, ∀ c ∈ a.cats,
      rateOf (strOf a.grp) (strOf c.ty) (BitVec.ofInt 32 c.cat) = BitVec.ofInt 64 (rate a c)) :
    Sim (CbRelFix (missedRewrite rate accs)) (Call.mk GenF.prog runFixRef [.ref ca, .ref aa, .ref da] σ)
      (EquivLean.Cobol.run CardDemo.Cbact04c { clock := clk } (n + 60)
        (CardDemo.Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)),
          (2, xrefs), (3, accts), (4, discs)])) := by
  obtain ⟨hstop, hrw, htw⟩ := cbact04c_all m hm clk hclk accs hval hdist hlen accts xrefs discs ai xi
    hacct hxref rate di dfill hdisc n hn
  have hok : ∀ a ∈ accs, AccOk rate acctOf rateOf a := fun a ha =>
    ⟨hval a ha, hjacct a ha, fun c hc => ⟨(hdisc a ha c hc).2.2.2, hjrate a ha c hc⟩⟩
  have hjt := (jRun_cbact04c rate acctOf rateOf accs hok hdist).2
  have hjf : jRunFix acctOf rateOf (jcats accs) =
      accs.map (fun a => jposted a (totalInt (rate a) a.cats)) :=
    jRunFix_cbact04c rate acctOf rateOf accs hok hdist
  have hcob : EquivLean.Cobol.Ok (CardDemo.Cbact04c.run { clock := clk } (n + 60)
      (CardDemo.Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)),
        (2, xrefs), (3, accts), (4, discs)])) := by
    rw [EquivLean.Cobol.Ok, hstop]; rfl
  rw [EquivLean.Cobol.run]
  refine sim_of_sat ((EquivLean.Cobol.safe_exec_iff _).2 hcob)
    ((EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hcob⟩) runFix_sat
    ⟨ca, aa, da, acctOf, rateOf, jcats accs, rfl, hpre⟩ ?_
  intro o ho
  cases o with
  | normal v σ' =>
    obtain ⟨res, fs, l, k, xs, mods, hv, hres, hl, ht, hlist, hpairs⟩ :=
      ho ca aa da acctOf rateOf (jcats accs) rfl hpre
    refine ⟨hstop, σ', res, fs, l, k, xs, mods, by rw [hv], hres, hl, hlist, ?_, ?_⟩
    · rw [hrw, dropLast_map_append_missed]
      rw [hjf] at hpairs
      exact pairs_map_dec (fun a ha => decodeAcct_posted a (hval a ha) _) hpairs
    · rw [ht, hjt, htw]
  | exc e σ' => simp [runFixSpec, Spec.of] at ho
  | wrong msg => simp [runFixSpec, Spec.of] at ho

/-- **The simulation is not vacuous**: for every input of coblean's `cbact04c_all` there is a Java
heap holding the same records as objects of the fixed port's classes (`runPreF_exists`), and from
it the simulation `cbact04c_fixed_sim` holds. -/
theorem cbact04c_fixed_sim_exists (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
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
    (n : Nat) (hn : (items accs).length < n) :
    ∃ σ ca aa da, ∃ acctOf : I64 → JAcct, ∃ rateOf : JStr → JStr → I32 → I64,
      RunPreF σ ca aa da acctOf rateOf (jcats accs) ∧
      Sim (CbRelFix (missedRewrite rate accs))
        (Call.mk GenF.prog runFixRef [.ref ca, .ref aa, .ref da] σ)
        (EquivLean.Cobol.run CardDemo.Cbact04c { clock := clk } (n + 60)
          (CardDemo.Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)),
            (2, xrefs), (3, accts), (4, discs)])) := by
  obtain ⟨σ, ca, aa, da, acctOf, rateOf, hpre, hjacct, hjrate⟩ :=
    runPreF_exists accs hval hdist hlen rate (fun a ha c hc => (hdisc a ha c hc).2.2.2)
      (rate_of_key accs discs rate di dfill hdisc)
  exact ⟨σ, ca, aa, da, acctOf, rateOf, hpre, cbact04c_fixed_sim m hm clk hclk accs hval hdist hlen
    accts xrefs discs ai xi hacct hxref rate di dfill hdisc n hn σ ca aa da acctOf rateOf hpre hjacct
    hjrate⟩

end EquivLean.Demo.Cbact04c

#print axioms EquivLean.Demo.Cbact04c.cbact04c_fixed_sim
#print axioms EquivLean.Demo.Cbact04c.cbact04c_fixed_sim_exists
