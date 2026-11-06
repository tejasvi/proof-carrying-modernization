import EquivLean.Bridge.Cobol.Behaves
import EquivLean.Bridge.Jimple.Behaves
import EquivLean.Demo.Jimple.Cbact04c.Glue
import EquivLean.Demo.Jimple.Cbact04c.JavaRun
import EquivLean.Demo.Jimple.Cbact04c.KeyRate
import EquivLean.Demo.Jimple.Cbact04c.NonVacuous


/-!
# COBOL → Java migration: CardDemo's CBACT04C ≡ `Cbact04c.run`, on every input

* **Source**: CBACT04C, the interest calculator of AWS CardDemo, unmodified (COBOL source and
  copybooks through coblean's front end; the program and coblean's theorem `cbact04c_all` are in
  `EquivLean.Demo.Cobol.Cbact04c`, copied unchanged from coblean's snapshot 20261024T0857Z).  Its
  meaning: `EquivLean.Cobol.run CardDemo.Cbact04c …` (five files, keyed reads, `REWRITE`).
* **Target**: `Cbact04c.run(Cat[], Account[], Disc[])` of `examples/java/cbact04c/Cbact04c.java`, a
  port of the program's business logic in which the files are arguments and results (javac
  --release 17, Soot 4.7.1, `jimple_import`).  Its meaning: JimpleLean's `MExec` (partial
  correctness).
* **Outcome relation** `CbRel`: the COBOL run ends with `GOBACK`; the Java method returns a
  `Result` whose rewritten accounts are, in order, the COBOL program's `REWRITE` records decoded
  (id, balance, cycle credit and debit, group: the fields the Java account holds), and whose
  transaction count is the number of records the COBOL program writes to the transaction file.
  Both rewrite every account but the last (the defect reported as CardDemo issue #64, kept by the
  port).

Proof chain:
1. COBOL: `cbact04c_all` (coblean): GOBACK, the rewrites `accs.dropLast.map (·.posted (totalInt …))`,
   `nTxA` transactions.
2. Java: `run_sat` (`Cbact04c/JavaRun.lean`, with the callee contracts of `Cbact04c/JavaCallees.lean`): every terminating run returns `jRun` (the loop as a fold).
3. `jRun_cbact04c` (`Cbact04c/Pure.lean`): `jRun` on the input records is coblean's specification,
   with Java's `long` arithmetic equal to the COBOL field arithmetic (`Cbact04c/Arith.lean`).
4. `decodeAcct_posted` (`Cbact04c/Decode.lean`): a posted record decodes to the Java account.
-/

open Cobol CardDemo.Cbact04c Jimple EquivLean.Jimple

namespace EquivLean.Demo.Cbact04c

/-- The outcome relation (see the module doc). -/
def CbRel (ot : Out) (os : Signal × Cobol.State) : Prop :=
  os.1 = .stop .goback ∧
  ∃ σ' res fs l k xs mods, ot = .normal (some (.ref res)) σ' ∧
    σ'.heap res = some (.plain "Cbact04c$Result" fs) ∧
    Fields.get fs ("Cbact04c$Result", "rewrites") = some (.ref l) ∧ σ'.heap l = some (.list k xs mods) ∧
    Pairs (fun x rec => ∃ ja, AcctAt σ' x ja ∧ decodeAcct rec = some ja) xs (acctRewrites os.2) ∧
    Fields.get fs ("Cbact04c$Result", "transactions") =
      some (.int (BitVec.ofNat 32 (tranWrites os.2).length))


/-- **COBOL → Java, CBACT04C, every input**, for a Java method that satisfies `runSpec` (`run_sat`
proves it of `Cbact04c.run`): `Sim CbRel (Java) (COBOL)`. -/
theorem cbact04c_sim_of (hrun : Sat Gen.prog runRef runSpec)
    (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
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
    (hpre : RunPre σ ca aa da acctOf rateOf (jcats accs))
    (hjacct : ∀ a ∈ accs, acctOf (BitVec.ofInt 64 a.id) = jacct a)
    (hjrate : ∀ a ∈ accs, ∀ c ∈ a.cats,
      rateOf (strOf a.grp) (strOf c.ty) (BitVec.ofInt 32 c.cat) = BitVec.ofInt 64 (rate a c)) :
    Sim CbRel (Call.mk Gen.prog runRef [.ref ca, .ref aa, .ref da] σ)
      (EquivLean.Cobol.run CardDemo.Cbact04c { clock := clk } (n + 60)
        (CardDemo.Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)),
          (2, xrefs), (3, accts), (4, discs)])) := by
  obtain ⟨hstop, hpost⟩ := cbact04c_post m hm clk hclk accs hval hdist hlen accts xrefs discs ai xi
    hacct hxref rate di dfill hdisc n hn σ ca aa da acctOf rateOf hpre hjacct hjrate
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbact04c.run { clock := clk } (n + 60)
      (CardDemo.Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)),
        (2, xrefs), (3, accts), (4, discs)])) := by
    rw [EquivLean.Cobol.Ok, hstop]; rfl
  rw [EquivLean.Cobol.run]
  refine sim_of_sat ((EquivLean.Cobol.safe_exec_iff _).2 hok)
    ((EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩) hrun
    ⟨ca, aa, da, acctOf, rateOf, jcats accs, rfl, hpre⟩ ?_
  intro o ho
  cases o with
  | normal v σ' =>
    obtain ⟨σ'', res, fs, l, k, xs, mods, he, h1, h2, h3, h4, h5⟩ := hpost _ ho
    cases he
    exact ⟨hstop, _, res, fs, l, k, xs, mods, rfl, h1, h2, h3, h4, h5⟩
  | exc e σ' => obtain ⟨_, _, _, _, _, _, _, he, _⟩ := hpost _ ho; cases he
  | wrong msg => obtain ⟨_, _, _, _, _, _, _, he, _⟩ := hpost _ ho; cases he

/-- **CardDemo's CBACT04C (COBOL) → `Cbact04c.run` (Java), on every input**: for every input of
coblean's `cbact04c_all` and every Java heap holding the same records, every terminating run of the
Java method returns, in order, the COBOL program's `REWRITE` records (decoded) and its number of
transaction records, and the COBOL program ends with `GOBACK`. -/
theorem cbact04c_sim (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
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
    (hpre : RunPre σ ca aa da acctOf rateOf (jcats accs))
    (hjacct : ∀ a ∈ accs, acctOf (BitVec.ofInt 64 a.id) = jacct a)
    (hjrate : ∀ a ∈ accs, ∀ c ∈ a.cats,
      rateOf (strOf a.grp) (strOf c.ty) (BitVec.ofInt 32 c.cat) = BitVec.ofInt 64 (rate a c)) :
    Sim CbRel (Call.mk Gen.prog runRef [.ref ca, .ref aa, .ref da] σ)
      (EquivLean.Cobol.run CardDemo.Cbact04c { clock := clk } (n + 60)
        (CardDemo.Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)),
          (2, xrefs), (3, accts), (4, discs)])) :=
  cbact04c_sim_of run_sat m hm clk hclk accs hval hdist hlen accts xrefs discs ai xi hacct hxref rate
    di dfill hdisc n hn σ ca aa da acctOf rateOf hpre hjacct hjrate

/-- **The simulation is not vacuous**: for every input of coblean's `cbact04c_all` there is a Java
heap holding the same records (`runPre_exists`; the rates depend only on the disclosure key,
`rate_of_key`), and from it the COBOL → Java simulation holds. -/
theorem cbact04c_sim_exists (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
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
      RunPre σ ca aa da acctOf rateOf (jcats accs) ∧
      Sim CbRel (Call.mk Gen.prog runRef [.ref ca, .ref aa, .ref da] σ)
        (EquivLean.Cobol.run CardDemo.Cbact04c { clock := clk } (n + 60)
          (CardDemo.Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)),
            (2, xrefs), (3, accts), (4, discs)])) := by
  obtain ⟨σ, ca, aa, da, acctOf, rateOf, hpre, hjacct, hjrate⟩ :=
    runPre_exists accs hval hdist hlen rate (fun a ha c hc => (hdisc a ha c hc).2.2.2)
      (rate_of_key accs discs rate di dfill hdisc)
  exact ⟨σ, ca, aa, da, acctOf, rateOf, hpre, cbact04c_sim m hm clk hclk accs hval hdist hlen accts
    xrefs discs ai xi hacct hxref rate di dfill hdisc n hn σ ca aa da acctOf rateOf hpre hjacct hjrate⟩

end EquivLean.Demo.Cbact04c

#print axioms EquivLean.Demo.Cbact04c.cbact04c_sim
#print axioms EquivLean.Demo.Cbact04c.cbact04c_sim_exists
