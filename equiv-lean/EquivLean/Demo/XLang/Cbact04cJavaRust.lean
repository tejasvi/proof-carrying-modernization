import EquivLean.Demo.Jimple.Cbact04c.Migration
import EquivLean.Demo.Cobol.Cbact04cRust.Exists

/-!
# Java ⊑ Rust for CBACT04C, by composition through the COBOL program

The two migrations of CardDemo's CBACT04C were proved separately against the same COBOL run:
`cbact04c_sim` (the Java port simulates the COBOL program, `Demo/Jimple/Cbact04c/Migration.lean`)
and `cbact04c_rust_equiv` (the Rust port is equivalent to it, `Demo/Cobol/Cbact04cRust/Sim.lean`).
`Sim.trans` chains them: the Java port simulates the Rust port (`cbact04c_java_rust`), with the
outcome relation `JRRel` stated directly between the two ports.  Every terminating run of the
Java method returns, in order, the accounts the Rust function returns (`SameAcct`: the `long`
fields are the Rust integers, the group id is the same ten EBCDIC bytes, as UTF-16 units in Java
and as a big-endian `u128` in Rust), and the Rust function's transaction count.  The COBOL
program is only the common reference: the statement mentions no COBOL value, and it holds for
every input of coblean's `cbact04c_all` (`cbact04c_java_rust_exists`: inputs for both ports
exist).  Three independently developed encodings take part (coblean, JimpleLean, Aeneas); the
relational layer is the same `Sim` for all of them.
-/

open Cobol CardDemo.Cbact04c Jimple EquivLean.Jimple
open Aeneas Aeneas.Std

namespace EquivLean.Demo.Cbact04cJR

/-- The same account in the Java port's and in the Rust port's representation. -/
def SameAcct (ja : Cbact04c.JAcct) (ra : Cbact04cRust.RAcct) : Prop :=
  ja.id = BitVec.ofInt 64 ra.id ∧ ja.bal = BitVec.ofInt 64 ra.bal ∧
  ja.cc = BitVec.ofInt 64 ra.cc ∧ ja.cd = BitVec.ofInt 64 ra.cd ∧
  ∃ g : List UInt8, ja.grp = Cbact04c.strOf g ∧ ra.grp = Cbact04cRust.beNat g

/-- A COBOL account record decodes to the same account on both sides. -/
theorem decode_same {rec : List UInt8} {ja : Cbact04c.JAcct} {ra : Cbact04cRust.RAcct}
    (hj : Cbact04c.decodeAcct rec = some ja) (hr : Cbact04cRust.decodeAcctR rec = some ra) :
    SameAcct ja ra := by
  unfold Cbact04c.decodeAcct at hj
  unfold Cbact04cRust.decodeAcctR at hr
  cases h1 : decodeNum {} ACCT_ID.fmt (rec.take 11) <;>
    cases h2 : decodeNum {} ACCT_CURR_BAL.fmt ((rec.drop 12).take 12) <;>
    cases h3 : decodeNum {} ACCT_CURR_CYC_CREDIT.fmt ((rec.drop 78).take 12) <;>
    cases h4 : decodeNum {} ACCT_CURR_CYC_DEBIT.fmt ((rec.drop 90).take 12) <;>
    simp only [h1, h2, h3, h4, Option.bind_eq_bind, Option.bind_none, Option.bind_some,
      reduceCtorEq, Option.some.injEq] at hj hr
  subst hj hr
  exact ⟨rfl, rfl, rfl, rfl, _, rfl, rfl⟩

theorem pairs_listRel {σ : Jimple.State} :
    ∀ {xs : List Jimple.Value} {rw : List cbact04c.Account} {recs : List (List UInt8)},
      Cbact04c.Pairs (fun x rec => ∃ ja, Cbact04c.AcctAt σ x ja ∧ Cbact04c.decodeAcct rec = some ja)
        xs recs →
      EquivLean.ListRel (fun a rec => Cbact04cRust.decodeAcctR rec = some (Cbact04cRust.RAcct.ofRust a))
        rw recs →
      Cbact04c.Pairs (fun x a => ∃ ja, Cbact04c.AcctAt σ x ja ∧ SameAcct ja (Cbact04cRust.RAcct.ofRust a))
        xs rw
  | xs, _, _, hp, .nil => by cases xs <;> simp_all [Cbact04c.Pairs]
  | xs, _ :: _, _ :: _, hp, .cons hr hrest => by
    cases xs with
    | nil => simp [Cbact04c.Pairs] at hp
    | cons x xs =>
      obtain ⟨⟨ja, hja, hdec⟩, hp'⟩ := hp
      exact ⟨⟨ja, hja, decode_same hdec hr⟩, pairs_listRel hp' hrest⟩

/-- The outcome relation between the two ports: the Java method returns a `Result` whose
rewritten accounts are, in order, the Rust function's accounts (`SameAcct`), and whose
transaction count is the Rust function's. -/
def JRRel (ot : Out) (orust : Except Error (alloc.vec.Vec cbact04c.Account × Std.U32)) : Prop :=
  ∃ σ' res fs l k xs mods rw n, ot = .normal (some (.ref res)) σ' ∧ orust = .ok (rw, n) ∧
    σ'.heap res = some (.plain "Cbact04c$Result" fs) ∧
    Fields.get fs ("Cbact04c$Result", "rewrites") = some (.ref l) ∧
    σ'.heap l = some (.list k xs mods) ∧
    Cbact04c.Pairs (fun x a => ∃ ja, Cbact04c.AcctAt σ' x ja ∧ SameAcct ja (Cbact04cRust.RAcct.ofRust a))
      xs rw.val ∧
    Fields.get fs ("Cbact04c$Result", "transactions") = some (.int (BitVec.ofNat 32 n.val))

/-- **Java ⊑ Rust, CBACT04C, every input**: for every input of coblean's `cbact04c_all`, a Java
heap and Rust slices holding the same records, the Java method simulates the Rust function under
`JRRel` (`Sim.trans` of `cbact04c_sim` and the reverse half of `cbact04c_rust_equiv`). -/
theorem cbact04c_java_rust (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
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
    -- the records as Java objects
    (σ : Jimple.State) (ca aa da : Addr) (jacctOf : Jimple.I64 → Cbact04c.JAcct)
    (jrateOf : Jimple.JStr → Jimple.JStr → Jimple.I32 → Jimple.I64)
    (hpre : Cbact04c.RunPre σ ca aa da jacctOf jrateOf (Cbact04c.jcats accs))
    (hjacct : ∀ a ∈ accs, jacctOf (BitVec.ofInt 64 a.id) = Cbact04c.jacct a)
    (hjrate : ∀ a ∈ accs, ∀ c ∈ a.cats,
      jrateOf (Cbact04c.strOf a.grp) (Cbact04c.strOf c.ty) (BitVec.ofInt 32 c.cat) =
        BitVec.ofInt 64 (rate a c))
    -- the records as Rust values
    (cats : Slice cbact04c.Cat) (accounts : Slice cbact04c.Account) (rdiscs : Slice cbact04c.Disc)
    (racctOf : Int → Cbact04cRust.RAcct) (rrateOf : Nat → Nat → Int → Int)
    (hcats : cats.val.map Cbact04cRust.RCat.ofRust = Cbact04cRust.rcats accs)
    (hlook : Cbact04cRust.Lookups cats accounts rdiscs racctOf rrateOf)
    (hracct : ∀ a ∈ accs, racctOf a.id = Cbact04cRust.racct a)
    (hrrate : ∀ a ∈ accs, ∀ c ∈ a.cats,
      rrateOf (Cbact04cRust.beNat a.grp) (Cbact04cRust.beNat c.ty) c.cat = rate a c) :
    Sim JRRel (Call.mk Cbact04c.Gen.prog Cbact04c.runRef [.ref ca, .ref aa, .ref da] σ)
      (cbact04c.run cats accounts rdiscs) := by
  have h1 := Cbact04c.cbact04c_sim m hm clk hclk accs hval hdist hlen accts xrefs discs ai xi hacct
    hxref rate di dfill hdisc n hn σ ca aa da jacctOf jrateOf hpre hjacct hjrate
  have h2 := (Cbact04cRust.cbact04c_rust_equiv m hm clk hclk accs hval hdist hlen accts xrefs discs
    ai xi hacct hxref rate di dfill hdisc n hn cats accounts rdiscs racctOf rrateOf hcats hlook hracct
    hrrate).2
  refine (h1.trans h2).mono ?_
  rintro ot orust ⟨ocob, ⟨-, σ', res, fs, l, k, xs, mods, hot, hres, hl, hlist, hpairs, htx⟩,
    ⟨-, rw, cnt, hor, hlr, hcnt⟩⟩
  exact ⟨σ', res, fs, l, k, xs, mods, rw, cnt, hot, hor, hres, hl, hlist, pairs_listRel hpairs hlr,
    by rw [htx, ← hcnt]⟩

/-- **Not vacuous**: for every input of coblean's `cbact04c_all` there are a Java heap and Rust
slices holding the same records (`runPre_exists`, `rust_inputs_exist`), and on them the Java
method simulates the Rust function. -/
theorem cbact04c_java_rust_exists (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
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
    ∃ σ ca aa da, ∃ (cats : Slice cbact04c.Cat) (accounts : Slice cbact04c.Account)
      (rdiscs : Slice cbact04c.Disc),
      Sim JRRel (Call.mk Cbact04c.Gen.prog Cbact04c.runRef [.ref ca, .ref aa, .ref da] σ)
        (cbact04c.run cats accounts rdiscs) := by
  have hkey := Cbact04c.rate_of_key accs discs rate di dfill hdisc
  obtain ⟨σ, ca, aa, da, jacctOf, jrateOf, hpre, hjacct, hjrate⟩ :=
    Cbact04c.runPre_exists accs hval hdist hlen rate (fun a ha c hc => (hdisc a ha c hc).2.2.2) hkey
  obtain ⟨cats, accounts, rdiscs, racctOf, rrateOf, hcats, hlook, hracct, hrrate⟩ :=
    Cbact04cRust.rust_inputs_exist accs hval hdist hlen rate (fun a ha c hc => (hdisc a ha c hc).2.2.2)
      (Cbact04cRust.rate_of_key accs discs rate di dfill hdisc)
  exact ⟨σ, ca, aa, da, cats, accounts, rdiscs, cbact04c_java_rust m hm clk hclk accs hval hdist hlen
    accts xrefs discs ai xi hacct hxref rate di dfill hdisc n hn σ ca aa da jacctOf jrateOf hpre hjacct
    hjrate cats accounts rdiscs racctOf rrateOf hcats hlook hracct hrrate⟩

end EquivLean.Demo.Cbact04cJR

#print axioms EquivLean.Demo.Cbact04cJR.cbact04c_java_rust
#print axioms EquivLean.Demo.Cbact04cJR.cbact04c_java_rust_exists
