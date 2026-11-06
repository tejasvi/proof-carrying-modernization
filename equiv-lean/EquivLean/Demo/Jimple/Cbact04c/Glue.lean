import EquivLean.Demo.Jimple.Cbact04c.Decode

/-!
# CBACT04C (COBOL) and `Cbact04c.run` (Java) on every input

For every input of coblean's `cbact04c_all` (any accounts with distinct keys, each with any
category balances, account, cross-reference and disclosure-group records found by key, any rates,
any storage, any clock) and the same records as Java objects: the COBOL program ends with `GOBACK`,
and every terminating run of the Java method returns, in order, its rewritten accounts, which are
the COBOL program's `REWRITE` records decoded (id, balance, cycle credit and debit, group), and the
number of transactions the COBOL program writes.
-/

open Cobol CardDemo.Cbact04c Jimple

namespace EquivLean.Demo.Cbact04c

theorem pairs_map {σ : Jimple.State} {xs : List Jimple.Value} {L : List Acc} {f : Acc → JAcct}
    {g : Acc → List UInt8} (hdec : ∀ a ∈ L, decodeAcct (g a) = some (f a))
    (h : Pairs (AcctAt σ) xs (L.map f)) :
    Pairs (fun x rec => ∃ ja, AcctAt σ x ja ∧ decodeAcct rec = some ja) xs (L.map g) := by
  induction L generalizing xs with
  | nil => cases xs <;> simp_all [Pairs]
  | cons a L ih =>
    cases xs with
    | nil => simp [Pairs] at h
    | cons x xs =>
      simp only [List.map_cons, Pairs] at h ⊢
      exact ⟨⟨f a, h.1, hdec a (List.mem_cons_self ..)⟩,
        ih (fun b hb => hdec b (List.mem_cons_of_mem _ hb)) h.2⟩

/-- The run of `run(cats, accounts, discs)`. -/
abbrev runRef : MethodRef := Gen.Cbact04c.«run(Cbact04c$Cat[],Cbact04c$Account[],Cbact04c$Disc[])».ref

theorem cbact04c_post (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
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
    -- the same records as Java objects
    (σ : Jimple.State) (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (hpre : RunPre σ ca aa da acctOf rateOf (jcats accs))
    (hjacct : ∀ a ∈ accs, acctOf (BitVec.ofInt 64 a.id) = jacct a)
    (hjrate : ∀ a ∈ accs, ∀ c ∈ a.cats,
      rateOf (strOf a.grp) (strOf c.ty) (BitVec.ofInt 32 c.cat) = BitVec.ofInt 64 (rate a c)) :
    let r := CardDemo.Cbact04c.run { clock := clk } (n + 60)
      (CardDemo.Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)), (2, xrefs),
        (3, accts), (4, discs)])
    r.1 = .stop .goback ∧
    ∀ o, runSpec.post [.ref ca, .ref aa, .ref da] σ o →
      ∃ σ' res fs l k xs mods, o = .normal (some (.ref res)) σ' ∧
        σ'.heap res = some (.plain "Cbact04c$Result" fs) ∧
        Fields.get fs ("Cbact04c$Result", "rewrites") = some (.ref l) ∧
        σ'.heap l = some (.list k xs mods) ∧
        Pairs (fun x rec => ∃ ja, AcctAt σ' x ja ∧ decodeAcct rec = some ja) xs (acctRewrites r.2) ∧
        Fields.get fs ("Cbact04c$Result", "transactions") =
          some (.int (BitVec.ofNat 32 (tranWrites r.2).length)) := by
  intro r
  obtain ⟨hstop, hrw, htw⟩ := cbact04c_all m hm clk hclk accs hval hdist hlen accts xrefs discs ai xi
    hacct hxref rate di dfill hdisc n hn
  refine ⟨hstop, fun o hspec => ?_⟩
  have hok : ∀ a ∈ accs, AccOk rate acctOf rateOf a := fun a ha =>
    ⟨hval a ha, hjacct a ha, fun c hc => ⟨(hdisc a ha c hc).2.2.2, hjrate a ha c hc⟩⟩
  obtain ⟨hjr, hjt⟩ := jRun_cbact04c rate acctOf rateOf accs hok hdist
  cases o with
  | normal v σ' =>
    obtain ⟨res, fs, l, k, xs, mods, hv, hres, hl, ht, hlist, hpairs⟩ :=
      hspec ca aa da acctOf rateOf (jcats accs) rfl hpre
    refine ⟨σ', res, fs, l, k, xs, mods, by rw [hv], hres, hl, hlist, ?_, ?_⟩
    · rw [hrw]
      rw [hjr] at hpairs
      exact pairs_map (fun a ha => decodeAcct_posted a
        (hval a (by rw [List.dropLast_eq_take] at ha; exact List.mem_of_mem_take ha)) _) hpairs
    · rw [ht, hjt, htw]
  | exc e σ' => simp [runSpec, Spec.of] at hspec
  | wrong msg => simp [runSpec, Spec.of] at hspec

/-- The same, for every terminating run of the Java method (`run_sat`: its contract). -/
theorem cbact04c_java (hrun : Sat Gen.prog runRef runSpec)
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
    let r := CardDemo.Cbact04c.run { clock := clk } (n + 60)
      (CardDemo.Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)), (2, xrefs),
        (3, accts), (4, discs)])
    r.1 = .stop .goback ∧
    ∀ o, MExec Gen.prog runRef [.ref ca, .ref aa, .ref da] σ o →
      ∃ σ' res fs l k xs mods, o = .normal (some (.ref res)) σ' ∧
        σ'.heap res = some (.plain "Cbact04c$Result" fs) ∧
        Fields.get fs ("Cbact04c$Result", "rewrites") = some (.ref l) ∧
        σ'.heap l = some (.list k xs mods) ∧
        Pairs (fun x rec => ∃ ja, AcctAt σ' x ja ∧ decodeAcct rec = some ja) xs (acctRewrites r.2) ∧
        Fields.get fs ("Cbact04c$Result", "transactions") =
          some (.int (BitVec.ofNat 32 (tranWrites r.2).length)) := by
  intro r
  obtain ⟨hstop, hpost⟩ := cbact04c_post m hm clk hclk accs hval hdist hlen accts xrefs discs ai xi
    hacct hxref rate di dfill hdisc n hn σ ca aa da acctOf rateOf hpre hjacct hjrate
  exact ⟨hstop, fun o ho => hpost o (hrun _ _ o ⟨ca, aa, da, acctOf, rateOf, jcats accs, rfl, hpre⟩ ho)⟩

end EquivLean.Demo.Cbact04c
