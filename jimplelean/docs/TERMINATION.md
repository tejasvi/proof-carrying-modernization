# Termination and total correctness

`Sat P m S` is partial correctness: `MExec` is a big-step relation, so an execution that does not
terminate has no derivation and satisfies every contract. `Jimple/Termination.lean` adds termination;
`Jimple/TermSplit.lean` derives a method's termination proof from its partial-correctness proof.

## Statements

All in namespace `Jimple`.

* `MTerm P m args σ` (mutual inductive with `VTerm`, `RTerm`, `BTerm`, `Jimple/Termination.lean`):
  every execution of the selected method `m` on `args` from `σ` terminates, over every
  nondeterministic choice and every outcome of every callee, and at least one execution exists
  (no call is stuck). An execution may still end in `.wrong`; the contracts exclude that.
* `MTerm.run : MTerm P m args σ → ∃ o, MExec P m args σ o`.
* `TermVC.mterm (hV : Valid P Γ) (hT : ∀ sig S', (Γ.below rank r) sig = some S' → ContractTerm P sig S')
  (h : TermVC P Γ rank r d m S A fuel) : ∀ args σ0, S.pre args σ0 → MTerm P m args σ0`.
* `AllTermVC.term (hV : Valid P Γ) (hT : AllTermVC P Γ rank d Ann) :
  ∀ sig S, Γ sig = some S → ContractTerm P sig S` (a whole contract table, callees ordered by `rank`).
* `total_of_sat_mterm (hs : Sat P m S) (ht : ∀ args σ, S.pre args σ → MTerm P m args σ) :
  ∀ args σ, S.pre args σ → (∃ o, MExec P m args σ o) ∧ ∀ o, MExec P m args σ o → S.post args σ o`.
* `TermVC.of_thin (hΓ : Γ.below rank r = Γ) (hV : MethodVC P Γ d m S I fuel)
  (hT : ThinVC P Γ d m S I vs fuel) : TermVC P Γ rank r d m S (I.withVariants vs) fuel`
  (`Jimple/TermSplit.lean`).

`#print axioms` of each: `propext`, `Classical.choice`, `Quot.sound`.

## The verification conditions

* `TermVC P Γ rank r d m S A fuel`: `bodyWP` with postcondition `True`. Each cut point of `A` has an
  invariant and a natural-number variant; a path from a cut point to the next one must reach it
  with a smaller variant. Calls are answered by `callWPT`: the contracts of `Γ` of rank below `r`
  (whose termination is a hypothesis of `TermVC.mterm`) or by inlining, and no call may be stuck (a
  virtual call answered by a contract is on a concrete class, an inlined library call has a
  receiver of the right shape).
* `ThinVC P Γ d m S I vs fuel`: the same paths with `MethodVC`'s invariants `I`, the cut assertions
  being only the variants (`vs pc`, one per cut point) and the calls answered by `callWPThin`
  (`callWPT` without the callee preconditions). `MethodVC` supplies the invariants and the
  preconditions: `TermVC.of_thin` combines the two (`bodyWP_and`, `callWP_thin`). A thin VC is
  much cheaper than the `MethodVC` it accompanies: no invariant is re-established.

## Writing a termination proof

For a method with `h_vc : MethodVC P Γ d m S I fuel`:

1. Choose variants. A loop head: the distance to the loop's bound, e.g. `(n.toInt - i.toInt).toNat`
   read from the frame (`fr.get j`). Nested or successive loops: weights, e.g. `2^33 * outer + inner`
   with every inner term below `2^33`. Straight-line cut points (proof splits): constants decreasing
   along the body. Write a per-cut-point variant with `if pc = 22 then … else if pc = 29 then …`,
   not by matching on the literals: a match on `92` unfolds in unary, and `jvc` then takes minutes
   and the kernel rejects the proof ("deep recursion").
2. `theorem m_thin : ThinVC P Γ d m S I vs fuel := by jthin [the unfold list of h_vc, the variants]`;
   for segment-wise proofs, one thin twin per segment theorem, with the segment's hypotheses and
   `jvc` call (the variants added to its list), then `TermVC.of_thin`.
3. `TermVC.mterm (rank := fun _ => 0) (r := 1) hValid hCalleesTerm
   (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) h_vc m_thin)`.
4. Callees: `jcontract_term [m_term]` proves `ContractTerm P sig S`; `Contracts.term_of_ok` lifts
   a table's; `ContractTerm.mono` passes to a stronger precondition.
5. `total_of_sat_mterm m_sat m_term`.

`jnorm_lits` turns raw numerals that `jvc`'s ground evaluation leaves in hypotheses back into numerals
for `omega`, when a variant goal is closed by hand.

One more pitfall, from the equiv-lean packages: a variant goal with the same large literal offset on
both sides (`x + 4294967308 < y + 4294967308`) can be closed by `simp` through offset unification in a
way the kernel then checks in unary ("deep recursion"); take the offset as a parameter with bounds
instead. `jcontract_term` enumerates the implementing application classes of an instance method or
constructor as `jcontract_ok` does (`Examples/Caching/TermLink.lean`); give it a fact for every class
that selects its own implementation.

## Callees that need a stronger precondition (`Jimple/TermSplitX.lean`)

A virtual call answered by a contract terminates only when the receiver's runtime class is concrete
(`callWPT`; `ContractTerm` promises `VTerm` for concrete classes only), and a partial-correctness
contract need not say that. `TermVC.of_thinX` pairs the `MethodVC` against `Γ` with a thin VC that also
checks an extra premise `X sig args σ` at every contracted call (`callWPThinX`), and gives the
termination VC against `Γ.strengthen X` (each contract's precondition with `X sig` added). Validity:
`Valid.strengthen`. Callee termination: each callee's own result under the stronger precondition
(`SpecEnv.strengthen_term`, `MethodVC.strengthen`). `ThinVCX.mk` splits the thin VC into the entry path
and the cut points' paths (no cut point at statement 0); prove each with `jvc_body [the jverify_body
list, the variant, X]`; `ThinVCPX` is the per-program form.

Patterns from equiv-lean's T4 Java column (Apache Thrift; t4-java-total 613c77c):
- An abstract collaborator (a transport behind contracts) is called virtually: take its termination as a
  hypothesis like its contracts, and the concreteness of its runtime class as a premise at the entry.
  Destructure the premise before `jvc` (keep it out of the `jvc` list: simp recursion); the
  concreteness goals then close by `assumption`, as long as the collaborator's frames keep its class.
- A callee premise (`X`) for the caller's own protocol methods passes the premise on. If a callee's
  contract does not say that the collaborator keeps its class, a second call cannot get the premise from
  the first call's postcondition; then state it for every valid collaborator object (a premise on the
  representation, e.g. "every object with `R.inv σ t` has a concrete class"), which gives it in every
  state where the invariant holds.
- A callee whose contract has the precondition `False` (a path the caller's precondition excludes):
  give it the premise `False` too. The thin VC does not check preconditions, so without it the thin VC
  follows the call into an arbitrary state (minutes instead of seconds); with it the path closes as in
  the `MethodVC` (by the same contradiction).
- A call on `this` of a program class: the goal `P.concrete c = true` closes from
  `P.findClass c = some d` by evaluating `d`'s modifiers.

## Results

| Program | Theorems | Files |
|---|---|---|
| `sumTo` | `Examples.Termination.sumTo_terminates` | `Examples/Termination.lean` |
| CBACT02C | `run_term`, `run_total` | `Examples/CardDemo/Cbact02cTerm*.lean` (`TermVC` directly) |
| CBCUS01C | `cu_run_term`, `cu_run_total` | `Examples/CardDemo/Cbcus01cTerm*.lean` (split VC) |
| CBACT03C | `c3_run_term`, `c3_run_total` | `Examples/CardDemo/Cbact03cTerm*.lean` (split VC) |

The thin VCs of CBCUS01C's `run` check in 20 s (its `MethodVC` segments: 11–59 s each).

The equiv-lean CardDemo proofs (`EquivLean.Modernize.<Prog>`) get their termination the same way:
thin twins of their segment theorems, generated from the sources, and the callee tables'
`ContractTerm`s (all eight programs: `run_term`, `run_total`; branch java-total 9f0e5fb). equiv-lean's
T4 Java column (Apache Thrift's compact and binary protocols: 26 methods, the 42 E/D/M theorems of its
table) is totally correct by `TermVC.of_thinX` (branch t4-java-total 613c77c, `Demo/Thrift/Java/Term/`).
