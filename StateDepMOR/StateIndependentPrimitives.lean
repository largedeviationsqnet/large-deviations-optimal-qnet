import StateDepMOR.Policy

/-!
# State-independent policy and support primitives

This module contains the non-semantic data needed both by the concrete
state-independent queue chain and by the paper statement ledger.  Keeping
these declarations below the chain breaks the former import cycle without
changing their fully qualified names.

The policy PMF is stationary at each fixed `K`: it depends on `K` and the
marked token type, but not on queue state, event epoch, or history.  The
separate `IsKIndependent` condition is the repair used only by Proposition 3,
Part 2.
-/

open scoped ENNReal Topology
open Filter Set

namespace StateDepMOR
namespace PaperStatements

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

/-! ## Generic logarithmic rates -/

/-- A scaled negative logarithmic rate with the paper's `limsup`. -/
noncomputable def negativeLimsupLogRate (loss : PNat -> Real) : EReal :=
  -limsup
    (fun K =>
      ENNReal.log (ENNReal.ofReal (loss K)) /
        ((((K : Nat) : Real)) : EReal))
    atTop

/-- The stronger converse-side rate with the paper's `liminf`. -/
noncomputable def negativeLiminfLogRate (loss : PNat -> Real) : EReal :=
  -liminf
    (fun K =>
      ENNReal.log (ENNReal.ofReal (loss K)) /
        ((((K : Nat) : Real)) : EReal))
    atTop

/-- The two negative logarithmic rates have the order forced by
`liminf <= limsup`; no convergence assumption is needed. -/
theorem negativeLimsupLogRate_le_negativeLiminfLogRate
    (loss : PNat -> Real) :
    negativeLimsupLogRate loss <= negativeLiminfLogRate loss := by
  let u : PNat -> EReal := fun K =>
    ENNReal.log (ENNReal.ofReal (loss K)) /
      ((((K : Nat) : Real)) : EReal)
  have habove :
      Filter.IsBoundedUnder (fun x y : EReal => x <= y) atTop u :=
    Filter.isBoundedUnder_of ⟨(⊤ : EReal), fun _ => le_top⟩
  have hbelow :
      Filter.IsBoundedUnder (fun x y : EReal => x >= y) atTop u :=
    Filter.isBoundedUnder_of ⟨(⊥ : EReal), fun _ => bot_le⟩
  exact EReal.neg_le_neg_iff.mpr
    (Filter.liminf_le_limsup habove hbelow)

/-! ## Fixed-graph randomized policies -/

/-- Randomized, stationary state-independent policy data on one fixed
compatibility graph.  Unlike a policy indexed by a full `Network`, this
object remains literally fixed when `phi` varies in Proposition 3. -/
structure FixedGraphStateIndependentPolicy (G : Network Buffer Server) where
  distribution : PNat -> Server -> Buffer -> PMF (Option Buffer)
  compatible_support : forall K j k action,
    action ∈ (distribution K j k).support ->
      match action with
      | none => True
      | some i => G.compatible i j

/-- The repaired policy class for Proposition 3, Part 2: one fixed collection
of distributions independent of system size. -/
def FixedGraphStateIndependentPolicy.IsKIndependent
    {G : Network Buffer Server}
    (U : FixedGraphStateIndependentPolicy G) : Prop :=
  exists distribution0 : Server -> Buffer -> PMF (Option Buffer),
    forall K j k, U.distribution K j k = distribution0 j k

/-! ## Fixed support classes -/

/-- Networks have the same compatibility graph, while their `phi` fields may
differ. -/
def SameCompatibility (N N' : Network Buffer Server) : Prop :=
  forall i j, N.compatible i j <-> N'.compatible i j

/-- Exact support of a service-token matrix. -/
def HasRateSupport (N : Network Buffer Server)
    (S : Set (Prod Server Buffer)) : Prop :=
  forall j k, 0 < N.phi j k <-> (j, k) ∈ S

/-- The source's support class `D(S)`, with the fixed graph made explicit. -/
def InSupportClass (base N : Network Buffer Server)
    (S : Set (Prod Server Buffer)) : Prop :=
  SameCompatibility base N /\ HasRateSupport N S

/-- Sup-norm distance between two service-token matrices. -/
noncomputable def rateDistance (N N' : Network Buffer Server) : Real :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun p : Prod Server Buffer =>
      |N.phi p.1 p.2 - N'.phi p.1 p.2|)

/-- Relative openness in `D(S)`, stated directly in the matrix sup norm. -/
def IsRelativelyOpenInSupportClass (base : Network Buffer Server)
    (S : Set (Prod Server Buffer))
    (C : Set (Network Buffer Server)) : Prop :=
  forall N, N ∈ C -> InSupportClass base N S ->
    exists epsilon, epsilon > 0 /\
      forall N', InSupportClass base N' S ->
        rateDistance N N' < epsilon -> N' ∈ C

/-- Relative density in `D(S)`, stated directly in the matrix sup norm. -/
def IsDenseInSupportClass (base : Network Buffer Server)
    (S : Set (Prod Server Buffer))
    (C : Set (Network Buffer Server)) : Prop :=
  forall N, InSupportClass base N S ->
    forall epsilon, epsilon > 0 ->
      exists N', InSupportClass base N' S /\
        N' ∈ C /\ rateDistance N N' < epsilon

/-- The support condition printed in Proposition 3. -/
def SupportCoversEveryServer (S : Set (Prod Server Buffer)) : Prop :=
  forall j, exists k, (j, k) ∈ S

/-- Support-level limited flexibility.  This is the additional repair needed
in Proposition 3, Part 2: without it, a destination-serving policy on an ample
support can have identically zero loss throughout `D(S)`. -/
def SupportHasLimitedFlexibility
    (base : Network Buffer Server)
    (S : Set (Prod Server Buffer)) : Prop :=
  exists j k, (j, k) ∈ S /\ Not (base.compatible k j)

/-- Every network in a support class with support-level limited flexibility
has limited flexibility in the network sense. -/
theorem hasLimitedFlexibility_of_inSupportClass
    (base N : Network Buffer Server)
    (S : Set (Prod Server Buffer))
    (hsupport : SupportHasLimitedFlexibility base S)
    (hclass : InSupportClass base N S) :
    N.HasLimitedFlexibility := by
  obtain ⟨j, k, hjk, hincompatible⟩ := hsupport
  refine ⟨j, k, ?_, (hclass.2 j k).2 hjk⟩
  intro hcompatible
  exact hincompatible ((hclass.1 k j).2 hcompatible)

end PaperStatements
end StateDepMOR
