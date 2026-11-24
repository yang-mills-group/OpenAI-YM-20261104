import YM.Integration.WilsonInvariantActionTransportedOld
import YM.Integration.WilsonRegisteredAxialCovariance

/-! Total connected response under the original one-step positive Wilson
posterior. Both singly transferred source readings use the very same lower
vacuum as the conditional product. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionConditionalMarginal
open Function Filter Finset MeasureTheory Lattice RG Wilson OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Legato Source MergeProof LocalComparison
open WilsonInvariantActionRegisteredReturn
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N p m:ℕ}
local notation "fine" => Config G (R.family.side (m+1) p)
local notation "coarse" => Config G (R.family.side m p)
local notation "upperLaw" => scene R.family.path N p (m+1)
local notation "lowerLaw" => scene R.family.path N p m

def mean (f:fine→ℂ) (V:coarse):ℂ:=∫U,f U ∂ActualWilsonConditionalRoots.fibre R.family (N:=N) V

def connected (f h:fine→ℂ) (V:coarse):ℂ:=pair (fun X=>mean R (N:=N) X V) f h

private theorem returned (live:m<N) (f:fine→ℂ):
    mean R (N:=N) f=actualTransport R.family (N:=N) f (Nat.le_succ m):=by
  funext V
  unfold mean
  rw [ActualWilsonConditionalRoots.average R.family R.makes live V f,
    actualTransport_step R.family R.makes live f (Nat.le_refl (m+1)),
    actualTransport_base R.family R.makes live]

private theorem fineSum (f h:fine→ℂ) (ef:Envelope f) (eh:Envelope h):
    Envelope (fun X=>f X*h X):=by
  refine ⟨ef.meas.mul eh.meas,⟨ef.cost.choose*eh.cost.choose,?_⟩⟩
  intro U
  rw [norm_mul]
  exact mul_le_mul (ef.cost.choose_spec U) (eh.cost.choose_spec U)
    (norm_nonneg _) ((norm_nonneg _).trans (ef.cost.choose_spec U))

private theorem conserved (live:m<N) (f:fine→ℂ) (ef:Envelope f):
    Integrable (mean R (N:=N) f) (lowerLaw) ∧ ∫V,mean R (N:=N) f V ∂lowerLaw=∫U,f U ∂upperLaw:=by
  rw [returned R live]
  have base:=actualTransport_weighted_integrable R.family R.makes live
    (ef.meas.aestronglyMeasurable (μ:=prior G _)) ef.cost.choose_spec (le_rfl (a:=m+1))
  rw [actualTransport_base R.family R.makes live] at base
  exact ⟨actualScene_integrable_of_weighted R.family R.makes live.le
    (actualTransport_weighted_integrable_of_integrable R.family R.makes live base (Nat.le_succ m)),
    actualScene_transport R.family R.makes live base (Nat.le_succ m)⟩

theorem original (live:m<N) (f h:fine→ℂ) (ef:Envelope f) (eh:Envelope h):
    pair (fun x=>∫U,x U ∂upperLaw) f h=
      (∫V,connected R (N:=N) f h V ∂lowerLaw)+
        pair (fun x=>∫V,x V ∂lowerLaw) (mean R (N:=N) f) (mean R (N:=N) h):=by
  letI:IsProbabilityMeasure (lowerLaw):=probability R.makes.wilson live.le
  have fpaid:=conserved R live f ef
  have hpaid:=conserved R live h eh
  have joint:=conserved R live _ (fineSum R f h ef eh)
  have cap(V:coarse):‖mean R (N:=N) f V‖≤ef.cost.choose:=by
    rw [returned R live];exact actualTransport_norm_le R.family R.makes live ef.cost.choose_spec (Nat.le_succ m) V
  have mixed:Integrable (fun V=>mean R (N:=N) f V*mean R (N:=N) h V) (lowerLaw):=
    hpaid.1.bdd_mul (c:=ef.cost.choose) fpaid.1.1 (ae_of_all _ cap)
  simp only [connected,pair]
  rw [integral_sub joint.1 mixed, fpaid.2, hpaid.2, joint.2]
  ring

end YM.Integration.WilsonInvariantActionConditionalMarginal
