import YM.Integration.ActualScalarTransport
import YM.Integration.WilsonOriginalFiniteRosterTrialRead

/-! Disintegrate an ordinary covariance on one inherited Wilson law.  Its
conditional covariance and the covariance of both conditional means terminate
at the same unrestricted physical expectation. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalConditionalCovarianceReturn
open Function MeasureTheory Lattice RG Wilson Source Labels OPE.Therm
open PhysicalNext.Repeat.Legato
open scoped Classical
variable {G:Gauge}(R:Run G){N p K i:ℕ}
local notation "C" => R.family
local notation "space" j:max => Config G ((C).side j p)
local notation "ν" j:max => scene (C).path N p j

/-- Finite native fee for the actual group function on its own field. -/
def Billed {j:ℕ}(B:ℝ)(F:space j→ℂ):Prop:=
  AEStronglyMeasurable F (prior G _) ∧ ∀V,‖F V‖≤B

theorem multiply {j:ℕ}{F H:space j→ℂ}{B D:ℝ}(a:Billed R B F)(b:Billed R D H):
    Billed R (B*D) (fun V=>F V*H V):=by
  refine ⟨a.1.mul b.1,fun V=>?_⟩
  rw [norm_mul]
  exact mul_le_mul (a.2 V) (b.2 V) (norm_nonneg _) ((norm_nonneg _).trans (a.2 V))

theorem subtract {j:ℕ}{F H:space j→ℂ}{B D:ℝ}(a:Billed R B F)(b:Billed R D H):
    Billed R (B+D) (fun V=>F V-H V):=
  ⟨a.1.sub b.1,fun V=>(norm_sub_le ..).trans (add_le_add (a.2 V) (b.2 V))⟩

theorem carry {F:space K→ℂ}{B:ℝ}(a:Billed R B F)(cut:K≤N)(road:i≤K):
    Billed R B (actualTransport (C) (N:=N) F road):=
  ⟨(actualTransport_integrable (C) R.makes cut a.1 a.2 road).aestronglyMeasurable,
     actualTransport_norm_le (C) R.makes cut a.2 road⟩

theorem paid {F:space K→ℂ}{B:ℝ}(a:Billed R B F)(cut:K≤N):
    Integrable F (ν K):=by
  have term:=actualTransport_weighted_integrable (C) R.makes cut a.1 a.2 (le_refl K)
  rw [actualTransport_base (C) R.makes cut] at term
  exact actualScene_integrable_of_weighted (C) R.makes cut term

theorem whole {F:space K→ℂ}{B:ℝ}(a:Billed R B F)(cut:K≤N)(road:i≤K):
    (∫V,actualTransport (C) (N:=N) F road V ∂ν i)=∫V,F V ∂ν K:=by
  have term:=actualTransport_weighted_integrable (C) R.makes cut a.1 a.2 (le_refl K)
  rw [actualTransport_base (C) R.makes cut] at term
  exact actualScene_transport (C) R.makes cut term road

def covariance {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)(F H:Ω→ℂ):ℂ:=
  (∫V,F V*H V ∂μ)-(∫V,F V ∂μ)*(∫V,H V ∂μ)

/-- Exact law at each original protected date, including coincident dates. -/
theorem original {F H:space K→ℂ}{B D:ℝ}(a:Billed R B F)(b:Billed R D H)(cut:K≤N)(road:i≤K):
    let push:=fun (X:space K→ℂ)=>actualTransport (C) (N:=N) X road
    covariance (ν K) F H=
      (∫V,push (fun U=>F U*H U) V-push F V*push H V ∂ν i)+covariance (ν i) (push F) (push H):=by
  intro push
  have ab:=multiply R a b
  have left:=paid R (carry R ab cut road) (road.trans cut)
  have right:=paid R (multiply R (carry R a cut road) (carry R b cut road)) (road.trans cut)
  dsimp only [push,covariance]
  rw [integral_sub left right,whole R ab cut road,whole R a cut road,whole R b cut road]
  ring
end YM.Integration.WilsonOriginalConditionalCovarianceReturn
end
