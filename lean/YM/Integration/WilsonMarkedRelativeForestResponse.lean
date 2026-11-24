import YM.Integration.WilsonMarkedHomogeneousJet
import YM.Integration.WilsonMarkedRelativeForestRay

/-! The signed contribution of any filed, mixed action tensor to a later
relative forest Taylor coefficient, before the selected Gaussian draw. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedRelativeForestResponse
open Function Filter Finset Lattice Tree Work.F03 Tensor AllOrder.Fire
open WilsonMarkedRelativeForestChart WilsonMarkedRelativeForestCoordinates WilsonMarkedRelativeForestRay
open scoped Classical ContDiff Topology BigOperators
variable {G:Gauge} {c f:Side} {g:Ratio c f}

def total (G:Gauge)(p:ℕ):ℝ:=1+∑i∈range (p+1),‖iteratedFDeriv ℝ i (localLog G) 0‖
theorem one (G:Gauge)(p:ℕ):1≤total G p:=le_add_of_nonneg_right (sum_nonneg fun _ _=>norm_nonneg _)

theorem inside (F:Forest g)(u:ChartVars F G){r p:ℕ}(h:r≤p):
    ‖iteratedDeriv r (ray F u) 0‖≤total G p*(1+‖u‖)^p:=by
  let S:=∑i∈range (p+1),‖iteratedFDeriv ℝ i (localLog G) 0‖
  have C:‖iteratedFDeriv ℝ r (localLog G) 0‖≤S:=single_le_sum
    (f:=fun i=>‖iteratedFDeriv ℝ i (localLog G) 0‖) (fun _ _=>norm_nonneg _) (by simpa using h)
  have A:1≤1+‖u‖:=le_add_of_nonneg_right (norm_nonneg _)
  have z:‖u‖^r≤(1+‖u‖)^p:=(pow_le_pow_left₀ (norm_nonneg u) (by linarith) r).trans (pow_le_pow_right₀ A h)
  refine (WilsonMarkedRelativeForestRay.bound F u r).trans ?_
  change 1+_ ≤ (1+S)*_
  rw [add_mul,one_mul]
  exact add_le_add (one_le_pow₀ A) (mul_le_mul C z (pow_nonneg (norm_nonneg _) _) (sum_nonneg fun _ _=>norm_nonneg _))

def output {d:ℕ}(F:Forest g)(A:T (ℝ×Stationary.Link G f) ℝ d)(j:ℕ)(u:ChartVars F G):ℝ:=
  iteratedDeriv j (diagonal A ∘ ray F u) 0

def charge (G:Gauge)(p j:ℕ):ℝ:=(Fintype.card (OrderedFinpartition j):ℝ)*
  WilsonMarkedHomogeneousJet.allowance p*(total G p)^p

theorem charge_nonnegative (G:Gauge)(p j:ℕ):0≤charge G p j:=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (WilsonMarkedHomogeneousJet.nonnegative _))
    (pow_nonneg (zero_le_one.trans (one G p)) _)

theorem bound {d:ℕ}(F:Forest g)(A:T (ℝ×Stationary.Link G f) ℝ d){p j:ℕ}(h:j≤p)(u:ChartVars F G):
    |output F A j u|≤charge G p j*‖A‖*(1+‖u‖)^(p*p):=by
  let B:=total G p*(1+‖u‖)^p
  have big:1≤B:=one_le_mul_of_one_le_of_one_le (one G p) (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _)))
  have Faa:=WilsonPhysicalLogChainPrice.sum h (diagonal A) (ray F u) 0
    (diag_smooth A (p:WithTop ℕ∞)).contDiffAt ((regular F u).of_le le_top)
    (mul_nonneg (WilsonMarkedHomogeneousJet.nonnegative p) (norm_nonneg A)) big
    (fun i hi=>by rw [zero];exact WilsonMarkedHomogeneousJet.paid A hi) (fun i hi=>inside F u hi)
  change ‖iteratedDeriv j (diagonal A ∘ ray F u) 0‖≤_
  refine Faa.trans_eq ?_
  dsimp only [B,charge];rw [mul_pow,pow_mul];ring

theorem grade {d:ℕ}(F:Forest g)(A:T (ℝ×Stationary.Link G f) ℝ d)(j:ℕ):
    Rank (ChartVars F G) j (output F A j):=by
  let J:=iteratedFDeriv ℝ j (diagonal A ∘ joint F) 0
  let L:ChartVars F G→L[ℝ](ℝ×ChartVars F G):=(0:ChartVars F G→L[ℝ]ℝ).prod (ContinuousLinearMap.id ℝ _)
  have regularity:ContDiffAt ℝ (j:WithTop ℕ∞) (diagonal A ∘ joint F) 0:=
    (diag_smooth A _).contDiffAt.comp 0 ((joint_smooth F).of_le le_top)
  have filed:output F A j=fun u:ChartVars F G=>J (fun _=>((1:ℝ),u)):=by
    funext u
    have rayprice:=PertExtension.Series.Radial.homogeneous_derivative (f:=diagonal A ∘ joint F) ((1:ℝ),u) j regularity
    unfold PertExtension.Series.Radial.jet at rayprice
    change iteratedDeriv j (diagonal A ∘ ray F u) 0=_
    apply (mul_left_cancel₀ (by positivity : (j.factorial:ℝ)⁻¹≠0))
    simpa only [J,Prod.smul_mk,smul_eq_mul,mul_one,Function.comp_def,ray,joint] using rayprice.symm
  rw [filed]
  let base:=Rank.hom (ContinuousLinearMap.id ℝ (ℝ×ChartVars F G)) J
  simpa [L] using base.app L ((1:ℝ),0)

theorem priced {d:ℕ}(F:Forest g)(A:T (ℝ×Stationary.Link G f) ℝ d){p j:ℕ}(h:j≤p):
    Prices (p*p) (charge G p j*‖A‖) (output F A j):=
  ⟨mul_nonneg (charge_nonnegative ..) (norm_nonneg _),
    (grade F A j).up (h.trans (Nat.le_mul_self p)),bound F A h⟩

end YM.Integration.WilsonMarkedRelativeForestResponse
end
