import YM.FormalBulk08.Plait.Wax
import YM.MSbar.Wave.Reedy
import YM.FVA2.ReindexLaplace

/-! Scalar all-order real logarithm of a finite perturbative vacuum jet at
its actual positive head. The head can depend on the retained field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorFormalLog

open Function Filter Finset PowerSeries FormalBulk08 FormalBulk08.Series FormalBulk08.Jets
open FormalBulk08.Plait PertExtension PertExtension.Series PertExtension.Series.Tested MSbar MSbar.Wave
open scoped Classical Topology BigOperators ContDiff

private def probe : (Unit → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj ()

def jets (f : ℝ→ℝ) : PowerSeries ℝ :=
  PowerSeries.map (MvPolynomial.eval (fun _ : Unit=>1)) (paste (f ∘ probe))

theorem quotes (f : ℝ→ℝ) (hot : ContDiffAt ℝ ∞ f 0) (j : ℕ) : coeff j (jets f)=Wave.bill f j := by
  rw [jets,PowerSeries.coeff_map]
  change traceP (fun _ : Unit=>1) (coeff j (paste (f ∘ probe))) = _
  rw [trace_paste,FVA2.GermLaplace.jet_pull probe f hot]
  rfl

/-- The polynomial selected up to `r` in the original scene genuinely
recovers all given normalized Taylor coefficients through that same order. -/
theorem polynomial (A : PowerSeries ℝ) (r : ℕ) : Through r (jets (peval (term A) r)) A := by
  let P:=peval (term A) r
  have hot : ContDiff ℝ ω P := by unfold P peval Zone.eval; fun_prop
  have fare : Wave.Grade (fun g:ℝ=>∑ j ∈ range (r+1),g^j*(coeff j A-Wave.bill P j)) (r+1) := by
    apply (Wave.certified hot.contDiffAt r).egress
    filter_upwards with g _ _
    change (∑ j ∈ range (r+1),g^j*coeff j A) - ∑ j ∈ range (r+1),g^j*Wave.bill P j = _
    simp only [mul_sub,Finset.sum_sub_distrib]
  intro i hi
  rw [quotes _ (hot.contDiffAt.of_le le_top)]
  exact (sub_eq_zero.mp (Wave.magnitude fare i hi)).symm

def logarithm (A : PowerSeries ℝ) : PowerSeries ℝ :=
  C (Real.log (coeff 0 A)) + covelog (C (coeff 0 A)⁻¹ * A)

/-- Normalize at the *actual* positive head before applying the original
formal exponential/logarithm inversion. -/
theorem scalar (P : ℝ→ℝ) (hot : ContDiffAt ℝ ∞ P 0) (positive : 0<P 0) :
    jets (Real.log ∘ P) = C (Real.log (P 0)) + covelog (C (P 0)⁻¹ * jets P) := by
  let f:=P ∘ probe
  let c:=P 0
  let u:=fun x : Rays Unit=>c⁻¹*f x
  have hf : ContDiffAt ℝ ∞ f 0 := hot.comp (g:=P) 0 (f:=probe) probe.contDiff.contDiffAt
  have fzero : f 0=c := by simp [f,c]
  have hc : 0<c:=positive
  have hu : ContDiffAt ℝ ∞ u 0:=contDiffAt_const.mul hf
  have head : u 0=1 := by dsimp only [u]; rw [fzero,inv_mul_cancel₀ hc.ne']
  have near : Real.log ∘ f =ᶠ[𝓝 (0 : Rays Unit)] (fun _=>Real.log c) + Real.log ∘ u := by
    have hu' : ∀ᶠ x in 𝓝 (0 : Rays Unit),0<u x :=
      hu.continuousAt.eventually (lt_mem_nhds (head.symm ▸ zero_lt_one))
    filter_upwards [hu'] with x hx
    change Real.log (f x)=Real.log c+Real.log (u x)
    rw [←Real.log_mul hc.ne' hx.ne']
    congr 1
    change f x=c*(c⁻¹*f x)
    rw [←mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]
  have tail : paste u = C (MvPolynomial.C c⁻¹) * paste f := by
    change paste ((fun _ : Rays Unit=> c⁻¹)*f) = _
    rw [paste_mul _ _ contDiffAt_const hf,paste_flat]
  have phead : coeff 0 (paste u)=1 := by rw [paste_first,head,map_one]
  change PowerSeries.map _ (paste (Real.log ∘ f)) = _
  rw [paste_replace near,paste_sum (fun _ : Rays Unit=>Real.log c) (Real.log ∘ u) contDiffAt_const
      (hu.log (head.symm ▸ one_ne_zero)),paste_flat,
    pin_rung u head hu,_root_.map_add,PowerSeries.map_C,map_covelog _ phead,tail,_root_.map_mul,PowerSeries.map_C]
  simp [jets,f,c]

theorem read (A : PowerSeries ℝ) (r i : ℕ) (paid : i≤r) (positive : 0<coeff 0 A) :
    Wave.bill (Real.log ∘ peval (term A) r) i = coeff i (logarithm A) := by
  let P:=peval (term A) r
  have hot : ContDiff ℝ ω P := by unfold P peval Zone.eval; fun_prop
  have head : P 0=coeff 0 A := by simp [P,term,Zone.eval,Finset.sum_range_succ']
  have valid : Through r (jets P) A := polynomial A r
  have normalized:= (Through.exact_eq (C (coeff 0 A)⁻¹) r).mul valid
  have unit : coeff 0 (C (coeff 0 A)⁻¹*jets P)=1 := by
    rw [coeff_C_mul,valid 0 (Nat.zero_le _),inv_mul_cancel₀ positive.ne']
  have same := (Through.exact_eq (C (Real.log (coeff 0 A))) r).add (normalized.cove_congr unit)
  have gp : 0<P 0 := head.symm ▸ positive
  rw [←quotes (Real.log ∘ P) ((hot.contDiffAt.of_le le_top).log gp.ne') i]
  rw [scalar P (hot.contDiffAt.of_le le_top) gp,head]
  exact same i paid

/-- Extract the exact Gaussian head and all retained interaction terms
from the actual physical quadratic convention, including the constant mode. -/
theorem kinetic (A F : PowerSeries ℝ) (r : ℕ) (height : ℝ) (positive : 0<coeff 0 A) (zeroth : coeff 0 F=0)
    (price : ∀ i≤r, coeff i F=Wave.bill (Real.log ∘ peval (term A) r) i + if i=0 then height else 0) :
    coeff 0 A=Real.exp (-height) ∧ Through r F (covelog (C (coeff 0 A)⁻¹*A)) := by
  have origin : coeff 0 (C (coeff 0 A)⁻¹*A)=1 := by rw [coeff_C_mul,inv_mul_cancel₀ positive.ne']
  have base:=price 0 (Nat.zero_le r)
  rw [zeroth,read A r 0 (Nat.zero_le r) positive,logarithm,map_add,coeff_zero_C,covelog_rank origin] at base
  have root : Real.log (coeff 0 A) = -height := by simp only [add_zero,if_true] at base; linarith
  refine ⟨(Real.exp_log positive).symm.trans (congrArg Real.exp root),?_⟩
  intro i hi
  cases i with
  | zero => rw [zeroth,covelog_rank origin]
  | succ i =>
    have h:=price (i+1) hi
    rw [read A r (i+1) hi positive] at h
    simpa [logarithm] using h

end YM.Integration.WilsonConditionalTaylorFormalLog
end

