import YM.FVA2.Wick.Analytic
import YM.Push.LOOP_COEFFICIENT.Chain
/-! # Determinant and inverse on actual analytic Taylor coefficients (real germs)
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick.Gem
open Function Set Finset Filter Matrix
open MS MS.Koszul MS.Plane MS.Orbit MS.Orbit.Cog MS.Swirl MS.Book Convolve MS.Cylinder Taylor
open MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.Actors
open Formal (overlay)
open scoped BigOperators Topology Matrix Matrix.Norms.Frobenius ContDiff
variable {A I J E : Type} {p : Sector A} [Fintype J] [DecidableEq J]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : E→Matrix J J ℝ}
lemma det_germ (h:germ M) : germ (fun x => (M x).det) := Push.Loops.det_contDiff.contDiffAt.comp _ h
lemma inv_germ (h:germ M)(hp:IsUnit (M 0).det) : germ (fun x => (M x)⁻¹):= (Push.Loops.inv_contDiffAt _ hp).comp _ h
lemma locally_inv (h:germ M)(hp:IsUnit (M 0).det) : ∀ᶠ x in 𝓝 0, IsUnit (M x).det := by
  filter_upwards [(det_germ h).continuousAt.tendsto.eventually_ne hp.ne_zero] -- syntax inspect
  intro x hx; exact isUnit_iff_ne_zero.mpr hx
lemma total_s {F : I→ E→ℝ}(l:Finset I)(h:∀ i∈l,germ (F i)) : germ (∑ i∈l,F i) := by
  unfold germ; rw [show ∑ i ∈ l,F i = fun x=> ∑ i∈ l,F i x from funext fun x=>Finset.sum_apply ..]; exact ContDiffAt.sum h
abbrev atM (M:E→Matrix J J ℝ)(i j:J) := fun x => M x i j
abbrev atV (M:E→Matrix J J ℝ) := atM fun x => (M x)⁻¹

def select (i j:J) : Matrix J J ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {toFun := fun x => x i j, map_add':= fun _ _=> rfl, map_smul':= fun _ _=> rfl}
omit [DecidableEq J] in
lemma select_s (h:germ M)(i j : J) : germ (atM M i j) := (select i j).contDiff.contDiffAt.comp 0 h
abbrev germ_det (M:E→Matrix J J ℝ)(x:E) := (M x).det
lemma Euler_det (h:germ M) (hp:IsUnit (M 0).det) : Euler (germ_det M) =ᶠ[𝓝 0] (∑ i:J,∑ j:J, Euler (atM M i j) * atV M j i) * germ_det M := by
  filter_upwards [h.eventually (by simp),locally_inv h hp] with x hx hu
  change fderiv ℝ (Matrix.det ∘ M) x x = _; rw [fderiv_comp x (Push.Loops.det_contDiff.differentiable (by simp) _) (hx.differentiableAt (by simp)), ContinuousLinearMap.comp_apply]; erw [Push.Loops.det_variation _ hu, mul_comm,Pi.mul_apply]
  suffices hh : ((M x)⁻¹ * (fderiv ℝ M x x)).trace=(∑ i:J,∑ j:J, Euler (atM M i j) * atV M j i) x from congr_arg (· * (M x).det) hh
  unfold Matrix.trace; simp only [Matrix.diag_apply, Finset.sum_apply,Matrix.mul_apply, Pi.mul_apply]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_
  change _ = fderiv ℝ (select i j ∘ M) x x * _
  rw [fderiv_comp x (select i j).differentiableAt (hx.differentiableAt (by simp))]; erw [(select i j).fderiv, ContinuousLinearMap.comp_apply]; exact mul_comm ..

local infixl:70 " ★ " => overlay p
variable (e:A→E)(H:∀ i,p i=true→e i=0)(h:germ M)(hp:IsUnit (M 0).det)
local notation "T" => letter e
local notation "W" => Swirl.clock useN (Raw A ℂ)
include h hp H
lemma Euler_ink : W (T (germ_det M)) = (∑ i:J, ∑ j:J, W (T (atM M i j)) ★ T (atV M j i)) ★ T (germ_det M) := by
  let X (i j:J) := Euler (atM M i j) * atV M j i
  have he (i j:J) : germ (X i j):= (Euler_s (select_s h ..)).mul (select_s (inv_germ h hp) ..)
  have h' (i:J) : germ (∑ j:J,X i j):= total_s Finset.univ (fun j _=> he i j)
  rw [← Gem.clock e (det_germ h), Gem.nearby e (Euler_det h hp), Gem.times e H (total_s Finset.univ (fun i _=> h' i)) (det_germ h), Gem.sum e Finset.univ (fun i=>∑ j:J,X i j) (fun i _=> h' i)]; congr 2
  apply Finset.sum_congr rfl; intro i _; rw [Gem.sum e _ _ (fun j _=> he i j)]; apply Finset.sum_congr rfl; intro j _; exact Eq.trans (Gem.times e H (Euler_s (select_s h ..)) (select_s (inv_germ h hp) ..)) (congr_arg ( · ★ T (atV M j i)) (Gem.clock e (select_s h i j)))

lemma inverse_ink (i j:J) : (∑ k:J, T (atM M i k) ★ T (atV M k j))= if i=j then Formal.tab (coin 1) else 0 := by
  let X (k:J) := atM M i k * atV M k j
  have he (k:J): germ (X k):= (select_s h i k).mul (select_s (inv_germ h hp) k j)
  simp_rw [← Gem.times e H (select_s h ..) (select_s (inv_germ h hp) ..)]; rw [← Gem.sum e Finset.univ X (fun i _=> he i)]
  have hv : (∑ k,X k)=ᶠ[𝓝 0] fun _=> (1:Matrix J J ℝ) i j := (locally_inv h hp).mono fun x hx=> by
    rw [Finset.sum_apply,← (M x).mul_nonsing_inv hx]; rfl
  rw [Gem.nearby e hv]; simp_rw [Matrix.one_apply]; split_ifs; · simpa using Gem.entire e 1
  exact Gem.zero e
end YM.FVA2.Wick.Gem
