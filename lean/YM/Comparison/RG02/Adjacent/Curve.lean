import YM.Comparison.RG02.Symmetry.Turn
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
/-!
# Sidestepping to the adjacent coupling, local positive side and real germs

Raw coupling factor `rating` (analytic representative of the **prescribed** finite-order
reset). Older history has its *own* ratio at the actual coupling. Do not replace the latter
by this one, especially under any µ or halo cutoff. Chosen direction: `Enter` starts from the
argument RU state to which the kernel *is being reexpressed* and takes it to the old state for
composition. Thus one uses `inverseCurve` of the coarse/fine ratio to re-express a fine-unit
ranking program in next (coarse) units. `inverseCurve` local analytic germ proof, not an assertion
these are inverse on each Coupling value sampled: numerical errors & every cost separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent
open Function Filter Finset MeasureTheory
open PertExtension.Series PertExtension.Series.Tested YM.Tensor
open Order Assembly Moving Moving.Path Moving.Shift Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

local notation "φ"=> 𝓝 (0:ℝ)
structure UnitCost where
 rating : ℝ→ℝ
 smooth : ContDiffAt ℝ ω rating 0
 origin : rating 0=1
namespace UnitCost
variable (K L : UnitCost)

def enter (t:ℝ):= t*K.rating t
@[simp] lemma borne: K.enter 0=0:=by simp [enter]
@[fun_prop] lemma here: ContDiffAt ℝ ω K.enter 0:= contDiffAt_id.mul K.smooth
lemma roots: Tendsto K.enter (𝓝 0) (𝓝 0):= by simpa using K.here.continuousAt.tendsto
lemma rating_rises: Tendsto K.rating (𝓝 0) (𝓝 1):= K.origin ▸ K.smooth.continuousAt.tendsto
lemma bright: ∀ᶠ v in φ,0<K.rating v:= K.rating_rises.eventually (lt_mem_nhds zero_lt_one)
lemma forward: Tendsto K.enter along along:= by
   refine tendsto_nhdsWithin_iff.mpr ⟨K.roots.mono_left nhdsWithin_le_nhds, ?_⟩
   filter_upwards [eventually_pos,K.bright.filter_mono (show along≤φ from nhdsWithin_le_nhds)] with v hv h; exact mul_pos hv h

lemma embark: HasFDerivAt K.enter ((ContinuousLinearEquiv.refl ℝ ℝ : ℝ ≃L[ℝ] ℝ) : ℝ →L[ℝ] ℝ) 0:= by
   have ht:= (hasFDerivAt_id (𝕜:=ℝ) (0:ℝ)).mul ((K.smooth.differentiableAt (by simp)).hasFDerivAt)
   simpa [K.origin,one_smul,enter] using! ht
abbrev backmap : ℝ→ℝ:= K.here.localInverse K.embark (by simp)
@[simp] lemma back_origin : K.backmap 0=0:= by
   have h:= K.here.localInverse_apply_image K.embark (by simp); rwa [K.borne] at h
lemma back_smooth : ContDiffAt ℝ ω K.backmap 0:= K.borne ▸ K.here.to_localInverse K.embark (by simp)
lemma back_rises : Tendsto K.backmap (𝓝 0) (𝓝 0):= by simpa only [back_origin] using K.back_smooth.continuousAt.tendsto
lemma enters_left : K.backmap ∘ K.enter=ᶠ[φ] id:= (K.here.hasStrictFDerivAt' K.embark (by simp)).eventually_left_inverse
lemma enters_right : K.enter ∘ K.backmap=ᶠ[φ] id:= by
   have H : K.enter ∘ K.backmap=ᶠ[𝓝 (K.enter 0)] id:= (K.here.hasStrictFDerivAt' K.embark (by simp)).eventually_right_inverse; rwa [borne] at H

def inverseCurve : UnitCost where
 rating x := (K.rating (K.backmap x))⁻¹
 smooth := ( (show ContDiffAt ℝ ω K.rating (K.backmap 0) from K.back_origin.symm ▸ K.smooth).comp _ K.back_smooth).inv (by simp [K.origin])
 origin := by simp [K.origin]
lemma checkedInverse : K.inverseCurve.enter=ᶠ[φ] K.backmap:= by
   filter_upwards [K.back_rises.eventually K.bright,K.enters_right] with v hv hh
   change v* (K.rating (K.backmap v))⁻¹= K.backmap v; change K.backmap v*K.rating (K.backmap v)=v at hh; rw [← div_eq_mul_inv,div_eq_iff hv.ne', hh]

/-- L represents the turn back from K. Useful at fixed Laurent budgets on rings, not a causal cost. -/
structure Recurs (L : UnitCost):Prop where
 pairs : L.enter ∘ K.enter =ᶠ[φ] id
 stairs : K.enter ∘ L.enter =ᶠ[φ] id
variable {K L} in
lemma Recurs.symm (h : K.Recurs L) : L.Recurs K := ⟨h.stairs,h.pairs⟩
lemma rightInverse : Recurs K K.inverseCurve := ⟨(K.checkedInverse.comp_tendsto K.roots).trans K.enters_left,(K.checkedInverse.fun_comp K.enter).trans K.enters_right⟩
variable {K L}

lemma Recurs.stays (h : Recurs K L) : ∀ᶠ t in φ,L.rating (K.enter t)=(K.rating t)⁻¹:= by
   filter_upwards [h.pairs,K.bright] with t ht hh; by_cases hz:t=0; · simp only [hz,borne,L.origin,K.origin,inv_one]
   apply mul_left_cancel₀ hh.ne'; rw [mul_inv_cancel₀ hh.ne']; apply mul_left_cancel₀ hz; rw [← mul_assoc,← enter,mul_one]; exact ht
lemma Recurs.only (h : Recurs K L) : L.rating=ᶠ[φ] K.inverseCurve.rating := by
   filter_upwards [L.roots.eventually h.stays, L.roots.eventually K.rightInverse.stays, h.stairs] with v H Y hv
   simp only [Function.comp_apply, id_eq] at hv; rw [hv] at H Y; rw [H,Y]

def Parallel (K L:UnitCost): Prop:= K.rating=ᶠ[φ] L.rating
-- parity
variable (K L)
def Even : Prop:= ∀ᶠ x in φ,K.rating (-x)=K.rating x
private def reflect_curve : UnitCost where
 rating x:= K.rating (-x)
 smooth := by
   let g : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ _
   exact (show ContDiffAt ℝ ω K.rating (g 0) from g.map_zero.symm ▸ K.smooth).comp _ g.contDiff.contDiffAt
 origin := by simpa using K.origin
private lemma reflects (x:ℝ): K.reflect_curve.enter x= -K.enter (-x):= by simp [enter,reflect_curve]
lemma Recurs.even (h : Recurs K L) (hp : K.Even) : L.Even:= by
   have hv : K.reflect_curve.enter=ᶠ[φ] K.enter:= hp.mono fun x hx=> by unfold enter reflect_curve; dsimp only; rw [hx]
   have hn : Tendsto Neg.neg φ φ:= by simpa using continuous_neg.tendsto (0:ℝ)
   have he : Recurs K.reflect_curve L.reflect_curve:= by
       constructor
       · filter_upwards [hn.eventually h.pairs] with t ht; simp only [Function.comp_apply,reflects,neg_neg]; exact neg_eq_iff_eq_neg.mpr ht
       filter_upwards [hn.eventually h.stairs] with t ht; simp only [Function.comp_apply,reflects,neg_neg]; exact neg_eq_iff_eq_neg.mpr ht
   have hw : Recurs K L.reflect_curve:= ⟨(hv.symm.fun_comp L.reflect_curve.enter).trans he.pairs,(hv.symm.comp_tendsto L.reflect_curve.roots).trans he.stairs⟩
   exact hw.only.trans h.only.symm

@[fun_prop] lemma spin (d:ℤ) : ContDiffAt ℝ ω (fun t=> (K.rating t)^d) 0:= by
   cases d
   case ofNat n => simp only [Int.ofNat_eq_natCast, zpow_natCast]; exact K.smooth.pow n
   case negSucc n=> simp_rw [zpow_negSucc]; exact (K.smooth.pow (n+1)).inv (by simp [K.origin])
end UnitCost
end YM.Comparison.RG02.Adjacent
