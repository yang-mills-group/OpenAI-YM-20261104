import YM.MS.Estimate
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Scale integration, keeping log losses

Native R=exp t. Primitive bounds in downward/tail integration can be used before choosing the initial t.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.LogTime
open Real Function Filter Set
open scoped Topology ContDiff Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma mono (b : ℝ) (hb : 0 ≤ b) : Monotone fun a : ℝ => exp (b*a) :=
  fun _ _ h => exp_monotone (mul_le_mul_of_nonneg_left h hb)

def polyExp (b : ℝ) (j : ℕ) (a : ℝ) := (1+a)^j * exp (-b*a)

lemma pe_pos {b a : ℝ} {j : ℕ} (h : 0 ≤ a) : 0 < polyExp b j a := by unfold polyExp; positivity

lemma vanishes {b : ℝ} (h : 0<b) (j : ℕ) : Tendsto (polyExp b j) atTop (𝓝 0) := by
  have hu := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (j:ℝ) b h).comp (show Tendsto (fun x:ℝ => 1+x) atTop atTop from tendsto_atTop_mono (fun x=> le_add_of_nonneg_left (by linarith : (0:ℝ)≤1)) tendsto_id)
  suffices hz:Tendsto (polyExp b j) atTop (𝓝 (0 * exp b)) by simpa using hz
  apply (hu.mul_const (exp b)).congr; intro a
  change (1+a)^(j:ℝ) * exp _ * exp b = _
  rw [rpow_natCast, mul_assoc, ← exp_add, show -b*(1+a)+b=-b*a by ring]
  rfl

private def tail (b : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  match j with
  | 0 => b⁻¹ * exp (-b*t)
  | j+1 => b⁻¹ * polyExp b (j+1) t + (↑j+1)*b⁻¹ * tail b j t

private lemma tail_pos {b t : ℝ} {j : ℕ} (hb : 0 < b) (ht : 0 ≤ t) : 0 < tail b j t := by
  induction j with
  | zero => rw [tail]; positivity
  | succ j ih => rw [tail]; have h := pe_pos (b:=b) (j:=j+1) ht; positivity

private lemma tail_deriv {b : ℝ} (hb : 0 < b) (j : ℕ) (t : ℝ) :
    HasDerivAt (tail b j) (-polyExp b j t) t := by
  have he : HasDerivAt (fun x => exp (-b*x)) (-b*exp (-b*t)) t := by
    simpa [mul_comm] using ((hasDerivAt_id' t).const_mul (-b)).exp
  induction j with
  | zero =>
    conv => arg 1; ext; rw [tail]
    convert! (he.const_mul b⁻¹) using 1
    simp [polyExp,hb.ne']
  | succ j IH =>
    have hp := (((hasDerivAt_id' t).const_add (1:ℝ)).pow (j+1)).mul he
    conv => arg 1; ext; rw [tail]
    convert! ((hp.const_mul b⁻¹).add (IH.const_mul ((↑j+1)*b⁻¹))) using 1
    dsimp [polyExp]; push_cast; field_simp; ring

private lemma tail_le' {b : ℝ} (hb : 0<b) (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ a : ℝ, 0 ≤ a → tail b j a ≤ C * polyExp b j a := by
  induction j with
  | zero => exact ⟨b⁻¹, by positivity,fun a h=> by simp [tail,polyExp]⟩
  | succ j IH =>
    obtain ⟨c,hc,I⟩ := IH
    refine ⟨b⁻¹+(j+1)*b⁻¹*c, by positivity,fun a ha=>?_⟩
    rw [tail,add_mul b⁻¹ _ _,mul_assoc ((↑j+1)*b⁻¹)]
    gcongr
    apply (I a ha).trans; unfold polyExp; gcongr <;> linarith

lemma backward_cost {b : ℝ} (hb : 0<b) (j : ℕ) : ∃ K : ℝ, 0<K ∧ ∀ (a c C : ℝ), 0 ≤ a → a ≤ c → 0 ≤ C → ∀ (f f' : ℝ → E),
    (∀ u ∈ Icc a c, HasDerivWithinAt f (f' u) (Icc a c) u) →
    (∀ u ∈ Ico a c, ‖f' u‖ ≤ C * polyExp b j u) →
    dist (f a) (f c) ≤ C*K*polyExp b j a := by
  obtain ⟨K,hk,HK⟩:= tail_le' hb j
  refine ⟨K,hk,fun a c C ha hac hc f f' hd h => ?_⟩
  let F u := f u - f a
  let B u := C * (tail b j a-tail b j u)
  have ht : ∀ u, HasDerivAt B (C * polyExp b j u) u := by
    intro u; simpa [B] using! (((tail_deriv hb j u).const_sub (tail b j a)).const_mul C)
  have he : ContinuousOn F (Icc a c) := (show ContinuousOn f (Icc a c) from fun u hu => (hd _ hu).continuousWithinAt).sub continuousOn_const
  have hx : ∀ u ∈ Ico a c, HasDerivWithinAt F (f' u) (Ici u) u := fun u hu=> ((hd u (Ico_subset_Icc_self hu)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hu)).sub_const (f a)
  rw [dist_comm, dist_eq_norm]; calc
    ‖f c-f a‖ ≤ B c := image_norm_le_of_norm_deriv_right_le_deriv_boundary he hx (by simp [F,B]) ht h ⟨hac,le_rfl⟩
    _ ≤ C * (K*polyExp b j a) := mul_le_mul_of_nonneg_left ((sub_le_self _ (tail_pos hb (ha.trans hac)).le).trans (HK a ha)) hc
    _ = _ := (mul_assoc ..).symm

lemma limits [CompleteSpace E] {b s C : ℝ} (hb : 0<b) (hs : 0≤s) (hc : 0 ≤ C) (j : ℕ) (f f' : ℝ → E)
    (hd : ∀ u ∈ Ici s, HasDerivWithinAt f (f' u) (Ici s) u)
    (h : ∀ u ∈ Ici s, ‖f' u‖ ≤ C * polyExp b j u) : ∃ x, Tendsto f atTop (𝓝 x) := by
  obtain ⟨K,-,hk⟩:=backward_cost (E:=E) hb j
  apply cauchy_map_iff_exists_tendsto.mp
  change CauchySeq f
  refine Metric.cauchySeq_iff'.2 fun ε he=>?_
  have hz : Tendsto (fun x => C*K*polyExp b j x) atTop (𝓝 0) := by simpa using (vanishes hb j).const_mul (C*K)
  obtain ⟨N, hN, H⟩ := ((eventually_ge_atTop s).and (hz.eventually (gt_mem_nhds he))).exists
  refine ⟨N,fun n hn=>?_⟩
  rw [dist_comm]; apply lt_of_le_of_lt _ H
  refine hk N n C (hs.trans hN) hn hc f f' ?_ ?_
  · exact fun u hu => (hd u (hN.trans hu.1)).mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hN))
  exact fun u hu => h u (hN.trans hu.1)
end YM.MS.LogTime
