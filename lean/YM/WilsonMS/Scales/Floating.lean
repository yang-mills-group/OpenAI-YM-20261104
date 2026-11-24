import YM.WilsonMS.Scales.CartScale
import Mathlib.Analysis.Polynomial.Basic
/-!
# Intrinsic grade detection by projection under dilation

Conjugation by the exponential grade clock tends to projection onto its
engineering block; paying both grade directions at once this way helps
separate exact grade, no read-after-estimate at a bare amplitude here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.GFlow
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Logarithm
open PowerSeries (coeff mk X C constantCoeff invOfUnit)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates FrameX Ice
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k n m j : ℕ}
local notation "BΨ" => Ensure.deck G
section timeline

variable {E : Type} [AddCommGroup E] [Module ℝ E] {F : ℝ → E}

private lemma recruit_poly (h : Ready F) {P : ℝ → ℝ} (ht : Ready P) : Ready (fun i => F (P i)) := by
  obtain ⟨S, hs⟩ := ht.scalar
  rw [hs]
  refine
    h.Ind (p := fun f => Ready (fun i => f (Polynomial.eval i S))) (fun a v => ?_) (Ready.const _)
      (fun _ _ hK hT => hK.add hT) (fun k _ hv => hv.scale k)
  simp_rw [← Polynomial.eval_comp]
  exact status _ _

lemma coord_burn (h : Ready F) (r : ℝ) : Ready (fun i => F (r - i)) :=
  recruit_poly h ((Ready.const r).sub (by simpa using Ready.got Polynomial.X))

lemma coord_apply {r : ℝ → ℝ} (h : Ready r) (ht : Ready F) : Ready (F ∘ r) :=
  recruit_poly ht h

lemma plus_poly (h : Ready F) (r : ℝ) : Ready (fun i => F (i + r)) := by
  have hh : Ready (fun i : ℝ => i) := by simpa using Ready.got Polynomial.X
  exact recruit_poly h (hh.add (Ready.const _))

lemma monopoly {f : ℝ → ℝ} (h : Ready f) (ht : Tendsto f atTop (𝓝 0)) : f = 0 := by
  obtain ⟨p, hP⟩ := h.scalar
  have hp := ht.abs
  rw [abs_zero, hP] at hp
  have he : p.degree ≤ 0 :=
    le_of_not_gt fun h => (not_tendsto_atTop_of_tendsto_nhds hp (p.abs_tendsto_atTop h))
  have hV : f = (fun _ => p.coeff 0) := by
    funext i
    rw [hP, Polynomial.eq_C_of_degree_le_zero he]
    simp
  rw [hV] at ht ⊢
  rw [tendsto_nhds_unique tendsto_const_nhds ht]
  rfl

lemma quiet {f : ℝ → ℂ} (h : Ready f) (ht : Tendsto f atTop (𝓝 0)) : f = 0 := by
  ext1 v
  apply Complex.ext
  · obtain he :=
      monopoly (h.linear Complex.reCLM.toLinearMap)
        (Complex.continuous_re.continuousAt.tendsto.comp ht)
    exact congr_fun he v
  obtain he :=
    monopoly (h.linear Complex.imCLM.toLinearMap) (Complex.continuous_im.continuousAt.tendsto.comp ht)
  exact congr_fun he v

lemma accounts {I : Type} (P : Finset I) {f : I → ℝ → E} (h : ∀ i ∈ P, Ready (f i)) :
    Ready (fun p => ∑ i ∈ P, f i p) := by
  convert Ready.sums P h using 1
  ext1 i
  rw [Finset.sum_apply]
end timeline
variable {Z : Guard G d}

lemma exchange_cost (h : CloseP Z) (L : Sec G d →ₗ[ℂ] ℂ) (n : ℕ) (x : Sec G d) :
    Tendsto (fun t => L (coeff n (buryD t Z) x)) atTop (𝓝 (L (coeff n (printM Z) x))) := by
  simp_rw [deep_move]
  rw [printed]
  let T := coeff n Z
  have hu := filter_emb h n
  conv => arg 1; intro i; rw [← whole x, map_sum, map_sum]
  conv_rhs => rw [← whole x, map_sum, map_sum];
  refine tendsto_finsetSum _ fun v hv => ?_
  simp_rw [Module.End.mul_apply, pane, tileskip]
  let p := tileK G d v x
  have hm (s : ℝ) (p : Sec G d) : T (s • p) = s • T p := _root_.map_smul (T.restrictScalars ℝ) s p
  let f (j : Pay d) (t : ℝ) : ℂ := (tag t v.val * tag (-t) j.val) • L (tileK G d j (T p))
  change Tendsto _ atTop (𝓝 (L (tileK _ _ _ (T p))))
  rw [show L (tileK _ _ v (T p)) = ∑ i : Pay d, if i = v then L (tileK _ _ i (T p)) else 0 from
      (by simp)]
  have H (i : ℝ) : L (window G d (-i) (T (tag i v.val • p))) = ∑ j, f j i := by
    rw [road, map_sum, hm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show tileK G d j ((tag i v.val) • T p) = tag i v.val • tileK G d j (T p) from
        _root_.map_smul ((tileK G d j).restrictScalars ℝ) _ _,
      smul_smul, mul_comm]
    exact map_smul (L.restrictScalars ℝ) _ _
  simp_rw [show ∀ i : ℝ, L (window G d (-i) (coeff n Z (tag i v.val • tileK G d v x))) = _ from H]
  refine tendsto_finsetSum _ fun j _ => ?_
  unfold f
  split_ifs with he
  · subst j
    simp_rw [tag_add, add_neg_cancel]
    simp [tag]
  rcases le_or_gt j v with hL | hL
  · have hp : (j.val : ℝ) < (v.val : ℝ) := by
      exact_mod_cast (show j.val < v.val from lt_of_le_of_ne hL (fun h => he (Fin.ext h)))
    have hD : Tendsto (fun t => exp (((j.val : ℝ) - v.val) * t)) atTop (𝓝 0) :=
      tendsto_exp_atBot.comp
        ((tendsto_id (x := atTop)).const_mul_atTop_of_neg (by linarith : ((j.val : ℝ) - v.val) < 0))
    simp_rw [show ∀ t : ℝ, tag t v.val * tag (-t) j.val = exp ((↑j.val - ↑v.val) * t) from fun t => by
        unfold tag
        rw [← exp_add]
        ring_nf]
    simpa using! hD.smul_const (L (tileK G d j (T p)))
  rw [show tileK G d j (T p) = 0 from hu _ _ hL _, map_zero]
  simp_rw [smul_zero]
  exact tendsto_const_nhds
end YM.WilsonMS.GFlow
