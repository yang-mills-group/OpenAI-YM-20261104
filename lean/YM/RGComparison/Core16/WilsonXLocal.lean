import YM.RGComparison.Core16.Savings
import YM.RGComparison.Core16.Marks

/-!
# WilsonX local prescription (one piece, conditional on flat)

This module is about the core, complex
*multi*-insertion side and extension from the real/positive vacuum comparisons above. Freeze the
formal prescription without choosing a new regulator. For WilsonX it supplies the finite lattice
conditional expansion at flat with the cost of the vacuum offsets made visible. Readers should
NOT use this coefficient as a formal cover-kernel moment after IR/image changes until the stated
producer dependencies are proved. Bare inputs with external Laurent powers resolved. Shift each
stencil's price before reporting; common output order used independently of engineering/shift.
Kinetic offsets constant through the Germ here; `u i` allowed to vary in estimates with explicit
cost (the precision theorem consumes `d.Band` for every offset). The prescription does not yet
include theoretical kinetic predictions for the offsets, except e.g. the special low-order case
which needs no prediction. In particular a `ranking v` statement beyond first order doesn't give
matching to the full Fk/A selected reset trajectory.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.WilsonXLocal
open Lattice RG Tree Wilson Precision Push.BetaTransport Marker
open Function Filter MeasureTheory Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PertExtension PertExtension.Series Tested Radial Core16.Descent
variable {G : Gauge} {n c : Side} {d : Descent n c} (P : ChartRatio G)

section map
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (L : X →L[ℝ] Y) {F : Config G n → X}
    {w r : ℕ} {a : ℕ → X} (β : ℕ → ℝ)

lemma tested (H : d.Testable F) : d.Testable (L ∘ F) where
  neat := L.continuous.comp H.neat
  invariant t U := congrArg L (H.invariant t U)
  smooth := L.contDiff.contDiffAt.comp 0 H.smooth

lemma wanted (h : d.grade F w) : d.grade (L ∘ F) w := by
  intro x; obtain ⟨C,hc,h⟩ := h x; refine ⟨‖L‖*C,by positivity,?_⟩
  filter_upwards [h,eventually_pos] with t ht he
  exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (mul_assoc ..).symm)

lemma eval_map (z : ℝ) : peval (L ∘ a) r z = L (peval a r z) := by
  unfold peval Zone.eval; rw [map_sum]; exact Finset.sum_congr rfl (fun i _ => Eq.symm (map_smul ..))
variable [CompleteSpace X] [CompleteSpace Y]

lemma measured (h : d.OK G) (he : Continuous F) (x) : d.conditioned β (L ∘ F) x = L (d.conditioned β F x) := by
  unfold Descent.conditioned
  rw [map_smul]; congr 1; unfold Descent.weighted
  let f := bare (β d.depth) (G:=G) (n:=n)
  have ha : L ∘ (f • F) = f • (L ∘ F) := funext fun i => L.map_smul _ _
  have ht := output_linear (f := f • F) h β L (((bare_cont _).smul he).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))
  rw [ha] at ht; exact (congr_fun ht _).symm
end map

variable {f : Config G n → ℂ} {w : ℕ} (R : LocalRatio P) (r : ℕ)
    (h : d.Room G) {M : ℝ} {v : ℕ → ℝ} (hf : d.Testable f) (hG : d.grade f w)
    (gV : d.Band M v)

-- no power of physical spacing here. `P` is always for probability Haar and
-- the Gaussian ranking coefficients include every Hessian from the actual tree-slice action.
def kernel (d : Descent n c) (v : ℕ → ℝ) (f : Config G n → ℂ) (w k : ℕ) : ℂ :=
    ⟨ranking P d v (Complex.re ∘ f) (w+k), ranking P d v (Complex.im ∘ f) (w+k)⟩

include R h gV
include hf hG
/-- Core bill on just the finite history. `a` is `t` Gaussian scale; not the calendar spacing. -/
theorem evaluation : ∃ A E : ℝ, 0 ≤ A ∧ 0 ≤ E ∧ ∀ a : ℝ, 0 < a → ∀ (u : ℕ → ℝ) (δ : ℝ),
    d.Band M u → d.Band δ (u-v) →
      ‖a⁻¹ ^ w • d.conditioned (offset u a) f 1 - peval (kernel P d v f w) r a‖ ≤
        A*a^(r+1) + E*a^2*δ := by
  let x := Complex.reCLM; let y := Complex.imCLM
  obtain ⟨A,E,hA,hE,H⟩ := covers P R r h (tested x hf) (wanted x hG) gV
  obtain ⟨B,D,hB,hD,W⟩ := covers P R r h (tested y hf) (wanted y hG) gV
  refine ⟨A+B,E+D,by positivity,by positivity,fun a ha u δ hu hv => ?_⟩
  let Z := a⁻¹ ^ w • d.conditioned (offset u a) f 1 - peval (kernel P d v f w) r a
  have h₁ : ‖x Z‖ ≤ A*a^(r+1)+E*a^2*δ := by
    unfold Z; rw [map_sub,map_smul,← eval_map,← measured _ _ (room_ok d h) hf.neat]; exact H a ha u δ hu hv
  have h₂ : ‖y Z‖ ≤ B*a^(r+1)+D*a^2*δ := by
    unfold Z; rw [map_sub,map_smul,← eval_map,← measured _ _ (room_ok d h) hf.neat]; exact W a ha u δ hu hv
  change ‖Z‖ ≤ _
  exact ((Complex.norm_le_abs_re_add_abs_im Z)).trans ((add_le_add h₁ h₂).trans_eq (by ring))

omit hf hG
section loads
variable {ι : Type} [DecidableEq ι] (O : ι → Config G n → ℂ) (K : Census ι) (w : ι → ℕ)
    (H : ∀ i, d.Testable (O i)) (hg : ∀ i, d.grade (O i) (w i))
omit R h gV
include H in
lemma products (T : K.Mode) : d.Testable (fullProduct O T.val) where
  neat := continuous_finsetProd _ fun _ _ => (H _).neat
  invariant t V := Finset.prod_congr rfl fun _ _ => (H _).invariant t V
  smooth := contDiffAt_prod (fun _ _ => (H _).smooth)

abbrev weight (T : K.Mode) := ∑ i ∈ T.val, w i

def conditionalTerms (d : Descent n c) (v : ℕ → ℝ) (T : K.Mode) := kernel P d v (fullProduct O T.val) (weight K w T)

include hg in
lemma atGrade (T : K.Mode) : d.grade (fullProduct O T.val) (weight K w T) := by
  intro x
  convert! bill_product T.val w (fun i a => O i (d.fine 1 (d.tablePath (a • x)))) (fun i _ => hg i x) using 1
  funext t; change (∏ _ ∈ _, _) = _; rw [Finset.prod_apply]; rfl

include h R gV H hg
/-- One output on all tag subsets, common reset, total normalization, uses exactly the FULL
product. Includes separate markers for repeated sources. -/
theorem every_moment : ∃ A E : ℝ, 0 ≤ A ∧ 0 ≤ E ∧ ∀ a : ℝ, 0 < a → ∀ (u : ℕ → ℝ) (δ : ℝ),
    d.Band M u → d.Band δ (u-v) → ∀ (T : K.Mode),
      ‖a⁻¹ ^ weight K w T • (d.moments K (offset u a) O 1).part T -
        peval (conditionalTerms P O K w d v T) r a‖ ≤ A*a^(r+1) + E*a^2*δ := by
  choose A E hA hE H using fun T => evaluation P R r h (products O K H T) (atGrade O K w hg T) gV
  refine ⟨∑ T, A T, ∑ T, E T, Finset.sum_nonneg (fun i _ => hA i), Finset.sum_nonneg (fun i _ => hE i), fun a ha u δ hu hv T => ?_⟩
  apply (H T a ha u δ hu hv).trans
  have he := nonnegativeBand hv
  gcongr; exacts [Finset.single_le_sum (fun i _ => hA i) (Finset.mem_univ T), Finset.single_le_sum (fun i _ => hE i) (Finset.mem_univ T)]
end loads
end YM.RGComparison.Core16.WilsonXLocal
