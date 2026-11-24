import YM.OPE.Frame.Ordered
/-!
# Uniformity also under arbitrary mixtures, and joint position (measure) tests of bounded mass

Term-wise genuine measurements (these tests are *separated*), no independence of slots assumed
for the position tests. Uniform in each chosen probability measure on the characters as well as
literally **all** viewers, with the same coefficients. Averaging does not yield a new detection
convention; no exceptional characters permitted.
-/
set_option autoImplicit false
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
namespace YM.OPE.Frame
variable {G : Gauge} {C : Family G} {U : Extraction.Order} {S : Table C.book} {F : Spec.Final C U S}
variable {I J : Type} [Fintype I] [Fintype J] {x : I → E4} {y : J → E4} {r : ℝ} {o : E4}
    (A : I → S.Tag) (B : J → S.Tag) (n : ℕ)

variable (F) in
/-- Mixtures for testing consist of all the former viewers (including `none`, the unselected),
and any probability average over the characters of F. -/
abbrev Audience := Viewers F ⊕ ProbabilityMeasure F.α.space.X
noncomputable def heard (μ : Audience F) (x : I → E4) (A : I → S.Tag) : ℂ :=
  match μ with
  | .inl w => sense (spectator F w) x A
  | .inr w => ∫ k, sense (F.α.ensemble k) x A ∂(w : Measure _)

private lemma phase_family_cont (hx : Injective x) : Continuous fun i=> sense (F.α.ensemble i) x A := by
  simp_rw [sense, ← character_sees F _ _ _ hx]; exact F.phase.phase.decomposition.weak _
lemma integrable_mix (μ : Measure F.α.space.X) [IsFiniteMeasure μ] (hx : Injective x) :
    Integrable (fun i=> sense (F.α.ensemble i) x A) μ := (phase_family_cont A hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Get a univariate moving-phase rate-zero bound as a special case. -/
private lemma whole_fast {R : Type} {L : Filter R} [L.NeBot] {T : R→ ℝ} {X : R → I → E4} (w : R → Viewers F) (H : Services C U S)
    (hT : Tendsto T L atTop) (hx : Kept L T 0 X) : RateLE L T (fun i=> sense (spectator F (w i)) (X i) A) 0 := by
  let E : Fin 0 → S.Tag := Fin.elim0; let Y (_:R) : Fin 0 → E4 := Fin.elim0
  have he : Kept L T 0 Y := fun _ _ => Eventually.of_forall fun i a => Fin.elim0 a
  have hp : Intervals L T 0 Y X := fun _ _ => Eventually.of_forall fun i a => Fin.elim0 a
  apply ((sense_base E A hT H w he hx hp le_rfl le_rfl).mono (by simp)).congr
  filter_upwards [hx.inject] with i hi; unfold sense; rw [beside_commutes]; exact observe_empty _ _ _ _ _ (spectate F _) hi
private lemma all_cap (F : Spec.Final C U S) (ε : ℝ) (h : 0 < ε) (H : Services C U S) :
    ∃ t : ℝ, ∀ (x : I → E4) (w : Viewers F), Apart ε x → ‖sense (spectator F w) x A‖ ≤ t := by
  by_contra! hh
  let T (n:ℕ) := (n:ℝ); have ht : Tendsto T atTop atTop := tendsto_natCast_atTop_atTop
  choose X w he hu using fun n => hh (Real.exp (T n))
  have hx : Kept atTop T 0 X := by intro r hr; filter_upwards [(RateIs.const ht h).overtakes (RateLE.exp (-r) ht) ht (neg_lt_zero.mpr hr)] with i hi using (he i).short hi.le
  obtain ⟨i,hi⟩ := (whole_fast A w H ht hx 1 zero_lt_one).exists; specialize hu i; rw [one_mul] at hi; exact hu.not_ge hi
lemma mix_cont (μ : Audience F) (H : Services C U S) (h : Injective x) : ContinuousAt (fun p=> heard μ p A) x := by
    cases μ with
    | inl w => exact smooth_observe (spectator F w) (spectate F w).smooth (deploy ∘ A) h
    | inr w =>
      have hp : ∀ᶠ r:ℝ in 𝓝[>]0, ∀ᶠ k in 𝓝 x, Apart r k := by
        have he (i j : I) : ∀ᶠ r:ℝ in 𝓝[>] 0, ∀ᶠ k in 𝓝 x, i ≠ j → r < ‖k i-k j‖ := by
          by_cases hh : i=j; · simp [hh]
          have hz : 0 < ‖x i-x j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (h.ne hh))
          refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_; filter_upwards [gt_mem_nhds hz] with r hr; exact ((show Continuous fun x:I→E4=> ‖x i-x j‖ from by fun_prop)|>.tendsto x|>.eventually (lt_mem_nhds (show r < ‖x i-x j‖ from hr))).mono fun k hk _ => hk
        simp_rw [Apart,eventually_all]; intro i j hh; exact (he i j).mono fun _ hv=> hv.mono fun _ hf=> hf hh -- eventually_all through → moves already?
      obtain ⟨r,hr,hx⟩ := ((show ∀ᶠ r:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin).and hp).exists
      obtain ⟨t,ht⟩ := all_cap A F r hr H
      exact continuousAt_of_dominated (μ := (w:Measure F.α.space.X)) (hx.mono fun i hi=> (integrable_mix (F:=F) A _ (hi.coin hr.le)).aestronglyMeasurable)
        (hx.mono fun i hi=>Eventually.of_forall fun j=> ht i (some j) hi) (integrable_const t)
        (Eventually.of_forall fun j=> smooth_observe (F.α.ensemble j) (spectate F (some j)).smooth (deploy ∘ A) h)

namespace Scheme
variable (Z : Scheme F)
def play (μ : Audience F) (n : ℕ) (r : ℝ) (A : I → S.Tag) (x : I → E4) (o : E4) (y : J → E4) (B : J → S.Tag) :=
  heard μ (beside x y) (beside A B) - ∑ i∈ limits Z.rings n, Z.coeff r i A x o * heard μ (beside (sole o) y) (beside (sole (Z.representation.label i)) B)
lemma play_one (w : Viewers F) : Z.play (.inl w) n r A x o y B = Z.residue (spectator F w) n r A x o y B := rfl
lemma play_mix (μ : ProbabilityMeasure F.α.space.X) (h : Injective (beside x y)) (hh : Injective (beside (sole o) y)) :
    Z.play (.inr μ) n r A x o y B = ∫ k, Z.residue (spectator F (some k)) n r A x o y B ∂(μ:Measure _) := by
  unfold residue play
  have ht i : Integrable (fun k=> Z.coeff r i A x o * sense (F.α.ensemble k) (beside (sole o) y) (beside (sole (Z.representation.label i)) B)) (μ:Measure _) := (integrable_mix (F:=F) _ (μ:Measure _) hh).const_mul _
  simp only [any_selected]; rw [integral_sub (integrable_mix (F:=F) (beside A B) (μ:Measure _) h) (integrable_finsetSum _ (fun i _=> ht i)), integral_finsetSum _ (fun i _=> ht i)]
  simp_rw [MeasureTheory.integral_const_mul]; rfl
lemma play_bound (μ : Audience F) (h : Injective (beside x y)) (hh : Injective (beside (sole o) y)) :
    ‖Z.play μ n r A x o y B‖ ≤ ‖Z.remainder n r A x o y B‖ := by
  have hp w : ‖Z.residue (spectator F w) n r A x o y B‖ ≤ ‖Z.remainder n r A x o y B‖ := by rw [Z.phase_error _ _ _ _ _ _ _ h hh]; exact glance_bound .. -- _
  cases μ with
  | inl μ => rw [Z.play_one]; exact hp _
  | inr μ => rw [Z.play_mix _ _ _ _ h hh]; apply (norm_integral_le_of_norm_le_const (Eventually.of_forall fun i : F.α.space.X => hp (some i))).trans; simp
end Scheme
end YM.OPE.Frame
