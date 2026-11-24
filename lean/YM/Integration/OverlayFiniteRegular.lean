import YM.GapsI.Many.Seat
import YM.MergeProof.Garnish
import YM.MergeProof.Endow
import YM.Push.ABSOLUTE_SUMS.Product

/-!
The literal masked regular rows of an actual Overlay.Bands presentation,
aggregated over the finite set of original supports.  The same rooted Hit
price is retained.  No term is truncated and no global volume estimate is
used as the output price.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.OverlayFiniteRegular
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay
open MergeProof MergeProof.Accent Push Push.AbsoluteSums
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V : Type} [Fintype V] [DecidableEq V]
    {B : Census V} {P : Rep G n} (A : Overlay.Bands B P)

def row : Support n → Config G n → Poly B := tally A.support A.ray

variable (hA : A.Active)

include hA in
/-- Each original row already has its actual healthy mask and full root support. -/
theorem ray_burns (i : ℕ) :
    Burns A.origins (A.support i) (A.ray i) P.p.threshold := by
  have hr := hA.regular i
  have hb : Borne A.origins (A.support i) (A.ray i) P.p.threshold := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro U W hUW hFlags
      apply congrArg (Poly.send (A.rays i))
      have he : Healthy P.p.threshold (A.support i) U ↔
          Healthy P.p.threshold (A.support i) W := by
        simp only [Healthy, disjoint_iff_inter_eq_empty, hFlags]
      by_cases hu : Healthy P.p.threshold (A.support i) U
      · rw [masked_eq _ _ _ _ hu, masked_eq _ _ _ _ (he.mp hu)]
        exact hr.sites U W hUW
      · rw [masked_ne _ _ _ _ hu, masked_ne _ _ _ _ (mt he.mpr hu)]
    · intro g U
      apply congrArg (Poly.send (A.rays i))
      by_cases hu : Healthy P.p.threshold (A.support i) U
      · rw [masked_eq _ _ _ _ (by simpa only [Healthy, gauge_flags] using hu),
          masked_eq _ _ _ _ hu]
        exact hr.symmetry g U
      · rw [masked_ne _ _ _ _ (by simpa only [Healthy, gauge_flags] using hu),
          masked_ne _ _ _ _ hu]
    · intro q
      exact (Poly.part_cont q).measurable.comp
        ((Overlay.Bands.sends (A.rays i)).measurable.comp
          (masked_measurable _ _ _ hr.borel))
    · intro U
      exact GridApprox.Nil.scope_send _ _ _ (fun v hv => hA.pins i v hv)
  refine ⟨hb, ?_, ?_⟩
  · intro U hu
    by_contra hn
    apply hu
    unfold Overlay.Bands.ray
    rw [masked_ne _ _ _ _ hn, Poly.send_zero]
  · intro U
    unfold Overlay.Bands.ray
    rw [Poly.part_send, if_neg]
    intro he
    exact (hA.proper i).ne_empty (congrArg Subtype.val he.symm)

variable {t : ℕ → ℕ} {w : V → ℝ} {σ : ℝ} {v : ℕ → ℝ}
    (hGrade : GapsI.Seat.Graded A t w σ v)
    (hw : ∀ i, 0 < w i) (hσ : 0 ≤ σ)

omit [Fintype V] in
include hA hGrade hw hσ in
/-- The native graded regular budget gives a common coefficient envelope,
with exactly its original price at grade zero. -/
theorem raw_towed : Towed w A.support A.ray P.p.B σ (v 0) := by
  obtain ⟨q, hq, hHit⟩ := hGrade.sounds
  let c i := Poly.toll w (A.rays i) * q i
  have hc i : 0 ≤ c i := mul_nonneg (Poly.worth hw _).le (hq i).1
  have hH : Ac.Hit A.support P.p.B c σ (v 0) := by
    simpa only [Nat.zero_le, ↓reduceIte] using hHit 0
  have hsupport i : (A.support i).Nonempty := by
    obtain ⟨j, hj⟩ := hA.proper i
    exact ⟨A.origins j, hA.pins i j hj⟩
  have he := Product.everyone_ne A.support P.p.B hc (fun i _ => hsupport i) hH
  have hs : Summable c := he.2.1.of_nonneg_of_le hc (fun i =>
    le_mul_of_one_le_right (hc i)
      (Real.one_le_exp (mul_nonneg hσ (by positivity))))
  refine ⟨c, hs, hH, ?_⟩
  intro i
  apply satin (masked P.p.threshold (A.support i) (A.H i)) (A.rays i) (q i) (hq i).1
  intro U
  by_cases hu : Healthy P.p.threshold (A.support i) U
  · rw [masked_eq _ _ _ _ hu]
    obtain ⟨j, hj⟩ := hA.proper i
    exact ((hq i).2 (A.origins j) (hA.pins i j hj)).2 U hu [] (by simp) (by simp)
  · rw [masked_ne _ _ _ _ hu, norm_zero]
    exact (hq i).1

omit [Fintype V] in
include hA hGrade hw hσ in
/-- Finite support aggregation preserves the same rooted numerical budget. -/
theorem row_towed : Towed w id (row A) P.p.B σ (v 0) :=
  towing A.support A.ray (raw_towed A hA hGrade hw hσ) hw

omit [Fintype V] in
include hA hGrade hw hσ in
theorem row_part (s : Support n) (U : Config G n) (q : B.Mode) :
    (row A s U).part q =
      ∑' i : {i : ℕ // A.support i = s}, (A.ray i.val U).part q := by
  exact Poly.share (((raw_towed A hA hGrade hw hσ).repair hw U).2.comp_injective
    Subtype.val_injective) q

include hA hGrade hw hσ in
/-- Every original row remains, and zero scalar units are not silently inserted. -/
theorem sum_rows (hzero : A.units = 0) (U : Config G n) :
    (∑ s : Support n, row A s U) = A.extra U := by
  rw [Overlay.Bands.extra, hzero]
  simp only [Pi.zero_apply, Poly.send_zero, sum_const_zero, zero_add]
  change (∑ s : Support n, cram A.support (fun i => A.ray i U) s) = _
  rw [← tsum_fintype (L := .unconditional (Support n))]
  exact (((raw_towed A hA hGrade hw hσ).repair hw U).2.hasSum.tsum_fiberwise
    A.support).tsum_eq

include hA hGrade hw hσ in
/-- The finite row still uses its original mask and original support. -/
theorem row_burns (s : Support n) : Burns A.origins s (row A s) P.p.threshold := by
  have hb (i : {i : ℕ // A.support i = s}) :
      Burns A.origins s (A.ray i.val) P.p.threshold := by
    simpa only [i.property] using ray_burns A hA i.val
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro U W hUW hFlags
    exact tsum_congr (fun i => (hb i).home U W hUW hFlags)
  · intro g U
    exact tsum_congr (fun i => (hb i).turns g U)
  · intro q
    have he : (fun U => (row A s U).part q) =
        (fun U => ∑' i : {i : ℕ // A.support i = s}, (A.ray i.val U).part q) :=
      funext (fun U => row_part A hA hGrade hw hσ s U q)
    rw [he]
    exact Measurable.tsum (fun i => (hb i).me q)
  · intro U q hq
    rw [row_part A hA hGrade hw hσ s U q]
    exact (tsum_congr (fun i => (hb i).scope U q hq)).trans tsum_zero
  · intro U hu
    by_contra hn
    apply hu
    exact (tsum_congr (fun i => not_ne_iff.mp (mt ((hb i).permits U) hn))).trans tsum_zero
  · intro U
    rw [row_part A hA hGrade hw hσ s U B.quiet]
    exact (tsum_congr (fun i => (hb i).sil U)).trans tsum_zero

/-- The finite old support rows together with every literal constant singleton. -/
abbrev Key := Support n ⊕ V

def region : Key (n := n) (V := V) → Support n :=
  Sum.elim id (fun i => {A.origins i})

def withUnits : Key (n := n) (V := V) → Config G n → Poly B :=
  Sum.elim (row A) (fun i _ => Poly.send (B.fire i) (A.units i))

/-- Literal constant terms are supported at their original marked root. -/
theorem unit_borne (i : V) :
    Borne A.origins {A.origins i}
      (fun _ : Config G n => Poly.send (B.fire i) (A.units i)) P.p.threshold := by
  refine ⟨fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ => measurable_const, ?_⟩
  intro U
  apply GridApprox.Nil.scope_send
  intro j hj
  have he : j = i := by
    change j ∈ ({i} : Finset V) at hj
    exact mem_singleton.mp hj
  subst j
  exact mem_singleton_self _

include hA hGrade hw hσ in
/-- This identity retains nonzero scalar units as well as all masked rays. -/
theorem sum_withUnits (U : Config G n) :
    (∑ i : Key (n := n) (V := V), withUnits A i U) = A.extra U := by
  have hrows : (∑ s : Support n, row A s U) = ∑' i, A.ray i U := by
    change (∑ s : Support n, cram A.support (fun i => A.ray i U) s) = _
    rw [← tsum_fintype (L := .unconditional (Support n))]
    exact (((raw_towed A hA hGrade hw hσ).repair hw U).2.hasSum.tsum_fiberwise
      A.support).tsum_eq
  rw [Fintype.sum_sum_type]
  change (∑ s : Support n, row A s U) +
    (∑ i : V, Poly.send (B.fire i) (A.units i)) = _
  rw [hrows]
  exact add_comm _ _

include hA hGrade hw hσ in
theorem withUnits_borne (i : Key (n := n) (V := V)) :
    Borne A.origins (region A i) (withUnits A i) P.p.threshold := by
  cases i with
  | inl s => exact (row_burns A hA hGrade hw hσ s).toBorne
  | inr j => exact unit_borne A j

include hA hGrade hw hσ in
theorem withUnits_quiet (i : Key (n := n) (V := V)) (U : Config G n) :
    (withUnits A i U).part B.quiet = 0 := by
  cases i with
  | inl s => exact (row_burns A hA hGrade hw hσ s).sil U
  | inr j =>
      change (Poly.send (B.fire j) (A.units j)).part B.quiet = 0
      rw [Poly.part_send, if_neg (Ne.symm (B.fire_hot j))]

include hw hσ in
/-- Constants cost only local occupancy; the total number of markers does
not enter the price.  Their exponential support factor is retained. -/
theorem units_towed {C : ℝ} {localCount : ℕ}
    (hC : 0 ≤ C) (hUnits : ∀ i, w i * ‖A.units i‖ ≤ C)
    (hOcc : Extra.Multi.Occupancy A.origins localCount) :
    Towed w (fun i => {A.origins i})
      (fun i (_ : Config G n) => Poly.send (B.fire i) (A.units i))
      P.p.B σ (localCount * (Real.exp σ * C)) := by
  let c i := w i * ‖A.units i‖
  have hc i : 0 ≤ c i := mul_nonneg (hw i).le (norm_nonneg _)
  have hcover i : (coverNumber P.p.B ({A.origins i} : Support n) : ℝ) ≤ 1 := by
    exact_mod_cast (Corona.cover_mono (Lattice.halo_subset 0 {A.origins i}) P.p.B).trans
      (show coverNumber P.p.B (halo 0 {A.origins i}) ≤ 1 from by
        simpa using Corona.tile (A.origins i) 0 P.p.B P.p.B_pos)
  have hterm i : c i * Real.exp (σ * coverNumber P.p.B ({A.origins i} : Support n))
      ≤ Real.exp σ * C := by
    calc
      _ ≤ C * Real.exp σ := mul_le_mul (hUnits i)
        (Real.exp_monotone (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (hcover i) hσ))
        (Real.exp_pos _).le hC
      _ = _ := mul_comm _ _
  refine ⟨c, Summable.of_finite, ?_, ?_⟩
  · intro x
    refine ⟨fun i => ?_, Summable.of_finite, ?_⟩
    · dsimp only
      split_ifs
      · exact mul_nonneg (hc i) (Real.exp_pos _).le
      · exact le_rfl
    rw [tsum_fintype]
    simp only [mem_singleton, ← Finset.sum_filter]
    calc
      _ ≤ ∑ i ∈ (Finset.univ.filter (fun i => x = A.origins i)),
          Real.exp σ * C := Finset.sum_le_sum (fun i _ => hterm i)
      _ = ((Finset.univ.filter (fun i => x = A.origins i)).card : ℝ) *
          (Real.exp σ * C) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast
        (show (Finset.univ.filter (fun i => x = A.origins i)).card ≤ localCount from by
          simpa only [eq_comm] using hOcc x))
        (mul_nonneg (Real.exp_pos _).le hC)
  · intro i
    have hs := satin (w := w) (fun _ : Config G n => A.units i) (B.fire i)
      ‖A.units i‖ (norm_nonneg _) (fun _ => le_rfl)
    simpa only [Poly.solo_toll] using hs

include hA hGrade hw hσ in
/-- A complete finite regular presentation, including its original units,
with the masked and constant bills added explicitly. -/
theorem withUnits_towed {C : ℝ} {localCount : ℕ}
    (hC : 0 ≤ C) (hUnits : ∀ i, w i * ‖A.units i‖ ≤ C)
    (hOcc : Extra.Multi.Occupancy A.origins localCount) :
    Towed w (region A) (withUnits A) P.p.B σ
      (v 0 + localCount * (Real.exp σ * C)) := by
  obtain ⟨a, _, ha, hA'⟩ := row_towed A hA hGrade hw hσ
  obtain ⟨b, _, hb, hB'⟩ := units_towed A hw hσ hC hUnits hOcc
  refine ⟨Sum.elim a b, Summable.of_finite, ?_, ?_⟩
  · intro x
    refine ⟨fun i => ?_, Summable.of_finite, ?_⟩
    · cases i with
      | inl s => exact (ha x).1 s
      | inr j => exact (hb x).1 j
    · rw [tsum_fintype, Fintype.sum_sum_type]
      have hax := (ha x).2.2
      have hbx := (hb x).2.2
      rw [tsum_fintype] at hax hbx
      exact add_le_add hax hbx
  · intro i
    cases i with
    | inl s => exact hA' s
    | inr j => exact hB' j

end YM.Integration.OverlayFiniteRegular
