import YM.Integration.FVA1Physical.Sources.AnchoredMass
import YM.Extra.MULTISOURCE_BOUNDS.Columns

/-! A terminal source price using the reference stencil and the actual fine
cutoff. Period, origins and orientations do not enter this price. -/

namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics

open Filter MeasureTheory Lattice RG Wilson Source Extra.Histories Extra.Multi Next.Foundations
open OPE.Therm LocalLTE.Sail MergeProof MergeProof.Accent YM.Integration.FVA1Physical
open scoped BigOperators

variable {G : Gauge} {H : History G} {N n : ℕ} {I : Type}

noncomputable def stencilCost (H : History G) (N d : ℕ)
    (v : ((Labels.frames G).level d).Coeff) : ℝ :=
  BasisCost.price (localSection G d) *
    ((Labels.frames G).level d).coeffSize (((Labels.frames G).level d).scaled
      (H.levels.clock.threshold N)⁻¹ v)

theorem terminalFieldSize_le_stencil (Y : Batch H N n I) (j : I) :
    terminalFieldSize Y j ≤ stencilCost H N (Y.demand j) (Y.voice j) := by
  let F := (Labels.frames G).level (Y.demand j)
  let C := localSection G (Y.demand j)
  let w := F.scaled (H.levels.clock.threshold N)⁻¹ (Y.voice j)
  let a : ℂ := (H.S.a N : ℂ) ^ Y.demand j
  have ha : a ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (H.S.a_pos N).ne')
  unfold terminalFieldSize
  apply (ContinuousMap.norm_le _ (mul_nonneg (zero_le_one.trans (BasisCost.price_pos C))
    (BasisCost.coeff_nonneg w))).mpr
  intro U
  change ‖a * Motion.scalar (Y.motion j) (a⁻¹ * C.places w 0
    (pull (Y.motion j).1 (Y.origin N j) U))‖ ≤ _
  rw [norm_mul, Motion.norm_scalar, norm_mul, norm_inv, ← mul_assoc,
    mul_inv_cancel₀ (norm_pos_iff.mpr ha).ne', one_mul]
  exact BasisCost.full C w _ _

noncomputable def stencilInsertionBound [Fintype I] (H : History G) (N : ℕ)
    (d : I → ℕ) (v : ∀ j, ((Labels.frames G).level (d j)).Coeff) : ℝ :=
  ∑ k ∈ Finset.range (Fintype.card I + 1),
    ‖((k.factorial : ℂ)⁻¹)‖ * (∑ j, stencilCost H N (d j) (v j)) ^ k

theorem terminalInsertionBound_le_stencil [Fintype I] (Y : Batch H N n I) :
    terminalInsertionBound Y ≤ stencilInsertionBound H N Y.demand Y.voice := by
  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => norm_nonneg _)
    (Finset.sum_le_sum fun j _ => terminalFieldSize_le_stencil Y j) k

/-- For fixed source coefficients and fine cutoff the entire bound, including
the insertion prefactor, is independent of lattice period and field positions. -/
theorem physicalAnchor_stencilBound (hH : H.Selected) (hP : Poetry H.levels) (hG : G.Simple) :
    ∀ᶠ i : ℕ in atTop, ∀ (N n : ℕ) (hi : i ≤ N) (A : Support (H.S.side i n))
      (I : Type) [DecidableEq I] [Fintype I] (B : Marker.Census I) (Y : Batch H N n I)
      (u : B.Mode → ℂ), (∀ j, ‖u j‖ ≤ 1) →
      let bad := {v : Config G (H.S.side i n) | ¬ Healthy (H.rep N n i).p.threshold A v}
      ‖(∫ v in bad, modeTest u (gust H N n N (Y.raw B) i hi v) ∂prior G (H.S.side i n)) /
        (Wilson.partition G (H.S.side N n) (H.β N n N) : ℂ)‖ ≤
        stencilInsertionBound H N Y.demand Y.voice *
          (((A.card * 5 ^ 4 * Fintype.card PlaqAxes : ℕ) : ℝ) * vanishP H.levels i) := by
  filter_upwards [physicalAnchor_testBound hH hP hG] with i h
  intro N n hi A I _ _ B Y u hu bad
  exact (h N n hi A I B Y u hu).trans (mul_le_mul_of_nonneg_right
    (terminalInsertionBound_le_stencil Y) (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le))

end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
