import YM.Integration.FVA1Physical.Sources.StencilCosts

/-! A joint bound for all coefficients of the actual transported physical
insertion. The independent test is selected after fixing the coarse field.
This avoids a loss proportional to the number of marker modes. -/

namespace YM.Integration.FVA1Physical.Round2

open MeasureTheory Lattice RG Wilson Source Extra.Histories
open PhysicalNext.Repeat.Legato.Bandage.Harmonics MergeProof.Accent LocalLTE.Sail

variable {I : Type} [DecidableEq I] {B : Marker.Census I}

theorem price_realized (X : Marker.Poly B) :
    ∃ u : B.Mode → ℂ, (∀ j, ‖u j‖ ≤ 1) ∧
      modeTest u X = (Marker.Poly.price (fun _ => 1) X : ℂ) := by
  let u := fun j => (‖X.part j‖ : ℂ) / X.part j
  refine ⟨u, ?_, ?_⟩
  · intro j
    by_cases hj : X.part j = 0
    · simp [u, hj]
    simp [u, Complex.norm_real, (norm_pos_iff.mpr hj).ne']
  unfold modeTest Marker.Poly.price
  simp only [Marker.Poly.toll, Finset.prod_const_one, one_mul, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : X.part j = 0
  · simp [u, hj]
  exact div_mul_cancel₀ _ hj

variable {G : Gauge} {H : History G} {N n : ℕ} [Fintype I]

/-- The pointwise total variation of all marked coefficients is dominated by
the actual coarse vacuum times the fine stencil price, with arbitrary flags. -/
theorem coarsePhysicalPrice (hH : H.Selected) (B : Marker.Census I) (Y : Batch H N n I)
    (i : ℕ) (hi : i ≤ N) (v : Config G (H.S.side i n)) :
    Marker.Poly.price (fun _ => 1) (gust H N n N (Y.raw B) i hi v) ≤
      (H.rep N n i).eval v * stencilInsertionBound H N Y.demand Y.voice := by
  obtain ⟨u, hu, he⟩ := price_realized (gust H N n N (Y.raw B) i hi v)
  have hq := SectorNext.Vacuum.strictly H hH N n i hi v
  have hb := gust_vacuum_bound H hH N n (fun w => modeTest u (Y.raw B w)) _
    (physicalSeed_testBound B Y hH u hu) i hi v
  rw [← congrFun (gust_modeTest_eq H N n (Y.raw B) (physicalSeed_integrable H hH B Y) u i hi) v,
    he, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hq.le),
    Real.norm_of_nonneg (Marker.Poly.nonnegative (fun _ => zero_lt_one) _)] at hb
  exact ((inv_mul_le_iff₀ hq).mp hb).trans
    (mul_le_mul_of_nonneg_left (terminalInsertionBound_le_stencil Y) hq.le)

end YM.Integration.FVA1Physical.Round2
