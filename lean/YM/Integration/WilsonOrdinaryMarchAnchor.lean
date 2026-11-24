import YM.Integration.WilsonOrdinarySampleReader
import YM.RG12.Canonical.Conclude

/-! An actual fixed coordinate anchor for the original consecutive Gram march. -/
noncomputable section
namespace YM.Integration.WilsonOrdinaryMarchAnchor
open Filter Set Spec Climb OPE RG12 RG12.Frames RG17 SharpGram Trace.Pilot
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (J : ℝ → PhysMS.tower S) (d : ℕ)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field d
local notation "V" => Desk.Sector F.sector.derivatives d
local notation "X" => Col V

/-- The measured frames use the predetermined free coordinates of the fixed horizon. -/
def atSample (T : X ≃ₗ[ℂ] D) (i : ℕ) : X ≃ₗ[ℂ] S.Field d :=
  T.trans (J (Sample.length i) d)

/-- No IR normalization of the prescribed frames is required. Choose one physical
date where every one of the finitely many rise identities holds; the given coherent
field prescription fixes the actual graded fields. -/
theorem original (H : PhysMS.Leading F J) (O : Prescription F.sector.derivatives) (coh : O.Coherent) :
    ∃ T : X ≃ₗ[ℂ] D, ∀ᶠ r in trail,
      triangular V ((Desk.official O coh d).symm.toLinearMap.comp (T.trans (J r d)).toLinearMap) := by
  let mark (r : ℝ) := ∀ (i : Grade d) (x : (Bel C.book).Field i.val),
    J r d ((Maxwell.Free.scheme C.labels).rise i.is_le x) =
      F.sector.derivatives.rise i.is_le (J r i x)
  have near : ∀ᶠ r in trail, mark r := eventually_all.mpr (fun i : Grade d => H.raised i.is_le)
  obtain ⟨s,hs⟩ := near.exists
  let T := (Desk.official O coh d).trans (J s d).symm
  refine ⟨T,near.mono ?_⟩
  intro r hr
  apply Desk.compatible O coh d F.room.kernel.laws.toSymmetric F.phase.transport.injection
  intro i x
  obtain ⟨z,hz⟩ := Desk.fits O coh d i x
  let v := (J s i).symm z
  have lift : T (put V i x) = (Maxwell.Free.scheme C.labels).rise i.is_le v := by
    apply (J s d).injective
    change J s d ((J s d).symm (Desk.official O coh d (put V i x))) = _
    rw [LinearEquiv.apply_symm_apply,hs i v]
    simpa [v] using hz.symm
  refine ⟨J r i v,?_⟩
  change F.sector.derivatives.rise i.is_le (J r i v) = J r d (T (put V i x))
  rw [← hr i v,lift]

/-- When evaluated on the actual displayed columns, the varying dual-frame
measure is one fixed norm `‖T x‖`. It obeys all three conditions of `Frames.Tests`,
uniformly in the step. -/
theorem stable (T : X ≃ₗ[ℂ] D) : ∃ K : ℝ, ∀ i : ℕ,
    Tests ((fun z => ‖(J (Sample.length i) d).symm z‖) ∘ (atSample F J d T i).toLinearMap) K := by
  let U := T.toLinearMap.toContinuousLinearMap
  let W := T.symm.toLinearMap.toContinuousLinearMap
  let K := max 1 (max ‖U‖ ‖W‖)
  refine ⟨K,?_⟩; intro i
  have eq : ((fun z => ‖(J (Sample.length i) d).symm z‖) ∘ (atSample F J d T i).toLinearMap) =
      fun x : X => ‖T x‖ := by ext x; simp [atSample]
  rw [eq]
  constructor
  · exact le_max_left ..
  · intro x; exact (U.le_opNorm x).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) (norm_nonneg _))
  · intro x
    have hz : ‖x‖ ≤ ‖W‖ * ‖T x‖ := by simpa [W] using W.le_opNorm (T x)
    exact hz.trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (norm_nonneg _))
  · intro x y; rw [map_add]; exact norm_add_le ..
  · intro c x hc; rw [map_smul,norm_smul,Complex.norm_real,Real.norm_of_nonneg hc]

end YM.Integration.WilsonOrdinaryMarchAnchor
