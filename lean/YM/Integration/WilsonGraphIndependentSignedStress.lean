import YM.Integration.WilsonGraphAppointedStressCoordinates
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.SignedAxes
import YangMills.WilsonProof.NativeSupport.WardStressSeries

/-! The public signed-axis equation places each independent Ward coefficient
in the four Maxwell columns before the Wilson construction is chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress.Independent
open Maxwell Maxwell.Free Labels Climb Table Work.A01 Next.UVStress XSpace.Normalize
open _root_.YangMills
open _root_.YangMills.Matching.WardStress
open _root_.PhysicalMatching.H7StandaloneAppointedPublicWardRows (columns)
open scoped BigOperators Classical

variable {g : GaugeGroup} {M : MSbar.Coefficients (maxwellReference g)}
variable {C : Matching.Conversion (maxwellReference g)} {P : Series (maxwellReference g)}

theorem fieldTurn (law : Determined M C P) (k : ℕ) (s : Signed) (i j : Axis) :
    ori s.ortho 4 (P k i j) =
      ((_root_.YM.Maxwell.Free.tilt s i * _root_.YM.Maxwell.Free.tilt s j : ℝ) : ℂ) • P k (s.perm i) (s.perm j) := by
  have signs (a : Axis) : _root_.YM.Maxwell.Free.tilt s a = 1 ∨ _root_.YM.Maxwell.Free.tilt s a = -1 := by
    unfold _root_.YM.Maxwell.Free.tilt
    split <;> simp
  let q : Sec g.core 4 := ((_root_.YM.Maxwell.Free.tilt s i * _root_.YM.Maxwell.Free.tilt s j : ℝ) : ℂ) • P k (s.perm i) (s.perm j)
  exact ((IssuedMaxwell.SignedAxes.original s (P k i j) q).mp
    (law.signedAxes k s.perm (_root_.YM.Maxwell.Free.tilt s) (Ortho.motion s.ortho) signs (heads s) i j)).symm

theorem filedTensor (F : Frames g.core) (law : Determined M C P) (k : ℕ) :
    RawTensor (Free.hierarchy F).spin (fun i j => (Free.fields F 4).symm (P k i j)) := by
  let b := Free.fields F 4
  intro s i j
  simp_rw [Complex.ofReal_mul, mul_smul, ← Finset.smul_sum]
  simp_rw [eps_column]
  apply b.injective
  have motion : b ((freeTable F).mirror (Free.hierarchy F).spin 4 s (b.symm (P k i j))) =
      ori s.ortho 4 (b (b.symm (P k i j))) :=
    Subtype.ext (Free.address_motion F s (b.symm (P k i j)))
  rw [motion, LinearEquiv.apply_symm_apply, fieldTurn law k s i j]
  have signValue (a : Axis) : eps s a = _root_.YM.Maxwell.Free.tilt s a := by simp [eps, Signed.matrix_at, _root_.YM.Maxwell.Free.tilt]
  simp only [map_smul, b, LinearEquiv.apply_symm_apply, signValue, Complex.ofReal_mul, mul_smul]
  rfl

theorem original (hg : g.core.Simple) (law : Determined M C P) (k : ℕ) :
    ∃ u : Fin 4 → ℂ, ∀ i j, P k i j = ∑ l, u l • columns hg i j l := by
  let F := Labels.frames g.core
  let J : (freeTable F).Stress := fun i j => (Free.fields F 4).symm (P k i j)
  obtain ⟨u, hu⟩ := PublicPanels.signedTensorCoordinates F hg (Free.hierarchy F).spin J
    (filedTensor F law k)
  refine ⟨u, fun i j => Subtype.ext ?_⟩
  change (P k i j).val = ((maxwellReference g).sector 4).subtype (∑ l, u l • columns hg i j l)
  have address : Free.address F 4 (J i j) = (P k i j).val := by
    simp only [J, Free.address_eval, LinearEquiv.apply_symm_apply]
  refine (address.symm.trans (hu i j)).trans ?_
  calc
    (∑ l : Fin 4, u l • (columns hg i j l).val) =
        ∑ l : Fin 4, ((maxwellReference g).sector 4).subtype (u l • columns hg i j l) :=
      Finset.sum_congr rfl (fun l _ => rfl)
    _ = _ := (map_sum ((maxwellReference g).sector 4).subtype
      (fun l : Fin 4 => u l • columns hg i j l) Finset.univ).symm

end YM.UVNext.FreeStress.Independent
end

