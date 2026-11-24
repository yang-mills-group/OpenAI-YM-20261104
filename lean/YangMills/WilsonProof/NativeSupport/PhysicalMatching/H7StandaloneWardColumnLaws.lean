import YM.Integration.WilsonGraphAppointedStressCoordinates
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.SignedAxes
import YangMills.WilsonProof.NativeSupport.WardStressSeries

set_option autoImplicit false
noncomputable section
namespace PhysicalMatching.H7StandaloneWardColumnLaws
open YM YM.Maxwell YM.Maxwell.Free YM.Labels YM.Climb YM.Table YM.Work.A01 YM.Next.UVStress
open YM.XSpace.Normalize YM.UVNext.FreeStress YM.UVNext.FreeStress.PublicPanels
open YangMills YangMills.Matching
open H7StandaloneAppointedPublicWardRows (columns)
open scoped BigOperators Classical
variable {g : YangMills.GaugeGroup}

def filed (hg : g.core.Simple) (u : Fin 4 → ℂ) (i j : YM.Axis) :
    (YangMills.maxwellReference g).sector 4 := ∑ k, u k • columns hg i j k

theorem nativeSymmetric (F : Frames g.core) (i j : YM.Axis) (k : Fin 4) :
    appointedSources F i j k = appointedSources F j i k := by
  by_cases e : i = j
  · subst j; rfl
  · fin_cases k <;> simp [appointedSources, e, Ne.symm e]
    exact panel_flip F i j

theorem nativeTurn (F : Frames g.core) (H : (freeTable F).RealSpin)
    (s : YM.Signed) (i j : YM.Axis) (k : Fin 4) :
    (freeTable F).mirror H 4 s (appointedSources F i j k) =
      ((eps s i * eps s j : ℝ) : ℂ) • appointedSources F (s.perm i) (s.perm j) k := by
  by_cases e : i = j
  · subst j
    fin_cases k <;> simp [appointedSources, near, (freeTable F).mirror_unit,
      panel_transfer, total_transfer, square_eps, map_add, map_neg, map_smul]
  · have pe : s.perm i ≠ s.perm j := fun h => e (s.perm.injective h)
    fin_cases k <;> simp [appointedSources, e, pe, panel_transfer, map_neg, smul_neg]

theorem weightedTurn (F : Frames g.core) (H : (freeTable F).RealSpin)
    (u : Fin 4 → ℂ) (s : YM.Signed) (i j : YM.Axis) :
    (freeTable F).mirror H 4 s (∑ k, u k • appointedSources F i j k) =
      ((eps s i * eps s j : ℝ) : ℂ) • ∑ k, u k • appointedSources F (s.perm i) (s.perm j) k := by
  simp only [map_sum, map_smul, nativeTurn F H, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact smul_comm (u k) (((eps s i * eps s j : ℝ) : ℂ)) _

theorem weightedTensor (F : Frames g.core) (H : (freeTable F).RealSpin)
    (u : Fin 4 → ℂ) :
    RawTensor H (fun i j => ∑ k, u k • appointedSources F i j k) :=
  column_tensor F H _ (weightedTurn F H u)

theorem fieldAddress (F : Frames g.core) (hg : g.core.Simple)
    (u : Fin 4 → ℂ) (i j : YM.Axis) :
    Free.fields F 4 (∑ k, u k • appointedSources F i j k) = filed hg u i j := by
  unfold filed
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  exact congrArg (fun x => u k • x) (Subtype.ext (addressColumns F hg i j k))

theorem symmetric (hg : g.core.Simple) (u : Fin 4 → ℂ) (i j : YM.Axis) :
    filed hg u i j = filed hg u j i := by
  let F := YM.Labels.frames g.core
  rw [← fieldAddress F hg u i j, ← fieldAddress F hg u j i]
  apply congrArg
  exact Finset.sum_congr rfl (fun k _ => congrArg (fun x => u k • x) (nativeSymmetric F i j k))

theorem fieldTurn (hg : g.core.Simple) (u : Fin 4 → ℂ) (s : YM.Signed) (i j : YM.Axis) :
    ori s.ortho 4 (filed hg u i j) =
      ((YM.Maxwell.Free.tilt s i * YM.Maxwell.Free.tilt s j : ℝ) : ℂ) • filed hg u (s.perm i) (s.perm j) := by
  let F := YM.Labels.frames g.core
  let v := ∑ k, u k • appointedSources F i j k
  have motion : Free.fields F 4 ((freeTable F).mirror (Free.hierarchy F).spin 4 s v) =
      ori s.ortho 4 (Free.fields F 4 v) := Subtype.ext (Free.address_motion F s v)
  have hsign (a : YM.Axis) : eps s a = YM.Maxwell.Free.tilt s a := by simp [eps, YM.Signed.matrix_at, YM.Maxwell.Free.tilt]
  rw [← fieldAddress F hg u i j, ← fieldAddress F hg u (s.perm i) (s.perm j)]
  change ori s.ortho 4 (Free.fields F 4 v) = _
  rw [← motion]
  dsimp only [v]
  rw [weightedTurn F (Free.hierarchy F).spin u, map_smul, hsign, hsign]
  rfl

theorem signedCoordinates (σ : Equiv.Perm YangMills.Axis) (sign : YangMills.Axis → ℝ)
    (U : YangMills.Spacetime ≃ₗᵢ[ℝ] YangMills.Spacetime)
    (hs : ∀ a, sign a = 1 ∨ sign a = -1)
    (hu : ∀ a, U (EuclideanSpace.single a 1) = sign a • EuclideanSpace.single (σ a) 1) :
    ∃ s : YM.Signed, s.perm = σ ∧ YM.Maxwell.Free.tilt s = sign ∧ YM.Ortho.motion s.ortho = U := by
  let s : YM.Signed := ⟨σ, fun a => decide (sign a = -1)⟩
  have sk : YM.Maxwell.Free.tilt s = sign := by
    funext a
    rcases hs a with h | h <;> simp [YM.Maxwell.Free.tilt, s, h] <;> norm_num
  refine ⟨s, rfl, sk, ?_⟩
  have column (a : YM.Axis) : YM.Ortho.motion s.ortho (EuclideanSpace.single a 1) =
      U (EuclideanSpace.single a 1) := by
    have e : YM.Ortho.move s.ortho (YM.basis a) = sign a • YM.basis (σ a) := by
      simpa only [sk] using YM.Maxwell.Free.heads s a
    exact e.trans (hu a).symm
  let basis := (EuclideanSpace.basisFun YM.Axis ℝ).toBasis
  have cb (a : YM.Axis) : YM.Ortho.motion s.ortho (basis a) = U (basis a) := by
    simpa [basis] using column a
  apply DFunLike.ext
  intro x
  calc
    _ = YM.Ortho.motion s.ortho (∑ a, basis.repr x a • basis a) :=
      congrArg _ (basis.sum_repr x).symm
    _ = U (∑ a, basis.repr x a • basis a) := by simp only [map_sum, map_smul, cb]
    _ = U x := congrArg U (basis.sum_repr x)

theorem signedAxes (hg : g.core.Simple) (u : Fin 4 → ℂ)
    (σ : Equiv.Perm YangMills.Axis) (sign : YangMills.Axis → ℝ)
    (U : YangMills.Spacetime ≃ₗᵢ[ℝ] YangMills.Spacetime)
    (hs : ∀ a, sign a = 1 ∨ sign a = -1)
    (hu : ∀ a, U (EuclideanSpace.single a 1) = sign a • EuclideanSpace.single (σ a) 1)
    (i j : YangMills.Axis) :
    RelatedByAxes (YangMills.maxwellReference g) σ sign U (filed hg u i j).val
      (((sign i * sign j : ℝ) : ℂ) • (filed hg u (σ i) (σ j)).val) := by
  obtain ⟨s, perm, tiltValue, motion⟩ := signedCoordinates σ sign U hs hu
  subst σ
  subst sign
  subst U
  let q : Sec g.core 4 := ((YM.Maxwell.Free.tilt s i * YM.Maxwell.Free.tilt s j : ℝ) : ℂ) • filed hg u (s.perm i) (s.perm j)
  exact (IssuedMaxwell.SignedAxes.original s (filed hg u i j) q).mpr (fieldTurn hg u s i j).symm

end PhysicalMatching.H7StandaloneWardColumnLaws
end

