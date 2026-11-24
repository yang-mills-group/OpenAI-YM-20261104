import YM.XSpace.Panorama

noncomputable section
namespace YM.XSpace.Normalize
open Function Filter Maxwell Maxwell.Free
open scoped Topology Classical

theorem guideOfEveryReader {ι : Type*} {G : Gauge} {d : ℕ} (f : Filter ι)
    (changes : ι → Change G d)
    (tested : ∀ (v : Sec G d) (out : Sec G d →ₗ[ℂ] ℂ),
      Tendsto (fun s => out ((changes s).val v)) f (𝓝 0)) :
    Tendsto (fun s => guide G d (changes s)) f (𝓝 0) := by
  let b := Module.finBasis ℂ (Sec G d)
  let I := Fin (Module.finrank ℂ (Sec G d))
  let readings : Change G d →ₗ[ℝ] (I × I → ℂ) := {
    toFun := fun X ij => b.coord ij.1 (X.val (b ij.2))
    map_add' := by
      intro X Y
      funext ij
      exact (b.coord ij.1).map_add _ _
    map_smul' := by
      intro a X
      funext ij
      exact ((b.coord ij.1).restrictScalars ℝ).map_smul a (X.val (b ij.2)) }
  have faithful : Injective readings := by
    intro X Y same
    apply Subtype.ext
    apply b.ext
    intro j
    apply b.repr.injective
    ext i
    exact congrFun same (i,j)
  obtain ⟨L, inverse⟩ := LinearMap.exists_leftInverse_of_injective readings (LinearMap.ker_eq_bot.mpr faithful)
  have undo (X : Change G d) : L (readings X) = X := by
    first
    | exact inverse X
    | exact congrArg (fun h : Change G d →ₗ[ℝ] Change G d => h X) inverse
  have coordinates : Tendsto (fun s => readings (changes s)) f (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro ij
    exact tested (b ij.2) (b.coord ij.1)
  let response := (guide G d).toLinearMap.comp L
  have result := (LinearMap.toContinuousLinearMap response).continuous.continuousAt.tendsto.comp coordinates
  change Tendsto (fun s => response (readings (changes s))) f (𝓝 (response 0)) at result
  have hresponse (s : ι) : response (readings (changes s)) = (guide G d) (changes s) := by
    change (guide G d) (L (readings (changes s))) = (guide G d) (changes s)
    rw [undo]
  simpa only [hresponse, map_zero] using result

end YM.XSpace.Normalize
