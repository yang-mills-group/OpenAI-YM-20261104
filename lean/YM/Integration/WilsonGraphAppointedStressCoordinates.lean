import YM.Integration.WilsonGraphStressColumnIdentification
import YM.Integration.WilsonGraphUnorderedMaxwellTrace
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneAppointedPublicWardRows

/-! The signed grade-four tensor on the four public Maxwell columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress.PublicPanels
open Maxwell Labels Climb Table Work.A01 Next.UVStress XSpace.Normalize
open Uncentered (fields)
open _root_.PhysicalMatching.H7StandaloneAppointedPublicWardRows (columns square unitLabel diagonalEnergy)
open scoped BigOperators Classical
variable {g : YangMills.GaugeGroup} (F : Frames g.core) (hg : g.core.Simple)

theorem squaresValue :
    (∑ k : Fin 6, square hg k).val = ∑ k : Fin 6, label g.core k k := by
  exact map_sum ((YangMills.maxwellReference g).sector 4).subtype (square hg) Finset.univ

def appointedSources (i j : Axis) :=
  ![if i = j then (freeTable F).unit 4 else 0, if i = j then near F i else 0,
    if i = j then (1/2 : ℂ) • total F else 0,
    -panel F i j + (if i = j then (1/4 : ℂ) • total F else 0)]

theorem addressColumns (i j : Axis) (k : Fin 4) :
    Free.address F 4 (appointedSources F i j k) = (columns hg i j k).val := by
  have tr : Free.address F 4 (total F) = (2 : ℂ) • ∑ q : Fin 6, label g.core q q :=
    (totalAddress F).trans (publicTrace F)
  have stress (a b : Axis) : ((YangMills.maxwellReference g).stress a b).val =
      -Free.polStress g.core a b := rfl
  by_cases e : i = j
  · subst j
    fin_cases k
    · change Free.address F 4 (if i = i then (freeTable F).unit 4 else 0) =
          (if i = i then unitLabel hg else 0).val
      simp only
      exact (unitAddress F).trans (by rfl)
    · simpa [appointedSources, columns, near, diagonalEnergy] using panelAddress F i i
    · norm_num [appointedSources, columns, map_smul, tr, smul_smul, squaresValue, square]
      rfl
    · simp [appointedSources, columns, stress, panelAddress, totalAddress, Free.polStress, Free.kr_eq] ; module
  · fin_cases k <;> simp [appointedSources, columns, e, stress, panelAddress, Free.polStress, Free.kr_eq]
    all_goals rfl

theorem normalizedAddress (d a b c : ℂ) (i j : Axis) :
    Free.address F 4 (fields F d a b c i j) =
      ∑ k : Fin 4, (![d, a - 2*b - c, 2*b + c/2, -c] : Fin 4 → ℂ) k • (columns hg i j k).val := by
  let u : Fin 4 → ℂ := ![d, a - 2*b - c, 2*b + c/2, -c]
  have h : fields F d a b c i j = ∑ k : Fin 4, u k • appointedSources F i j k := by
    rw [Fin.sum_univ_four]
    simpa [u, appointedSources, add_assoc] using Uncentered.normalizedColumns F d a b c i j
  rw [h, map_sum]
  exact Finset.sum_congr rfl (fun k _ => by
    simp only [map_smul, addressColumns F hg, u]
    rfl)

theorem signedTensorCoordinates (S : (freeTable F).RealSpin) (J : (freeTable F).Stress)
    (h : RawTensor S J) :
    ∃ u : Fin 4 → ℂ, ∀ i j, Free.address F 4 (J i j) =
      ∑ k : Fin 4, u k • (columns hg i j k).val := by
  obtain ⟨d, a, b, c, hj⟩ := Uncentered.coordinates F S hg J h
  refine ⟨![d, a - 2*b - c, 2*b + c/2, -c], ?_⟩
  intro i j
  rw [hj]
  exact normalizedAddress F hg d a b c i j

end YM.UVNext.FreeStress.PublicPanels

