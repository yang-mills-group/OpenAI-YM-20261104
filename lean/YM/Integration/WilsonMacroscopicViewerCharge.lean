import YM.Integration.WilsonMacroscopicLoggedRow

/-! A fixed macroscopic exterior has a finite charge for any inserted field of
one given grade, uniform over all viewers on the same original final hierarchy. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicViewerCharge
open Function Set Filter MeasureTheory Table Extraction OPE OPE.Orbits OPE.Orbits.Reader
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
    (F : Spec.Final C f S) {J : Type} [Fintype J] {e : J → ℕ}

private def money (m : ℕ) (val : Fin (Module.finrank ℂ (S.Field m)) → ℝ) : ℝ :=
  ∑ j, ‖((Module.finBasis ℂ (S.Field m)).coord j).toContinuousLinearMap‖ * val j

private theorem quote (m : ℕ) (o : E4) (y : J → E4) (w : Labels S e)
    (apart : Injective (beside (sole o) y)) (val : Fin (Module.finrank ℂ (S.Field m)) → ℝ)
    (bound : ∀ j, ‖viewing F (beside (sole o) y) (beside
      (names (d:=fun _:Unit => m) (sole (Module.finBasis ℂ (S.Field m) j))) (names w))‖ ≤ val j)
    (q:Viewers F) (z:S.Field m) : ‖upon (spectator F q) m o y w z‖ ≤ money m val * ‖z‖ := by
  let B := Module.finBasis ℂ (S.Field m)
  let W := upon (spectator F q) m o y w
  have pay (j) : ‖W (B j)‖ ≤ val j := by
    let value := viewing F (beside (sole o) y) (beside (names (d:=fun _:Unit => m) (sole (B j))) (names w))
    have g : ‖glance F q value‖ ≤ ‖value‖ := (glance_contract F (norm_nonneg value)).1 le_rfl q
    rw [show glance F q value = W (B j) from read_algebra F q apart] at g
    exact g.trans (bound j)
  have expansion : W z = ∑ j, B.repr z j • W (B j) := by
    conv_lhs => rw [← B.sum_repr z]
    rw [map_sum]
    simp only [map_smul]
  change ‖W z‖ ≤ (∑ j, ‖(B.coord j).toContinuousLinearMap‖ * val j) * ‖z‖
  rw [expansion, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul]
  calc
    _ ≤ (‖(B.coord j).toContinuousLinearMap‖ * ‖z‖) * val j :=
      mul_le_mul ((B.coord j).toContinuousLinearMap.le_opNorm z) (pay j)
        (norm_nonneg _) (mul_nonneg ((B.coord j).toContinuousLinearMap.opNorm_nonneg) (norm_nonneg _))
    _ = (‖(B.coord j).toContinuousLinearMap‖ * val j) * ‖z‖ := by ring

theorem original (m : ℕ) (o : E4) (y : J → E4) (w : Labels S e)
    (apart : Injective (beside (sole o) y)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q:Viewers F) (z:S.Field m),
      ‖upon (spectator F q) m o y w z‖ ≤ D * ‖z‖ := by
  let val (j:Fin (Module.finrank ℂ (S.Field m))) := ‖viewing F (beside (sole o) y)
    (beside (names (d:=fun _:Unit => m) (sole (Module.finBasis ℂ (S.Field m) j))) (names w))‖
  exact ⟨money m val,Finset.sum_nonneg (fun _ _ => mul_nonneg (ContinuousLinearMap.opNorm_nonneg _)
    (norm_nonneg _)),quote F m o y w apart val (fun _ => le_rfl)⟩

theorem uniform (paid : Services C f S) (m : ℕ) (w : Labels S e) {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (o:E4) (y:J→E4), ClearOf o y δ → Injective (beside (sole o) y) →
      ∀ (q:Viewers F) (z:S.Field m), ‖upon (spectator F q) m o y w z‖ ≤ D * ‖z‖ := by
  let v (j:Fin (Module.finrank ℂ (S.Field m))) : C.book.Token := quoteTag
    (⟨m,Module.finBasis ℂ (S.Field m) j⟩ : S.Tag)
  choose A price using fun j => OPE.Log.spectators F (names w) paid hδ (v j)
  let D j := max (A j) 0
  refine ⟨money m D, Finset.sum_nonneg (fun j _ => mul_nonneg
    (ContinuousLinearMap.opNorm_nonneg _) (le_max_right _ _)),?_⟩
  intro o y clear apart
  apply quote F m o y w apart D
  intro j
  exact (price j y o clear).trans (le_max_left _ _)

end YM.Integration.WilsonMacroscopicViewerCharge
