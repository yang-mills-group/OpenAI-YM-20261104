import YM.Integration.WilsonGraphMixedOriginalNumeratorNames

/-! Simultaneous translation of the two groups of sites in the original physical numerator. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedNumeratorTranslation

open Function Real Growth Continuation
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Book MS.Land Scale Register O O.Enh O.Score Dframe
open YM.Answer.ContinuumLimit YM.OPE YM.OPE.Orbits
open AppointedMixedFarRow
open scoped Topology BigOperators Classical

variable {G : Gauge} {R : Family G} {f : Extraction.Order} {P : Table R.book}
variable (U : Spec.Final R f P) (J : Physical.FramesH P)
variable {n m : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}

/-- Moving every site by the same displacement preserves the numerator for each viewer. -/
theorem withOrigin (w : Window) (phase : Viewers U) (o : E4) (x : Points n) (y : Points m)
    (u : Inputs G d) (v : Inputs G e)
    (safe : Injective (beside (Physical.atPos w.len 0 x) (Physical.atPos w.Coarse 0 y))) :
    Physical.Y0 U J d e w (phase,o) x y u v =
      Physical.Y0 U J d e w (phase,0) x y u v := by
  let sites := beside (Physical.atPos w.len 0 x) (Physical.atPos w.Coarse 0 y)
  have shifted : beside (Physical.atPos w.len o x) (Physical.atPos w.Coarse o y) =
      fun i => sites i + o := by
    funext i
    rcases i with i | i <;> simp [sites, Physical.atPos, add_comm]
  rw [Physical.Y0_value,Physical.Y0_value,whole_observed,whole_observed]
  change observe (spectator U phase) (beside (Physical.atPos w.len o x) (Physical.atPos w.Coarse o y)) _ =
    observe (spectator U phase) sites _
  rw [shifted]
  exact observe_carry (spectator U phase) (spectate U phase).translations _ safe o

/-- The separated public forest pays the translation condition at the actual two radii. -/
theorem onPlacement (w : Window) (hr : 0 < w.len) (phase : Viewers U) (o : E4)
    (x : Points n) (y : Points m) (u : Inputs G d) (v : Inputs G e)
    (safe : placement w.2 (x,y) ∈ YM.conf (n+m)) :
    Physical.Y0 U J d e w (phase,o) x y u v =
      Physical.Y0 U J d e w (phase,0) x y u v := by
  let points : YM.Points (n+m) := WithLp.toLp 2 fun i => (0:E4) + w.len • placement w.2 (x,y) i
  let rename : Fin n ⊕ Fin m ≃ Fin (n+m) := finSumFinEquiv
  have distinct : points ∈ YM.conf (n+m) := ElectedMeasurement.centerSeparated hr 0 _ safe
  have chart : beside (Physical.atPos w.len 0 x) (Physical.atPos w.Coarse 0 y) = points.ofLp ∘ rename := by
    funext i
    rcases i with i | i
    · change (0:E4) + w.len • x i = 0 + w.len • forest x (squeeze (-w.2) y) (Fin.castAdd m i)
      rw [forest_left]
    · change (0:E4) + (w.len * exp w.2) • y i = 0 + w.len • forest x (squeeze (-w.2) y) (Fin.natAdd n i)
      rw [forest_right]
      simp [squeeze,PiLp.smul_apply,← mul_smul]
  apply withOrigin U J w phase o x y u v
  rw [chart]
  exact distinct.comp rename.injective

end YM.FVA2.GradedFar.AppointedNumeratorTranslation
end

