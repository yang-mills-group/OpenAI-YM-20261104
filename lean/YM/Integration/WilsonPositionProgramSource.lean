import YM.Integration.WilsonCoherentTerminalFrame
import YM.FVAAlt2.Sound.Figure

/-! The cutoff field used by the position program, with the original inverse field calibration. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramSource
open Lattice Wilson RG RGComparison.Core16.Spool PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2
open scoped Classical BigOperators
variable {G : Gauge} (C : Run G) {I : Type} [Fintype I] [LinearOrder I]
variable (d : I → ℕ) (z : I → Lattice.Cover) (u : ∀ i,(C.family.labels.level (d i)).Index)

/-- The entire basis roster, including every spectator, is the program's single microscopic mark. -/
theorem basis (f : Side) (U : Config G f) :
    ((Boot.scout C Finset.univ d u z).Vt f U : ℂ) =
      tally (fun i => WilsonCoherentTerminalFrame.lamp C (d i) (u i)) (fun i => wrap f (z i)) U := by
  calc
    _ = ∏ j,(C.family.localSection (d j)).places (Pi.single (u j) 1) (wrap f (z j)) U := by
      change (Kick.topMark (Lodge.basisR C) Finset.univ d u f z U : ℂ) = _
      have read := congrFun (Boot.combined C Finset.univ d u z f) U
      simp only [Finset.prod_apply,Function.comp_apply] at read
      convert read using 1
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      rfl

/-- This finite sum uses the actual inverse terminal matrix and engineering normalization. -/
theorem source (N per : ℕ) (v : ∀ j,C.family.label (d j)) (U : Config G (C.family.side N per)) :
    ∏ j,C.family.O N per (v j) (wrap _ (z j)) U =
      ∑ a,WilsonCoherentTerminalFrame.weight C N per d v a *
        ((Sound.Figure.prop C (fun _ : Unit => z) d a ()).Vt (C.family.side N per) U : ℂ) := by
  rw [WilsonCoherentTerminalFrame.joint C N per d v]
  apply Finset.sum_congr
  · ext
    simp
  · intro a _
    rw [← basis C d z a]
    rfl

/-- The true Wilson expectation on every tuple of sites, with its original vacuum divisor. -/
theorem measured {n : ℕ} (caps : Fin n → ℕ) (N per : ℕ) (x : Fin n → Site (C.family.side N per))
    (v : ∀ j,C.family.label (caps j)) :
    C.family.ensemble (N := N) (p := per) caps x v =
      ∑ a,WilsonCoherentTerminalFrame.weight C N per caps v a * C.family.omega N per
        (fun U => ((Sound.Figure.prop C (fun _ : Unit => lift ∘ x) caps a ()).Vt (C.family.side N per) U : ℂ)) := by
  have atSites (U : Config G (C.family.side N per)) := source C caps (lift ∘ x) N per v U
  simp only [Function.comp_apply,wrap_lift] at atSites
  change C.family.omega N per (fun U => ∏ j,C.family.O N per (v j) (x j) U) = _
  unfold Family.omega Wilson.moment
  simp_rw [atSites]
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_const_mul]
  · intro a _
    exact Wilson.continuous_integrable _ (continuous_const.mul (Complex.continuous_ofReal.comp
      ((Sound.Figure.prop C (fun _ : Unit => lift ∘ x) caps a ()).payment _)))

end YM.Integration.WilsonPositionProgramSource
end
