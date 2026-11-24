import YM.Integration.WilsonPositionProgramCommonBare
import YM.FVAAlt2.Rocket.Reading

/-! The true Wilson input word on the auxiliary copy of the finite chronological program. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramCopyTop
open Lattice Wilson RG XSpace RegulatorIR.FVAAlt2 PertExtension PertExtension.Orb
open PhysicalNext.Repeat.Legato Precision
open scoped BigOperators Classical PowerSeries
variable {G : Gauge} (C : Run G) (p : XSpace.Period)
    {I : Type} [Fintype I] [LinearOrder I] (d : I → ℕ) (z : I → Cover)
    (a : ∀ i,(C.family.labels.level (d i)).Index)

def planted : Config G p.side → ℝ := (Sound.Figure.prop C (fun _ : Unit => z) d a ()).Vt p.side

theorem allowed : PreTest (planted C p d z a) :=
  YM.FVAAlt2.Home.Profiles.frameKeys (Lodge.basisR C) d a (wrap p.side ∘ z) ⟨p.large,p.even⟩

def normalized (T : p.Tree) := XSpace.Bare.normalized T G (XSpace.Taylor.expandTaylor (T.basis G)
  (Complex.ofRealCLM ∘ (planted C p d z a ∘ T.links)))

/-- Every field order of the native finite position coefficient at the actual top word,
including the field-grade shift, agrees with its complete normalized inversion on this copy. -/
theorem original (D : ChartRatio G) (law : LocalRatio D) (T : p.Tree) (q : ℕ) :
    PowerSeries.coeff (q+Kick.depthF Finset.univ d a) (normalized C p d z a T) =
      ((YM.FVAAlt2.Fixed.treeMom D (planted C p d z a) (Kick.depthF Finset.univ d a) q : ℝ) : ℂ) := by
  have form := allowed C p d z a
  have allowedOne : PreTest ((1:ℝ) • planted C p d z a) := by simpa using form
  have charts := YM.FVAAlt2.Home.Profiles.diag_sm D law (planted C p d z a) 1
    (even_iff_two_dvd.mpr p.even) form allowedOne
  have h : diag (restrictedO (planted C p d z a)) = diagonalWith D (restrictedO (planted C p d z a)) := by
    simpa only [one_smul,diag] using charts
  rw [normalized,FVA2.XPos.genuine_X T form,PowerSeries.coeff_map,PowerSeries.coeff_mk,h]
  rfl

/-- The same complete coefficient on the deployed auxiliary epoch, with each input's measured field lift. -/
theorem calibrated (N per : ℕ) (v : ∀ j,C.family.label (d j)) (run : XSpace.Run) (i : ℕ)
    (T : (run.step i).p.Tree) (D : ChartRatio G) (law : LocalRatio D) (q : ℕ) :
    ∑ b,WilsonCoherentTerminalFrame.weight C N per d v b *
      PowerSeries.coeff (q+Kick.depthF Finset.univ d b) (normalized C (run.step i).p d z b T) =
    ∑ b,WilsonCoherentTerminalFrame.weight C N per d v b *
      ((YM.FVAAlt2.Fixed.treeMom D (planted C (run.step i).p d z b) (Kick.depthF Finset.univ d b) q : ℝ) : ℂ) := by
  simp_rw [original C _ d z _ D law T q]

end YM.Integration.WilsonPositionProgramCopyTop
end
