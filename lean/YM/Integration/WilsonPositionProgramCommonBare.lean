import YM.Integration.WilsonPositionProgramSource
import YM.FVA2.XPos.Vertices
import YM.FVAAlt2.Home.Vista

/-! The original complete source on a common finite inversion regulator. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramCommonBare
open Lattice Wilson RG XSpace RegulatorIR.FVAAlt2 PertExtension PertExtension.Orb PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G : Gauge} (C : Run G) (N per : ℕ)

def period : XSpace.Period where
  side := C.family.side N per
  even := (show 2 ∣ 4 by decide).trans (C.family.S.side_four N per)
  large := Nat.le_of_dvd (C.family.side N per).property (C.family.S.side_four N per)

variable {I : Type} [Fintype I] [LinearOrder I] (d : I → ℕ) (z : I → Cover)
    (a : ∀ i,(C.family.labels.level (d i)).Index)

def mark : Config G (C.family.side N per) → ℝ :=
  (Sound.Figure.prop C (fun _ : Unit => z) d a ()).Vt (C.family.side N per)

theorem permitted : PreTest (mark C N per d z a) := by
  let n := C.family.side N per
  have allowed : Pert.Orb.Admissible n := ⟨(period C N per).large,(period C N per).even⟩
  exact YM.FVAAlt2.Home.Profiles.frameKeys (Lodge.basisR C) d a (wrap n ∘ z) allowed

def wick (T : (period C N per).Tree) : PowerSeries ℂ :=
  XSpace.Bare.normalized T G (XSpace.Taylor.expandTaylor (T.basis G)
    (Complex.ofRealCLM ∘ (mark C N per d z a ∘ T.links)))

/-- The full conditional program's original bare mark has the common normalized inversion expansion. -/
theorem common (T : (period C N per).Tree) :
    wick C N per d z a T = PowerSeries.map Complex.ofRealHom
      (PowerSeries.mk (diag (restrictedO (mark C N per d z a)))) :=
  FVA2.XPos.genuine_X T (permitted C N per d z a)

/-- The common-regulator calculation holds before the measured field matrix is estimated. -/
theorem calibrated (T U : (period C N per).Tree) (v : ∀ i,C.family.label (d i)) :
    ∑ b,WilsonCoherentTerminalFrame.weight C N per d v b • wick C N per d z b T =
      ∑ b,WilsonCoherentTerminalFrame.weight C N per d v b • wick C N per d z b U := by
  simp_rw [common]

end YM.Integration.WilsonPositionProgramCommonBare
end
