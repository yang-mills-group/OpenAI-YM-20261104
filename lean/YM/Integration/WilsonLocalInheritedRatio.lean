import YM.Integration.WilsonLocalTerminalWeights

/-! The original incoming field at an interior date, retained exactly
relative to the measured Wilson weight at the same temperature. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalInheritedRatio
open Lattice RG Wilson Tree RG16 PertExtension Push.BetaTransport PhysicalNext.Repeat.Legato
variable {G:Gauge}

def rest (C:Family G) (N per m:ℕ) (V:Config G (C.side m per)) (U:Config G (C.side (m+1) per)) :=
  let β:=C.path.β N per (m+1)
  let Q:=C.path.rep N per (m+1)
  (C.path.levels.clock.op m per).density β U V*(Q.eval U/bare β U)

theorem split (C:Family G) (N per m:ℕ) (V:Config G (C.side m per)) (U:Config G (C.side (m+1) per)) :
    actualConditionalDensity C N per m V U =
      rest C N per m V U*bare (C.path.β N per (m+1)) U/(C.path.rep N per m).eval V := by
  dsimp only [rest,actualConditionalDensity]
  rw [mul_assoc,div_mul_cancel₀ _ (bare_pos _ _).ne']

theorem positive (R:Run G) (N per m:ℕ) (hm:m < N) (V:Config G (R.family.side m per)) :
    ∀U:Config G (R.family.side (m+1) per),0 < rest R.family N per m V U ∧
      0 < actualConditionalDensity R.family N per m V U := by
  intro U
  obtain ⟨hk,hr⟩:=WilsonLocalConditionalResidue.positive R.family R.makes N per m hm V U
  exact ⟨mul_pos hk (div_pos (Multi.AxisShift.chosen_positive R.makes.wilson hm U) (bare_pos _ _)),hr⟩

theorem logarithm (R:Run G) (N per m:ℕ) (hm:m < N) (V:Config G (R.family.side m per))
    (X Y:Config G (R.family.side (m+1) per)) (a b:ℝ) (ha:0 < a) (hb:0 < b) :
    let C:=R.family
    let β:=C.path.β N per (m+1)
    let ρ:=actualConditionalDensity C N per m V
    let K:=rest C N per m V
    Real.log ((a*ρ X)/(b*ρ Y))=Real.log (a/b)+Real.log (K X/K Y)+Real.log (bare β X/bare β Y) := by
  dsimp only
  rw [split,split]
  exact WilsonLocalConditionalFactors.factors ha hb (positive R N per m hm V X).1 (positive R N per m hm V Y).1
    (bare_pos _ _) (bare_pos _ _) (Multi.AxisShift.chosen_positive R.makes.wilson hm.le V)

theorem terminal (R:Run G) (m per:ℕ) (V:Config G (R.family.side m per)) (U:Config G (R.family.side (m+1) per)) :
    rest R.family (m+1) per m V U=(R.family.path.levels.clock.op m per).density (R.family.path.β (m+1) per (m+1)) U V := by
  let n:=m+1
  let β:=R.family.path.β n per n
  have issued : (R.family.path.rep n per n).eval=bare β := (R.makes.wilson.starts n per).2
  change (R.family.path.levels.clock.op m per).density β U V*((R.family.path.rep n per n).eval U/bare β U)=_
  rw [issued,div_self (bare_pos _ _).ne',mul_one]

end YM.Integration.WilsonLocalInheritedRatio
