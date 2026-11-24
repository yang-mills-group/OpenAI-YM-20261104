import YM.Integration.WilsonPositionProgramCopyTop

/-! Genuine lifted positions can be used in the finite position reader whenever
their sites agree. All relative plaquette paths stay in the field definition. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramPeriodicLeaf
open Finset Lattice Wilson RG XSpace RegulatorIR.FVAAlt2 PhysicalNext.Repeat.Legato
open WilsonPositionProgramCopyTop
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (p : XSpace.Period)
    {I : Type} [Fintype I] [LinearOrder I] (d : I → ℕ) (a : ∀ i, (R.family.labels.level (d i)).Index)
    (z w : I → Cover) (sites : ∀ j, wrap p.side (z j) = wrap p.side (w j))

include sites
theorem field : planted R p d z a = planted R p d w a := by
  funext U
  apply Complex.ofReal_injective
  have hz := congrFun (Boot.combined R (univ : Finset I) d a z p.side) U
  have hw := congrFun (Boot.combined R (univ : Finset I) d a w p.side) U
  simp only [Function.comp_apply, Finset.prod_apply] at hz hw
  exact hz.trans ((Finset.prod_congr rfl (fun j _ => by rw [sites j])).trans hw.symm)

theorem original (T : p.Tree) : normalized R p d z a T = normalized R p d w a T := by
  rw [normalized,field R p d a z w sites]
  rfl
end YM.Integration.WilsonPositionProgramPeriodicLeaf
