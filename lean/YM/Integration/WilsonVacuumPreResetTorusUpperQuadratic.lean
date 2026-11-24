import YM.Integration.WilsonVacuumPreResetTorusFoldedOutput
import YM.WilsonCoeffUV.Kinetic.Base

/-! The independently folded upper action has on each original finite side
exactly the quadratic needed for the relative-to-absolute Gaussian change. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusUpperQuadratic
open Lattice RG Matrix Laurent Bloch Wilson Precision FreeResolvent
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Winding WilsonCoeffUV.Wheel WilsonCoeffUV.Mer
open scoped Classical BigOperators
variable {G:Gauge}

theorem original (R:Run G)(simple:G.Simple)(N j:ℕ)(live:j ≤ N)(n:Side):
    let A:=R.family.path.levels
    let action:=emera (actionW A R.metals.O N j) n
    shellK 2 action ∧ action 0=shine (orbQ (precisionC G n (freeForms A N j))):=by
  intro A action
  refine ⟨(emera_far A simple R.alloy.B.ratio live n).1,?_⟩
  have win:=catchment A R.metals.O simple R.alloy.B.ratio live
  funext r
  cases r with
  | zero=>
    change 0=shine _ 0
    rw [shine_dark (by omega)]
  | succ k=>
    change lagoon (actionW A R.metals.O N j 0 (k+1)) n=shine _ (k+1)
    rw [win.readout]
    by_cases h:k=1
    · subst k
      rw [shine_lit,shine_lit]
      obtain ⟨s,B,hs,_,strip⟩:=forms_tail A.clock.kernel.penalty
        A.clock.kernel.penalty_pos _ (A.clock.adm j)
      exact plain_act G n ((strip A j rfl rfl).1 N) hs.le
    · rw [shine_dark (by omega),shine_dark (by omega),lagoon_none]

end YM.Integration.WilsonVacuumPreResetTorusUpperQuadratic
