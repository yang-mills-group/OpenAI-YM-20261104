import YM.Integration.WilsonPositionProgramStageInvoice
import YM.Integration.WilsonPositionProgramInfraredCircuit

/-! Unweighted formal kernel prices on the physical patches of the elected run. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramStageRows
open Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Push.PriceCompiler RegulatorIR RegulatorIR.Atlas RegulatorIR.FVAAlt2
open scoped Classical Topology ENNReal
variable {G : Gauge}

private theorem same {K K' : KernelChoices} (h : K=K') (a : ∀ P : RG.Patch, P.Branches K G)
    (b : ∀ P : RG.Patch, P.Branches K' G) (j : ℕ) (L : Side) :
    Lodge.pad (Oracle.books K) a j L = Lodge.pad (Oracle.books K') b j L := by subst K'; rfl

variable (C : Run G)
local notation "A" => C.family.path.levels
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel

theorem actual (paid : WilsonPositionProgramStageInvoice.Requested C.kit)
    (Z : ∀ P : RG.Patch, P.Branches (A).clock.kernel G) (m : ℕ) (P : RG.Patch)
    (size : P.L=C.family.S.block m) (stage : P.J=(A).clock.J (m+1)) (p : ℕ) (hp : p ≤ P.J) :
    (glowF G Y Z p (Lodge.through p) P + glowPage G Y (Lodge.through p) P.J).toReal ≤
      Real.log (RG16.Lambda (A) m) := by
  refine (WilsonPositionProgramStageInvoice.bill Z P p hp).trans ?_
  have hk : (A).clock.kernel=C.metals.p.kernel := C.alloy.B.valid.kernel
  rw [same hk Z C.metals.p.has P.J P.L,stage,size,
    show C.family.S.block m=C.rolls.L ((A).clock.J (m+1)) from block_eq C.alloy.B.valid m]
  exact paid m

end YM.Integration.WilsonPositionProgramStageRows
end
