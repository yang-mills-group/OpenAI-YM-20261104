import YM.Integration.WilsonIndependentPublicFreeAppointment

/-! Recover the two common infinite-cover Wick kernels from the genuine periodic hearings. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000
namespace YM.Integration.WilsonIndependentPublicCoverFields
open Lattice RG WilsonCoeffUV FreeResolvent RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle
open Laurent Bloch Exterior Stationary Work.F08 Matrix Metric Precision Next.Free Tree
open RegulatorIR.Budget RegulatorIR.Quadratic Filter
open scoped Classical BigOperators
variable {G:Gauge}{Ω:Type}{M:Ω→ℕ}{n:Page M→Side}

private theorem undo {α β γ μ:Type}(e:α ≃ γ)(f:β ≃ μ)(L:Matrix α β ℝ)(T:Matrix γ μ ℝ)
    (read:T=repackM e f L):L=T.submatrix e f:=by
  subst T
  ext a b
  simp [repackM]

private theorem detect (P Q:Patch)(agree:P=Q)(K:KernelChoices)(U:TreeRow G Q)(V:CoarseMean G Q)
    (X Y:Layer (Geometry.Long G.ColorIndex) (Geometry.Long G.ColorIndex))(hU:Whole U)(hV:Whole V)(hX:Billed X)(hY:Billed Y)
    (aX:Albedo (blockQ G P.L) (blockQ G P.L) X)(aY:Albedo (blockQ G P.L) (linksQ G) Y)
    (read:∀ c:Side,let split:=unitSplit G (avenue P K c) 1
      HEq (U.acts c) (repackM split split (ledgerRow (blockQ G P.L) (blockQ G P.L) X c)) ∧
      HEq (V.acts c) (repackM split (Equiv.refl _) (ledgerRow (blockQ G P.L) (linksQ G) Y c))) :
    X=lading (blockQ G Q.L) (blockQ G Q.L) U ∧ Y=lading (blockQ G Q.L) (linksQ G) V:=by
  subst Q
  obtain ⟨σ,C,pos,charged⟩:=hU
  obtain ⟨τ,D,clear,paid⟩:=hV
  constructor
  · apply solely _ _ hX ((fond _ _ U charged).buys pos.le).1 aX (ladingW _ _ _)
    apply Eventually.of_forall
    intro i
    let c:Side:=⟨i+1,i.succ_pos⟩
    dsimp only
    rw [ledger_lade]
    exact undo _ _ _ _ (eq_of_heq (read c).1)
  · apply solely _ _ hY ((fond _ _ V paid).buys clear.le).1 aY (ladingW _ _ _)
    apply Eventually.of_forall
    intro i
    let c:Side:=⟨i+1,i.succ_pos⟩
    dsimp only
    rw [ledger_lade]
    exact undo _ _ _ _ (eq_of_heq (read c).2)

variable {A:Levels G}{C:Circuit M n}{K:KernelChoices}{s:ℕ}{w:Ω}
theorem original (grant:WilsonIndependentPublicFreeTrain.Matches A C K s w)
    (Y:Program K)(Z:∀ P:Patch,P.Branches K G)(f:Flap M)(hf:f.volW=w):
    let N:=s+M w
    let m:=s+(M w-(f.offset+1))
    let B:=blockQ G (loose A m).L
    C.pulses Y G Z f=lading B B (conditional A N m) ∧ C.sails Y G f=lading B (linksQ G) (feedA A N m) :=by
  intro N m B
  have hU:=(cond_laws A m N).2.1
  have hV:Whole (feedA A N m):=by
    obtain ⟨σ,Cst,pos,_⟩:=(cond_laws A m N).2.1
    obtain ⟨cost,_,bill⟩:=probe_pay G (loose A m) A.clock.kernel.penalty pos.le
    exact hU.prod ⟨σ,cost,pos,bill⟩
  have price:= C.predicted Y f
  have pos:=(C.honored Y f.prev).card.pos.le
  apply detect (C.pactP f) (loose A m) (grant.patches f hf).symm K _ _ _ _ hU hV
    (heatP _ _ _ _ _ _) ((overrides _ _ _ G price.rows pos price.costV).buys pos).1
    (phaseT _ _ _ _ _ _) (placates _ _ _ G) (WilsonIndependentPublicFreeFields.original grant Y Z f hf)

end YM.Integration.WilsonIndependentPublicCoverFields
