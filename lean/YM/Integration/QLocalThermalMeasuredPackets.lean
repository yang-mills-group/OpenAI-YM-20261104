import YM.Integration.QLocalThermalFundedFieldSplit
import YM.Integration.WilsonLimitConstruction.FundedPhysicalMarkedClosure
import YM.Extra.SOURCE_HISTORIES.Unit

/-! Present a chosen marked program on the same carrier as the complete
measured output. The opposite signed compulsory updates give its actual
model and residual and keep their original vacuum K on every field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalThermalMeasuredPackets

open Function Finset Lattice Wilson RG Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal Comparison.Density.RenderM
open Next.Rank.Exponential WilsonLimitConstruction WilsonLimitConstruction.FundedMarkedFieldSplit
open WilsonLimitConstruction.FundedMarkedSoftRows
open scoped Classical BigOperators

variable {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] {Γ:Census V} {C:Family G}
    {D:V→ ComparisonDensity.Address.Orbit} {N t m:ℕ} {o:V→Site (C.side (m+1) t)} {c:V→Site (C.side m t)}
    {Q:PhysicalCarrier C N t (m+1)} {input:Taste (TestSpace D) o Q.rep Γ}
    (H:FundedPhysicalMarkedClosure.Measured c input) (M:MarkedPackets D G (C.side m t) Γ)
local notation "g₀" => Pert.Asymptotics.regulatorRun C N t (m+1)

def produced (gas:∀U,Summable (fun s:Finset ℕ=>‖H.carrier.rep.activities.gasOccurrence H.carrier.rep.p s U‖))
    (S:Invoice H.output (vacuumRemainder H.output) (fun x U=>M.read x (g₀) U)) : ProducedOutput D Q o c input := by
  let V₀:=realize S (fun x U=>M.quiet_read x (g₀) U)
  refine ⟨H.carrier,M,H.output,V₀.formal,V₀.residual,H.roots,H.vacuum,H.density,?_,?_,?_⟩
  · intro x U
    rw [V₀.formal_density,←mul_assoc,←Next.Rank.Exponential.pass_add _ _ (M.quiet_read x (g₀) U)
      (by rw [Poly.part_neg,M.quiet_read,neg_zero]),add_neg_cancel,Next.Rank.Exponential.pass_zero,one_mul]
  · intro x U
    rw [V₀.residual_density,vacuumRemainder_density H.output x U (gas U),mul_smul_comm,mul_one]
    exact IsScalarTower.algebraMap_smul ℂ (H.carrier.rep.eval U) (M.read x (g₀) U).pass
  · intro x U
    rw [V₀.formal_log,V₀.residual_log,vacuumRemainder_log,zero_add]
    abel

omit [Fintype V] in
theorem vacuum_radial {n:Side} {X:Type*} {B:Rep G n} {a:V→Site n} (T:Taste X a B Γ)
    {w:V→ℝ} (pos:∀v,0<w v) (x:X) : ((vacuumRemainder T).menu.terms x).Radial w 0 0 0 1 := by
  refine ⟨pos,fun v=>by change w v*‖(0:ℂ)‖≤0;simp,zero_lt_one,?_,?_⟩
  · refine ⟨fun _=>0,fun i=>⟨le_rfl,fun v _=>(regular0 B.p (T.menu.branch i) (T.menu.origins v)).2⟩,?_⟩
    intro v
    simpa [vacuumRemainder,BudgetPoint.mass] using
      (show SumBudget (fun _:ℕ=>(0:ℝ)) 0 from ⟨fun _=>le_rfl,summable_zero,by simp⟩)
  · refine ⟨fun _=>0,fun i j=>⟨le_rfl,fun _=>by simp [vacuumRemainder]; rfl⟩,?_⟩
    intro v
    simpa [vacuumRemainder,BudgetPoint.mass] using
      (show SumBudget (fun _:ℕ×ℕ=>(0:ℝ)) 0 from ⟨fun _=>le_rfl,summable_zero,by simp⟩)

/-- The native first selection only needs the complete actual outgoing
taste and a paid packet on its addressed carrier. -/
theorem issued (K:Guard.Keeper H.carrier.rep.p H.carrier.rep.activities) {p:BudgetPoint}
    {a:V→Support (C.side m t)} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) (C.side m t)}
    {w:V→ℝ} {width budget:ℝ} {off cov:ℕ} (paid:M.Paid p a region w (g₀) width budget off cov)
    (hg:(g₀)≠0) (point:∀v,c v∈a v) {e k:ℝ} (good:H.carrier.rep.activities.Valid H.carrier.rep.p e k)
    (active:∀x,(H.output.leaf x).Active) (fare:∀x,∃u v b d,(H.output.menu.terms x).Radial w u v b d) :
    ∃O:ProducedOutput D Q o c input, O.carrier=H.carrier ∧ HEq O.output H.output ∧ O.model=M ∧
      ∀x U,(O.formalAligned.leaf x).density U=(H.carrier.rep.eval U:ℂ) • Poly.pass (M.read x (g₀) U) ∧
        (O.residual.leaf x).density U=Poly.pass (-(M.read x (g₀) U))*(H.output.leaf x).density U := by
  obtain ⟨S⟩:=QLocalThermalJoinedInvoice.invoice M K paid hg point H.output (vacuumRemainder H.output) good active
    (fun x=>vacuumRemainder_active H.output x (active x) x) fare
    (fun x=>⟨0,0,0,1,vacuum_radial H.output paid.positive x⟩)
  let gas:= (Activities.gasSeries good).absolute
  let O:=produced H M gas S
  refine ⟨O,rfl,HEq.rfl,rfl,fun x U=>⟨O.formal_full x U,?_⟩⟩
  exact (realize S (fun x U=>M.quiet_read x (g₀) U)).formal_density x U

def appended {n:Side} {X Y:Type} {B:Rep G n} {o:V→Site n} (p:BudgetPoint) (T:Taste X o B Γ)
    (L:Rows X Γ G n) (f:Y→X) {w:V→ℝ} {κ b:ℝ} (sold:ForcedBudget p (pullback f T) w κ b) :
    ForcedBudget p (pullback f (append L T)) w κ b where
  black:=sold.black
  black_nonnegative:=sold.black_nonnegative
  forced:=sold.forced
  total:=sold.total

end YM.Integration.QLocalThermalMeasuredPackets
