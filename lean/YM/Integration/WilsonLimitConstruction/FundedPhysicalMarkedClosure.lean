import YM.Integration.WilsonLimitConstruction.FundedPhysicalConnectedReference
import YM.Integration.WilsonLimitConstruction.FundedMarkedFieldSplit

/-! Compare the genuine connected finite measured density directly with the
actual independently prescribed cover. This construction needs the physical
marked push but starts before a finite analytic packet model is chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedPhysicalMarkedClosure
open Function Lattice Wilson RG RG.Supply Precision Marker Overlay RG3.Forms RG3.Held RG3.Script.Picnic
open PhysicalNext.Repeat.Legato LocalComparison FullQLocal OPE.Therm Next.Rank.Exponential
open scoped BigOperators Classical

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {Γ : Census V}
    {C : Family G} {D : V → ComparisonDensity.Address.Orbit} {N p m : ℕ}
    {o : V→Site (C.side (m+1) p)} (c : V→Site (C.side m p))
    {Q : PhysicalCarrier C N p (m+1)} (input : Taste (TestSpace D) o Q.rep Γ)

structure Measured where
  carrier : PhysicalCarrier C N p m
  output : Taste (TestSpace D) c carrier.rep Γ
  roots v : (C.path.levels.clock.op m p).ratio.parent (o v)=c v
  vacuum : (C.path.levels.clock.op m p).push (C.path.β N p (m+1)) Q.rep.eval=carrier.rep.eval
  density (x) : actualPush C N p m ((input.leaf x).density)=(output.leaf x).density

def from_output (O : ProducedOutput D Q o c input) : Measured c input :=
  ⟨O.carrier,O.output,O.roots,O.vacuum,O.density⟩

variable {c input} (H : Measured (Q:=Q) (D:=D) c input)

theorem actual (hC : C.Makes) (hm : m<N) (fine : Q.rep.eval=(C.path.rep N p (m+1)).eval) :
    H.carrier.rep.eval=(C.path.rep N p m).eval := by
  rw [←H.vacuum,fine]
  exact (hC.wilson.steps N p m hm).1.symm

theorem on_run (R : Run G) {N p m : ℕ} {Q : PhysicalCarrier R.family N p (m+1)}
    {c : V→Site (R.family.side m p)} {o : V→Site (R.family.side (m+1) p)}
    {T : Taste (TestSpace D) o Q.rep Γ} (A : Measured c T) (hm : m<N)
    (fine : Q.rep.eval=(R.family.path.rep N p (m+1)).eval) {δ k : ℝ}
    (valid : A.carrier.rep.activities.Valid A.carrier.rep.p δ k)
    {w : V→ℝ} {u a d b t : ℝ} (paid : A.output.Snacks w u a d b t) :
    FundedPhysicalConnectedReference.Actual A.output :=
  FundedPhysicalConnectedReference.from_purchase A.output valid
    (fun U => by
      rw [actual A R.makes hm fine]
      exact (ActualCoveredNormalization.same_run_reference R N p m hm.le).1 U) paid

variable (F : FundedPhysicalConnectedReference.Actual H.output) (M : MarkedPackets D G (C.side m p) Γ)
local notation "g₀" => Pert.Asymptotics.regulatorRun C N p (m+1)

def difference (x : TestSpace D) (U : Config G (C.side m p)) : Poly Γ :=
  FundedPhysicalConnectedReference.source H.output F x U-M.read x (g₀) U

theorem quiet (x : TestSpace D) (U : Config G (C.side m p)) :
    (difference H F M x U).part Γ.quiet=0 := by
  rw [difference,Next.Rank.Exponential.part_sub,
    (FundedPhysicalConnectedReference.expansion H.output F x U).1,M.quiet_read,sub_self]

/-- The two signed source invoices contain the original compulsory partition;
the ordinary signed correction is represented only once. -/
abbrev Invoice := FundedMarkedFieldSplit.Invoice H.output (vacuumRemainder H.output) (difference H F M)

variable (S : Invoice H F M)

def produced : ProducedOutput D Q o c input := by
  let V := FundedMarkedFieldSplit.realize S (quiet H F M)
  refine ⟨H.carrier,M,H.output,V.residual,V.formal,H.roots,H.vacuum,H.density,?_,?_,?_⟩
  · intro x U
    rw [V.residual_density,←mul_assoc,
      ←Next.Rank.Exponential.pass_add _ _ (M.quiet_read x _ U) (quiet H F M x U)]
    have h : M.read x (g₀) U+difference H F M x U=FundedPhysicalConnectedReference.source H.output F x U := by
      unfold difference
      abel
    rw [h]
    exact FundedPhysicalConnectedReference.full H.output F x U
  · intro x U
    rw [V.formal_density,FundedPhysicalConnectedReference.formal H.output F,mul_smul_comm,
      ←Next.Rank.Exponential.pass_add _ _ (by rw [Poly.part_neg,quiet,neg_zero])
        (FundedPhysicalConnectedReference.expansion H.output F x U).1]
    have h : -difference H F M x U+FundedPhysicalConnectedReference.source H.output F x U=M.read x (g₀) U := by
      unfold difference
      abel
    rw [h]
    exact Complex.coe_smul _ _
  · intro x U
    rw [V.formal_log,V.residual_log,vacuumRemainder_log]
    abel

theorem carrier : (produced H F M S).carrier=H.carrier := rfl
theorem model : (produced H F M S).model=M := rfl

theorem relative (hC : C.Makes) (hm : m<N) (fine : Q.rep.eval=(C.path.rep N p (m+1)).eval)
    (x : TestSpace D) (U : Config G (C.side m p)) :
    (produced H F M S).residualError x U=Poly.pass (difference H F M x U)-1 := by
  let V := FundedMarkedFieldSplit.realize S (quiet H F M)
  change ((C.path.rep N p m).eval U)⁻¹ • (V.residual.leaf x).density U-1=_
  rw [V.residual_density,vacuumRemainder_density H.output x U (F.gas U),
    mul_smul_comm,mul_one,←actual H hC hm fine]
  rw [Complex.coe_smul,smul_smul,inv_mul_cancel₀ (F.positive U).ne',one_smul]

end YM.Integration.WilsonLimitConstruction.FundedPhysicalMarkedClosure
end
