import YM.Integration.WilsonLimitConstruction.FundedCoverFlatStep
import YM.Integration.QLocalNormalizedQBirth

/-! Preserve the actual signed birth function and its external radii across
one canonical physical handoff. The successor reads the same whole packet
on every test and configuration, including untouched compulsory partners. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalReceivedWilsonState

open Lattice Wilson RG Marker Precision LocalComparison LocalComparison.Global
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 FullQLocal.PreRun.SuccessiveRequests WilsonLimitConstruction
open RG3.Script.Picnic MergeProof.Accent
open scoped Classical

variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {J:Request V}
    {C:Family G} {d:LocalFormal.Datum C Γ} {A:NumericSchedule C J}
    {F:AnalyticInput J A d} {η:ℝ}

structure State (I:FullPreparedInputAt F η) (j:ℕ)
    (birth:TestSpace J.tests → Config G (C.side j d.period)→Poly Γ) : Prop where
  before : d.level+1≤j
  radii v : F.inputRadii v≤F.kernelCosts v
  current t : (I.input.leaf t).density=gust C.path d.cutoff d.period j (birth t) (d.level+1) before

theorem start (I:FullPreparedInputAt F η) (unit:∀v,F.inputRadii v≤F.kernelCosts v) :
    State I (d.level+1) (fun t=>(I.input.leaf t).density) :=
  ⟨le_rfl,unit,fun t=>(gust_base C.path d.cutoff d.period (d.level+1) ((I.input.leaf t).density)).symm⟩

variable {I:FullPreparedInputAt F η} {j:ℕ} {birth:TestSpace J.tests → Config G (C.side j d.period)→Poly Γ}

theorem output (L:State I j birth) (M:FundedRenderedBank.Catalogue J d)
    (H:FundedRenderedBank.Bank I M) (t:TestSpace J.tests) :
    (H.output.output.leaf t).density=gust C.path d.cutoff d.period j (birth t) d.level
      ((Nat.le_succ _).trans L.before) := by
  exact (H.output.density t).symm.trans ((congrArg (actualPush C d.cutoff d.period d.level)
    (L.current t)).trans (gust_step C.path d.cutoff d.period j (birth t) L.before).symm)

theorem admitted (L:State I j birth) (v:V) : F.outputRadii v≤F.kernelCosts v := by
  calc
    _≤F.outputRadii v*A.radiusLoss d.level:=le_mul_of_one_le_right (F.output_radius_positive v).le
      (A.radius_loss_ge_one d.level)
    _≤_ := (F.radius_admission v).trans (L.radii v)

theorem weight (L:State I j birth) (v:V) : F.outputRadii v/F.kernelCosts v≤1 :=
  (div_le_one (F.kernel_positive _)).mpr (admitted L v)

private theorem read_eq {X:Type} {N p a b:ℕ} {P:PhysicalCarrier C N p a} {P':PhysicalCarrier C N p b}
    {o:V→Site (C.side a p)} {o':V→Site (C.side b p)}
    {T:Taste X o P.rep Γ} {T':Taste X o' P'.rep Γ}
    (level:a=b) (carrier:HEq P P') (roots:HEq o o') (marked:HEq T T') (x:X) :
    HEq (T.leaf x).density (T'.leaf x).density := by
  subst b
  have hP:P=P':=eq_of_heq carrier
  subst P'
  have ho:o=o':=eq_of_heq roots
  subst o'
  exact heq_of_eq (congrArg (fun T:Taste X o P.rep Γ=>(T.leaf x).density) (eq_of_heq marked))

omit [Fintype V] in
private theorem same_gust {N p:ℕ} {a b:ℕ} {B:Config G (C.side j p)→Poly Γ}
    (h:a=b) (ha:a≤j) (hb:b≤j) :
    HEq (gust C.path N p j B a ha) (gust C.path N p j B b hb) := by
  subst b
  rfl

variable (R:Run G) {d:LocalFormal.Datum R.family Γ} {A:NumericSchedule R.family J}
    {K:NumericPrices A} {caps:Handoff.OutputCapacities} {F:AnalyticInput J A d} {η:ℝ}
    {I:FullPreparedInputAt F η} {M:FundedPhysicalCatalogue.Purchase caps K F}
    {S:FundedRenderedBank.Chosen K I M.toCatalogue} {P:FundedRenderedBank.Canonical S}
    {m r q:ℕ} {hm:d.level=m+1} {A':NumericSchedule R.family (nextRequest J caps r)}
    {W:Bulk.Colors Γ G (R.family.side (m+1) d.period)} {x:Exterior.fieldDir G (R.family.side m d.period) 1}
    {Q:FundedCoverStepPrice.Receipt R M S P r hm A' W x q} {j:ℕ}
    {birth:TestSpace J.tests → Config G (R.family.side j d.period)→Poly Γ}

/-- The same full signed source and the same unit-weight reserve hold on
the actually selected successor. This rule can be applied at every depth. -/
theorem issued (L:State I j birth) (next:FundedCoverFlatStep.Accepted R Q) :
    State next.input j birth := by
  have old:d.level≤j:=(Nat.le_succ _).trans L.before
  have bound:m+1≤j:=hm ▸ old
  refine ⟨bound,fun v=>?_,fun t=>?_⟩
  · rw [Q.shared.radii,Q.shared.costs]
    exact admitted L v
  · have moved:=read_eq (C:=R.family) (Γ:=Γ) hm.symm next.carrier Q.shared.roots next.marked t
    have prior:=output L M.toCatalogue P.bank t
    exact eq_of_heq (moved.trans ((heq_of_eq prior).trans (same_gust hm old bound)))

end YM.Integration.QLocalReceivedWilsonState
