import YM.Integration.QLocalThermalMeasuredPackets

/-! The regular and compulsory addresses of the elected measured packet
presentation satisfy the native all-field activity laws. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalThermalPacketActivity

open Finset Lattice Wilson RG Marker Overlay Extra.Histories Next.Foundations Planned.GuardedAtom
open RG3.Script.Picnic LocalComparison FullQLocal Comparison.Density.RenderM
open WilsonLimitConstruction WilsonLimitConstruction.FundedMarkedSoftRows WilsonLimitConstruction.FundedMarkedFieldSplit
open scoped Classical BigOperators

variable {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] {Γ:Census V} {D:V→ ComparisonDensity.Address.Orbit}
    {n:Side} {Q:Rep G n} {p:BudgetPoint} {a:V→Support n} {o:V→Site n}
    {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n} {w:V→ℝ}
    {g width budget:ℝ} {off cov:ℕ} (P:MarkedPackets D G n Γ)
    (H:P.Paid p a region w g width budget off cov)

set_option backward.isDefEq.respectTransparency false in
include H in
theorem rows (fill:Γ.Mode) (initial:fill.val.Nonempty) (point:∀v,o v∈a v) :
    let L:=QLocalThermalPacketRebooking.regular P fill g
    (∀i,(L.mode i).val.Nonempty) ∧ (∀i v,v∈(L.mode i).val→ o v∈L.site i) ∧
      ∀x i,Q.p.Regular (L.site i) (L.value x i) := by
  constructor
  · intro i
    cases h:P.packet i with
    | none=>simpa [QLocalThermalPacketRebooking.regular,h] using initial
    | some T=>
      have yes:(P.mode i).val.Nonempty:=Finset.nonempty_iff_ne_empty.mpr fun e=>P.marked i T h (Subtype.ext e)
      simpa [QLocalThermalPacketRebooking.regular,h] using yes
  constructor
  · intro i v hv
    cases h:P.packet i with
    | none=>simp [QLocalThermalPacketRebooking.regular,h]
    | some T=>
      have use:v∈(P.mode i).val:=by simpa [QLocalThermalPacketRebooking.regular,h] using hv
      simpa [QLocalThermalPacketRebooking.regular,h] using H.addresses i T h v use (point v)
  · intro x i
    cases h:P.packet i with
    | none=>
      simp only [QLocalThermalPacketRebooking.regular,MarkedPackets.term,h]
      convert (regular0 Q.p (univ:Support n) (0:Site n)).1 using 1 <;> ext U <;> rfl
    | some T=>
      simpa [QLocalThermalPacketRebooking.regular,MarkedPackets.term,h,Pi.smul_def,smul_eq_mul] using
        regular_smul ((g:ℂ)^P.power i) (QLocalThermalJoinedLaw.smooth P H i T h x Q.p)

set_option backward.isDefEq.respectTransparency false in
include H in
theorem realized (point:∀v,o v∈a v) (F E:Taste (TestSpace D) o Q Γ)
    (S:Invoice F E (fun x U=>P.read x g U))
    (chosen:S.soft=QLocalThermalPacketRebooking.regular P (F.menu.rays 0) g) (x:TestSpace D) :
    let pair:=realize S (fun x U=>P.quiet_read x g U)
    (pair.formal.leaf x).Active ∧ (pair.residual.leaf x).Active := by
  let fill:=F.menu.rays 0
  have data:=rows (Q:=Q) P H fill ((S.formal_active x).articles.proper 0) point
  have life (i): (S.soft.mode i).val.Nonempty:=by rw [chosen];exact data.1 i
  have pins (i v) (h:v∈(S.soft.mode i).val):o v∈S.soft.site i:=by
    rw [chosen] at h ⊢
    exact data.2.1 i v h
  have smooth (i):Q.p.Regular (S.soft.site i) (S.soft.value x i):=by rw [chosen];exact data.2.2 x i
  constructor
  · apply FundedMarkedSoftRows.active (negative S.soft) (replace F S.formalForced) x (S.formal_active x) life
    · simpa [negative,replace,F.root] using pins
    · intro i
      have leg:=regular_smul (-1:ℂ) (smooth i)
      rw [neg_one_smul] at leg
      change Q.p.Regular (S.soft.site i) (fun U=> -S.soft.value x i U)
      convert leg using 1
      ext U
      rfl
  · apply FundedMarkedSoftRows.active S.soft (replace E S.residualForced) x (S.residual_active x) life
    · simpa [replace,E.root] using pins
    · exact smooth

end YM.Integration.QLocalThermalPacketActivity
