import YM.Integration.WilsonReportHarvestReplayPhysical
import YM.Integration.WilsonReportHarvestReadmittedWallet
import YM.Integration.WilsonReportingMeasuredAdmission
import YM.Integration.WilsonMixedTaggedSpend

/-! Fixed representatives of the prescribed finite frame on both true reporting
origins. A single choice works for every retained degree and accuracy. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportHarvestReplayPrescribed
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station WilsonLimitConstruction
open WilsonCloseCaptureCalendar
open Next.Rank RG12 RG17 Extraction Spec Climb Table Trace.Pilot Pier.Lair SharpGram SharpGram.Lenses OPE.Orbits
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
universe u
variable {G : Gauge} (R : Run G) (simple : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (fund : FundedOriginalProperties.{u} simple δ W)
    (book : OPE.Package R.family R.w (mutt R.family.path.levels R.Q) R.doors)
    (portfolio : Funding R) (slow : WilsonWindowReportingPace.Slow R.kit)

variable {order:Extraction.Order}{table:Table R.family.book}{F:Final R.family order table} (L:Layout F)

variable {J:ℝ→FamilyBasis (C:=R.family) table} {u:Filter (ℕ×ℕ)}
    (B:Mantle F u) (E:OPE.Services R.family order table)
    (paid:Pier.Lair.Present F J) (pegs:Pegs B L)
    (near:∀ᶠ r in trail,R.family.S.a (L.level r) ≤ r ∧
      r ≤ R.family.S.a (L.level r)*R.family.path.levels.clock.hatBeta (L.level r)^2)

def Selected (L:Layout F)(J:ℝ→FamilyBasis (C:=R.family) table)(s:Fin 3→ℕ)
    (v:(i:Fin 3)→Free R.family (s i))(h:ℕ)(r:ℝ)(w:(i:Fin 3)→R.family.label (s i)):Prop :=
  ∀i,master L (s i) r (w i)=J r (s i) (v i) ∧
    mass R.family (s i) (WilsonReportingUnitOrbit.phase • L.shift (s i) r (w i)) ≤
      (R.family.path.levels.clock.hatBeta (L.level r))^h

def Received (R:Run G)(simple:G.Simple)(portfolio:Funding R)
    {order:Extraction.Order}{table:Table R.family.book}{F:Final R.family order table}(L:Layout F)
    (K d h k p engineering reserve:ℕ)(ε:ℝ)(s:Fin 3→ℕ)(r:ℝ)(w:(v:Fin 3)→R.family.label (s v)):Prop :=
  let C:=R.family
  let m:=WilsonMeasuredWindow.stop C.path.levels simple K r
  let b₀:=crossLevel C.S r-1-1
  let H:=2*(h+1)+2*(K+1)
  ∀b:ℕ,b₀ ≤ b → b ≤ b₀+1 → ∃bm:b ≤ m,∀u≥m,L.level r ≤ u+1 → ∀per:ℕ,
    let N:=u+1
    let S:=fun v:Fin 3=>portfolio.basis (s v) (N,per)
    let Q:=WilsonReportHarvestReplayPhysical.allowance R m N d H
    let x:=fun v:Fin 3=>WilsonReportHarvestReadmittedSource.filed L (s v) r (w v) (S v) m N per
    ∃P:(v:Fin 3)→Sight C (s v) per,
      (∀v,Spine R.doors portfolio.allowance R.makes b per (s v) N (P v) (S v)) ∧
      (∀v,size (x v) ≤ Q ∧ Many.point (S v) (x v) m N=chunk (WilsonReportingUnitOrbit.primary (s v))
        ((C.factory (s v) N per).terminal.symm (atRef L (s v) r (N,per) (w v)))) ∧
      ∀(o:Fin 3→Site (C.side b per))(E:Fin 3→Motion)(q:ManyStem C o b→Body)(roster:Census (Fin 3)),
      (∀v:ManyStem C o b,Cap (s v.val.1+2) (q v) 1) →
      ∀i:ℕ,∀mi:m ≤ i,∀iu:i ≤ u,WilsonReportHarvestUpperRange.eligible C.S m i u →
        WilsonReportHarvestReplayPhysical.Retained R bm mi (Nat.le_succ_of_le iu) s S P x o E q roster d k Q
          (WilsonReportHarvestReplayPhysical.amount R b m i N per p engineering reserve ε)

local notation "C" => R.family

include W fund book slow B E paid pegs near in
theorem original (K d:ℕ)(hk:0<K)(s:Fin 3→ℕ)(degree:∀i,s i ≤ d)(v:(i:Fin 3)→Free R.family (s i)):
    ∃(h:ℕ)(w:(r:ℝ)→(i:Fin 3)→(C).label (s i)),(∀ᶠr in trail,Selected R L J s v h r (w r)) ∧
      ∀ε:ℝ,0<ε → ∃k:ℕ,∀p engineering reserve:ℕ,∀ᶠr in trail,
        Received R simple portfolio L K d h k p engineering reserve ε s r (w r) := by
  obtain ⟨h,tender⟩:=WilsonReportingMeasuredTender.roster B E paid pegs near s v WilsonReportingUnitOrbit.phase
  change ∀ᶠr in trail,∃w,Selected R L J s v h r w at tender
  let w (r:ℝ):(i:Fin 3)→(C).label (s i):=
    if existsW:∃z,Selected R L J s v h r z then existsW.choose else fun _=>0
  have elected:∀ᶠr in trail,Selected R L J s v h r (w r):=by
    filter_upwards [tender] with r purchased
    dsimp only [w]
    rw [dif_pos purchased]
    exact purchased.choose_spec
  refine ⟨h,w,elected,?_⟩
  intro ε ep
  obtain ⟨k,fields⟩:=WilsonReportHarvestReplayPhysical.original R simple W fund book portfolio slow d ep
  refine ⟨k,?_⟩
  intro p engineering reserve
  let H:=2*(h+1)+2*(K+1)
  obtain ⟨start,entries⟩:=eventually_atTop.mp (fields p H engineering reserve (K+3))
  have windows:=(WilsonMixedTaggedMeasuredWindow.original R simple K hk slow.2).2
  have balance:=WilsonReportHarvestReadmittedWallet.original R simple L K hk d h slow pegs.level.growing near
  filter_upwards [elected,(WilsonMixedTaggedSpend.lower R).eventually_ge_atTop start,windows,balance]
    with r names late dates funded
  unfold Received
  intro C' m b₀ h' b lower upper
  have before : b₀ + 1 < m := dates.1
  have bm:b ≤ m:=by omega
  refine ⟨bm,?_⟩
  intro u mu originalN per N S Q x
  have short:((m-b:ℕ):ℝ) ≤ ((K+3:ℕ):ℝ)*(1+Real.log (WilsonMeasuredAdmission.mast (C).path.levels m)):=by
    have order:m-b ≤ m-b₀:=by omega
    exact (Nat.cast_le.mpr order).trans dates.2.2
  obtain ⟨P,spine,price⟩:=entries b (late.trans lower) m bm short u mu per s degree
  have bill (v:Fin 3):size (x v) ≤ Q ∧
      Many.point (S v) (x v) m N=chunk (WilsonReportingUnitOrbit.primary (s v))
        (((C).factory (s v) N per).terminal.symm (atRef L (s v) r (N,per) (w r v))):=
    funded b (s v) N per bm (max_le originalN (Nat.le_succ_of_le mu)) (degree v)
      R.doors portfolio.allowance (P v) (S v) (spine v) (w r v) (names v).2
  exact ⟨P,spine,bill,price x (fun v=>(bill v).1)⟩

end YM.Integration.WilsonReportHarvestReplayPrescribed
