import YM.Integration.WilsonMatrixTicketLanesTerminalQBudget

/-! Every sufficiently high absolute Taylor order is affordable on the same filed physical first block. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogGradeMarket
open Filter Function Finset Lattice Wilson RG RG12 RG17 Precision Tree Extraction Source Labels Spec
open MS MS.Land MS.Menus MS.Rake MS.Local.Physical PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Spool FVA2 FVA2.CityHistory
open Pert.Asymptotics
open WilsonMatrixTicketLanesTerminalQWords WilsonMatrixTicketLanesReportedPrepaid
open WilsonMatrixTicketLanesTerminalQGrades
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){B:Deck G}(Q:Prescription B){n:ℕ}(l:Fin n→Label B)

theorem purchased (simple:G.Simple)(paid:Paid G R.kit)(K cap q:ℕ)(μ:ℝ):
    ∃ (start : ℕ),∀order≥start, (∀ t : ∀ i, Piece R (l i), power (word R l t) ≤ order) ∧
      ∀ᶠ b:ℕ in atTop,∀(per:ℕ)(k:Fin n→ℕ),(∀i,k i≤K)→∀reader:Fin n→ℂ,
        let D:=R.family.path.levels.clock.op b per
        let g:=regulatorRun R.family (b+1) per (b+1)
        let θ:=μ-R.family.S.scale (b+1)
        ∀(large:Bid.Larger (G:=G) D)(T:Forest D.ratio)(u:Pins G (R.family.side b per))
          (o:Fin n→Site (R.family.side (b+1) per))(tag:D.Choices)(v:(Descent.nil (top:=R.family.side (b+1) per)).Tags),
          (∀i,‖u i‖≤(cap:ℝ)+1)→
          ‖WilsonMatrixTicketLanesTerminalQReturn.measured R Q l θ k reader u o-
            stack R Q l order θ k reader large T u o tag v‖≤g^q*(∏i,‖reader i‖):=by
  obtain ⟨C,cp,e,caps⟩:=WilsonMatrixTicketLanesTerminalQFees.billed R Q l simple K μ
  let w:=univ.sup fun t:∀i,Piece R (l i)=>power (word R l t)
  let minimum:=q+2*(e+1)
  refine ⟨max w minimum,fun n hn=>?_⟩
  have degree (t:∀i,Piece R (l i)):power (word R l t)≤n:=
    (Finset.le_sup (f:=fun t:∀i,Piece R (l i)=>power (word R l t)) (mem_univ t)).trans
      ((le_max_left _ _).trans hn)
  have ordered:minimum≤n:=(le_max_right _ _).trans hn
  obtain ⟨m₀,mature⟩:=eventually_atTop.1 (WilsonMatrixTicketLanesReportedAccuracy.coupon R simple q e C 1 cp.le zero_lt_one)
  obtain ⟨m₁,small⟩:=eventually_atTop.1 (IterationFour.Currency.g_small simple R.makes 1 zero_lt_one)
  refine ⟨degree,?_⟩
  filter_upwards [terminal R Q l simple paid n cap degree,eventually_ge_atTop m₀,eventually_ge_atTop m₁] with b marked after₀ after₁
  intro per k orders reader D g θ large T u o tag v inside
  let readers:=∏i,‖reader i‖
  let heat:=R.family.path.levels.clock.hatBeta (b+1)
  let Λ:=2+Real.log (R.family.path.levels.clock.hatBeta b)
  have rp:0≤readers:=prod_nonneg fun _ _=>norm_nonneg _
  have gp:0<g:=IterationFour.Currency.g_pos R.makes _ _ _ le_rfl
  have g₁:g≤1:=(small (b+1) (by omega) (b+1) per le_rfl).le
  have bp:1≤R.family.path.levels.clock.hatBeta b:=(R.family.path.levels.fits.delayed b).le
  have lp:0≤Λ:=add_nonneg (by norm_num) (Real.log_nonneg bp)
  have fee:=caps (b+1) k orders reader
  have low:C*heat^e*(g^(minimum+1)*Λ)≤g^q:=by
    simpa only [one_mul] using mature (b+1) (by omega) b (b+1) per (by omega) le_rfl
  have cheaper:g^(n+1)*Λ≤g^(minimum+1)*Λ:=mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one gp.le g₁ (Nat.succ_le_succ ordered)) lp
  calc
    _≤WilsonMatrixTicketLanesTerminalQGrades.fee R Q l θ k reader*(g^(n+1)*Λ):=marked per θ k reader large T u o tag v inside
    _≤(C*heat^e*readers)*(g^(n+1)*Λ):=mul_le_mul_of_nonneg_right fee (mul_nonneg (pow_nonneg gp.le _) lp)
    _=(C*heat^e*(g^(n+1)*Λ))*readers:=by ring
    _≤(C*heat^e*(g^(minimum+1)*Λ))*readers:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left cheaper (mul_nonneg cp.le (pow_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed (b+1)).le) _))) rp
    _≤_:=mul_le_mul_of_nonneg_right low rp

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogGradeMarket
