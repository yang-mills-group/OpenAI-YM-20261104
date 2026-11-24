import YM.Integration.WilsonMatrixTicketLanesTerminalQFees

/-! Uniform physical first-block comparison at the actual filed ultraviolet clock. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesTerminalQBudget
open Filter Function Finset Lattice Wilson RG RG12 RG17 Precision Tree Extraction Source Labels Spec
open MS MS.Land MS.Menus MS.Rake MS.Local.Physical PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Spool FVA2 FVA2.CityHistory
open Pert.Asymptotics
open WilsonMatrixTicketLanesTerminalQWords WilsonMatrixTicketLanesReportedPrepaid
open WilsonMatrixTicketLanesTerminalQGrades
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){B:Deck G}(Q:Prescription B){n:ℕ}(l:Fin n→Label B)

theorem purchased (simple:G.Simple)(paid:Paid G R.kit)(K cap q:ℕ)(μ:ℝ){ε:ℝ}(ep:0<ε):
    ∃ (order : ℕ), (q ≤ order) ∧ (∀ t : ∀ i, Piece R (l i), power (word R l t) ≤ order) ∧
      ∀ᶠ b:ℕ in atTop,∀(per:ℕ)(k:Fin n→ℕ),(∀i,k i≤K)→∀reader:Fin n→ℂ,
        let D:=R.family.path.levels.clock.op b per
        let g:=regulatorRun R.family (b+1) per (b+1)
        let θ:=μ-R.family.S.scale (b+1)
        ∀(large:Bid.Larger (G:=G) D)(T:Forest D.ratio)(u:Pins G (R.family.side b per))
          (o:Fin n→Site (R.family.side (b+1) per))(tag:D.Choices)(v:(Descent.nil (top:=R.family.side (b+1) per)).Tags),
          (∀i,‖u i‖≤(cap:ℝ)+1)→
          ‖WilsonMatrixTicketLanesTerminalQReturn.measured R Q l θ k reader u o-
            stack R Q l order θ k reader large T u o tag v‖≤ε*g^q*(∏i,‖reader i‖):=by
  obtain ⟨C,cp,e,caps⟩:=WilsonMatrixTicketLanesTerminalQFees.billed R Q l simple K μ
  let w:=univ.sup fun t:∀i,Piece R (l i)=>power (word R l t)
  let p:=q+w
  let degreeBound:=p+2*(e+1)
  have qp:q≤p:=Nat.le_add_right q w
  have degree (t:∀i,Piece R (l i)):power (word R l t)≤degreeBound:=by
    have top:power (word R l t) ≤ w := Finset.le_sup (f:=fun t:∀i,Piece R (l i)=>power (word R l t)) (mem_univ t)
    dsimp only [degreeBound,p];omega
  obtain ⟨m₀,mature⟩:=eventually_atTop.1 (WilsonMatrixTicketLanesReportedAccuracy.coupon R simple p e C ε cp.le ep)
  obtain ⟨m₁,small⟩:=eventually_atTop.1 (IterationFour.Currency.g_small simple R.makes 1 zero_lt_one)
  refine ⟨degreeBound,?_,degree,?_⟩
  · dsimp only [degreeBound];omega
  filter_upwards [terminal R Q l simple paid degreeBound cap degree,eventually_ge_atTop m₀,eventually_ge_atTop m₁] with b measured after₀ after₁
  intro per k orders reader D g θ large T u o tag v inside
  let readers:=∏i,‖reader i‖
  let heat:=R.family.path.levels.clock.hatBeta (b+1)
  let cost:=g^(degreeBound+1)*(2+Real.log (R.family.path.levels.clock.hatBeta b))
  have rp:0≤readers:=prod_nonneg fun _ _=>norm_nonneg _
  have gp:0<g:=IterationFour.Currency.g_pos R.makes _ _ _ le_rfl
  have g₁:g≤1:=(small (b+1) (by omega) (b+1) per le_rfl).le
  have bp:1≤R.family.path.levels.clock.hatBeta b:=(R.family.path.levels.fits.delayed b).le
  have c₀:0≤cost:=mul_nonneg (pow_nonneg gp.le _) (add_nonneg (by norm_num) (Real.log_nonneg bp))
  have fee:=caps (b+1) k orders reader
  have received:C*heat^e*cost ≤ε*g^p:=mature (b+1) (by omega) b (b+1) per (by omega) le_rfl
  calc
    _≤WilsonMatrixTicketLanesTerminalQGrades.fee R Q l θ k reader*cost:=measured per θ k reader large T u o tag v inside
    _≤(C*heat^e*readers)*cost:=mul_le_mul_of_nonneg_right fee c₀
    _=(C*heat^e*cost)*readers:=by ring
    _≤(ε*g^p)*readers:=mul_le_mul_of_nonneg_right received rp
    _≤_:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp.le g₁ qp) ep.le) rp

end YM.Integration.WilsonMatrixTicketLanesTerminalQBudget
