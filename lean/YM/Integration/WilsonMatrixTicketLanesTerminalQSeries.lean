import YM.Integration.WilsonMatrixTicketLanesTerminalQCoefficients
import YM.Integration.WilsonMatrixTicketLanesTerminalQFees
import YM.Integration.WilsonMatrixTicketLanesReportedAccuracy

noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesTerminalQSeries
open Filter Function Finset Lattice Wilson RG RG12 RG17 Precision Tree Extraction Source Labels Spec
open MS MS.Land MS.Menus MS.Rake MS.Local.Physical PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Spool FVA2 FVA2.CityHistory
open Pert.Asymptotics
open WilsonMatrixTicketLanesTerminalQWords WilsonMatrixTicketLanesReportedPrepaid
open WilsonMatrixTicketLanesTerminalQGrades
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){B:Deck G}(Q:Prescription B){n:ℕ}(l:Fin n→Label B)

private theorem entry {g clock C:ℝ}{W w n k:ℕ}{a:ℕ→ℂ}
    (gp:0<g)(gs:g≤1)(cp:0≤C)(lp:0≤clock)(hot:g^2*clock≤6)
    (height:w≤W)(level:k≤n)(principal:‖a 0‖≤g⁻¹^w*C+g*clock)
    (positive:∀j:ℕ,j+1≤n→‖a (j+1)‖≤(1+g)*clock):
    g^(W+2)*‖if w≤k then a (k-w) else 0‖≤C+12:=by
  by_cases active:w≤k
  · rw [if_pos active]
    have power:g^(W+2)≤g^2:=pow_le_pow_of_le_one gp.le gs (by omega)
    cases h:k-w with
    | zero =>
      have inv:g^(W+2)*g⁻¹^w≤1:=calc
        _≤g^w*g⁻¹^w:=mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one gp.le gs (by omega)) (by positivity)
        _=1:=by rw [←mul_pow,mul_inv_cancel₀ gp.ne',one_pow]
      have err:g^(W+2)*(g*clock)≤6:=(mul_le_mul power
        (show g*clock≤clock by simpa using mul_le_mul_of_nonneg_right gs lp) (mul_nonneg gp.le lp) (sq_nonneg g)).trans hot
      calc
        _≤g^(W+2)*(g⁻¹^w*C+g*clock):=mul_le_mul_of_nonneg_left principal (by positivity)
        _=(g^(W+2)*g⁻¹^w)*C+g^(W+2)*(g*clock):=by ring
        _≤C+12:=by have z:=mul_le_mul_of_nonneg_right inv cp; linarith
    | succ j =>
      have pos:=positive j (by omega)
      have factor:(1+g)*clock≤2*clock:=mul_le_mul_of_nonneg_right (by linarith) lp
      have each:=mul_le_mul power (pos.trans factor) (norm_nonneg _) (sq_nonneg g)
      linarith [show g^2*(2*clock)=2*(g^2*clock) by ring]
  · simp [active]; linarith

def term {b per:ℕ}(θ:ℝ)(k:Fin n→ℕ)(reader:Fin n→ℂ)(j:ℕ)
    (large:Bid.Larger (G:=G) (R.family.path.levels.clock.op b per))
    (T:Forest (R.family.path.levels.clock.op b per).ratio)(u:Pins G (R.family.side b per))
    (o:Fin n→Site (R.family.side (b+1) per))(tag:(R.family.path.levels.clock.op b per).Choices)
    (v:(Descent.nil (top:=R.family.side (b+1) per)).Tags):ℂ:=
  ∑t:∀i,Piece R (l i),coefficient R Q l θ k reader t *
    if power (word R l t) ≤ j then
      WilsonCoherentJointReturn.series (word R l t) (R.family.path.levels.clock.op b per) T R.metals.O u o large tag v
        (j-power (word R l t)) else 0

theorem purchased (simple:G.Simple)(paid:Paid G R.kit)(K cap:ℕ)(μ:ℝ):
    ∃(E:ℕ)(C:ℝ),0<C ∧ ∀nq:ℕ,∀ᶠ b:ℕ in atTop,∀(per:ℕ)(k:Fin n→ℕ),(∀i,k i≤K)→∀reader:Fin n→ℂ,
      let D:=R.family.path.levels.clock.op b per
      let g:=regulatorRun R.family (b+1) per (b+1)
      let θ:=μ-R.family.S.scale (b+1)
      ∀(large:Bid.Larger (G:=G) D)(T:Forest D.ratio)(u:Pins G (R.family.side b per))
        (o:Fin n→Site (R.family.side (b+1) per))(tag:D.Choices)(v:(Descent.nil (top:=R.family.side (b+1) per)).Tags),
        (∀i,‖u i‖≤(cap:ℝ)+1)→∀j:ℕ,j≤nq→
        g^E*‖term R Q l θ k reader j large T u o tag v‖≤C*(∏i,‖reader i‖):=by
  obtain ⟨A,ap,e,fees⟩:=WilsonMatrixTicketLanesTerminalQFees.billed R Q l simple K μ
  obtain ⟨C,cp,zero⟩:=WilsonMatrixTicketLanesTerminalQCoefficients.purchased R l simple paid 0 cap
  let W:=univ.sup (fun t:∀i,Piece R (l i)=>power (word R l t))
  have wp (t:∀i,Piece R (l i)):power (word R l t)≤W:=le_sup (f:=fun t:∀i,Piece R (l i)=>power (word R l t)) (mem_univ t)
  obtain ⟨b₀,small⟩:=eventually_atTop.mp (WilsonMatrixTicketLanesReportedAccuracy.small R simple 1 zero_lt_one)
  refine ⟨2*e+(W+2),(2:ℝ)^e*(A*(C+12)),by positivity,?_⟩
  intro nq
  obtain ⟨_,_,coeffs⟩:=WilsonMatrixTicketLanesTerminalQCoefficients.purchased R l simple paid nq cap
  filter_upwards [zero,coeffs,eventually_ge_atTop b₀] with b initial rows late
  intro per k orders reader D g θ large T u o tag v inside j hj
  let H:=R.family.path.levels.clock.hatBeta (b+1)
  let clock:=2+Real.log (R.family.path.levels.clock.hatBeta b)
  have gp:0<g:=IterationFour.Currency.g_pos R.makes _ _ _ le_rfl
  have gs:g≤1:=small (b+1) (by omega) (b+1) per le_rfl
  have bp:1≤R.family.path.levels.clock.hatBeta b:=(R.family.path.levels.fits.delayed b).le
  have lp:0≤clock:=by dsimp [clock]; exact add_nonneg (by norm_num) (Real.log_nonneg bp)
  have heat:H*g^2≤2:=WilsonMatrixTicketLanesReportedAccuracy.thermal R _ _ _ le_rfl
  have inc:R.family.path.levels.clock.hatBeta b≤H:=WilsonStartup.Timing.hat_mono R.family.path.levels
    (Gauge.slopeConstant_pos simple).le (Nat.le_succ b)
  have lc:clock≤3*H:=by dsimp [clock]; linarith [Real.log_le_self (zero_le_one.trans bp)]
  have hot:g^2*clock≤6:=by
    have u₀:=mul_le_mul_of_nonneg_left lc (sq_nonneg g)
    linarith [show g^2*(3*H)=3*(H*g^2) by ring]
  let c (t:∀i,Piece R (l i)):=coefficient R Q l θ k reader t
  let a (t:∀i,Piece R (l i)):=WilsonCoherentJointReturn.series (word R l t) D T R.metals.O u o large tag v
  let val (t:∀i,Piece R (l i)):=if power (word R l t)≤j then a t (j-power (word R l t)) else 0
  have spent (t:∀i,Piece R (l i)):g^(W+2)*‖val t‖≤C+12:=entry gp gs cp lp hot (wp t) hj
    (initial per large T u o tag v inside t).1 (rows per large T u o tag v inside t).2
  let load:=fee R Q l θ k reader
  have full:g^(W+2)*‖term R Q l θ k reader j large T u o tag v‖≤load*(C+12):=calc
    _≤g^(W+2)*(∑t,‖c t*val t‖):=mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _=∑t,‖c t‖*(g^(W+2)*‖val t‖):=by rw [mul_sum];apply sum_congr rfl;intro t _;rw [norm_mul];ring
    _≤∑t,‖c t‖*(C+12):=sum_le_sum fun t _=>mul_le_mul_of_nonneg_left (spent t) (norm_nonneg _)
    _=_:=(sum_mul ..).symm
  let U:=∏i,‖reader i‖
  have bill:load≤A*H^e*U:=fees (b+1) k orders reader
  calc
    _≤g^(2*e)*(load*(C+12)):=by rw [pow_add,mul_assoc]; exact mul_le_mul_of_nonneg_left full (by positivity)
    _≤g^(2*e)*((A*H^e*U)*(C+12)):=mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right bill (by linarith)) (by positivity)
    _=(H*g^2)^e*(A*(C+12))*U:=by rw [mul_pow,pow_mul];ring
    _≤_:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by
      exact mul_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed (b+1)).le) (sq_nonneg g)) heat e)
      (by positivity)) (by dsimp [U];positivity)

end YM.Integration.WilsonMatrixTicketLanesTerminalQSeries
