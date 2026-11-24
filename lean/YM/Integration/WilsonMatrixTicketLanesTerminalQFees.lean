import YM.Integration.WilsonMatrixTicketLanesTerminalQGrades
import YM.Integration.WilsonMatrixTicketLanesReportedAccuracy

/-! The closed first-block Q roster at its prescribed ultraviolet clock.
All price constants and the absolute degree precede the period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesTerminalQFees
open Filter Function Finset Lattice Wilson RG RG12 RG17 Precision Tree Extraction Source Labels Spec
open MS MS.Land MS.Menus MS.Rake MS.Local.Physical PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Spool FVA2 FVA2.CityHistory
open WilsonMatrixTicketLanesTerminalQWords WilsonMatrixTicketLanesReportedPrepaid
open WilsonMatrixTicketLanesTerminalQGrades
open private date from YM.Integration.WilsonReportingMeasuredWardFunding
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){B:Deck G}(Q:Prescription B){n:ℕ}(l:Fin n→Label B)

theorem billed (simple:G.Simple)(K:ℕ)(μ:ℝ):
    ∃C:ℝ,0<C ∧ ∃e:ℕ,∀(m:ℕ)(k:Fin n→ℕ), (∀i,k i≤K)→∀reader:Fin n→ℂ,
      fee R Q l (μ-R.family.S.scale m) k reader≤
        (C*R.family.path.levels.clock.hatBeta m^e)*(∏i,‖reader i‖):=by
  obtain ⟨C,cp,d,fees⟩:=ActualOriginalFeeGrowth.shifted_bound B Q l K μ
  obtain ⟨A,ap,dates⟩:=date R simple
  let c (i:Fin n)(t:Piece R (l i)):=ActualOriginalDictionary.coordinates R B t.1.size t.1.grade t.1.2.2 t.2
  let M:=∑t:∀i,Piece R (l i),∏i,‖c i (t i)‖
  let L:=C*A^d
  have lp:0<L:=mul_pos cp (pow_pos ap _)
  have Mp:0≤M:=sum_nonneg fun _ _=>prod_nonneg fun _ _=>norm_nonneg _
  refine ⟨L^n*(M+1),mul_pos (pow_pos lp n) (by linarith),d*n,?_⟩
  intro m k orders reader
  let H:=R.family.path.levels.clock.hatBeta m
  have hp:0≤H:=le_of_lt (WardBin.hot R.family.path.levels m)
  let readers:=∏i,‖reader i‖
  have rp:0≤readers:=prod_nonneg fun _ _=>norm_nonneg _
  have bound (i)(t:Piece R (l i)):‖oil (Q.fees (l i).h (l i).item) t.1 (k i) (μ-R.family.S.scale m)‖≤L*H^d:=by
    calc
      _≤C*(1+‖R.family.S.scale m‖)^d:=fees i _ (orders i) t.1 _
      _≤C*(A*H)^d:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (dates m) d) cp.le
      _=_:=by rw [mul_pow];dsimp [L];ring
  have each (t:∀i,Piece R (l i)):‖coefficient R Q l (μ-R.family.S.scale m) k reader t‖≤
      (readers*(L*H^d)^n)*(∏i,‖c i (t i)‖):=by
    unfold coefficient
    simp only [WilsonMatrixTicketLanesTerminalQWords.weight,norm_prod,norm_mul,prod_mul_distrib]
    let oils:=∏i,‖oil (Q.fees (l i).h (l i).item) (t i).1 (k i) (μ-R.family.S.scale m)‖
    have bill:oils≤(L*H^d)^n:=by
      calc
        _≤∏i:Fin n,(L*H^d):=prod_le_prod (fun i _=>norm_nonneg _) fun i _=>bound i (t i)
        _=_:=by simp
    have cp₁:0≤∏i,‖c i (t i)‖:=prod_nonneg fun _ _=>norm_nonneg _
    change readers*(oils*_)≤_
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bill rp) cp₁
  calc
    fee R Q l _ k reader≤∑t:∀i,Piece R (l i),(readers*(L*H^d)^n)*(∏i,‖c i (t i)‖):=sum_le_sum fun t _=>each t
    _=(readers*(L*H^d)^n)*M:=(mul_sum ..).symm
    _≤(readers*(L*H^d)^n)*(M+1):=mul_le_mul_of_nonneg_left (by linarith)
      (mul_nonneg rp (pow_nonneg (mul_nonneg lp.le (pow_nonneg hp _)) _))
    _=_:=by dsimp only [H,readers];rw [mul_pow,←pow_mul];ring

end YM.Integration.WilsonMatrixTicketLanesTerminalQFees
