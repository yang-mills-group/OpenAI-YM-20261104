import YM.Integration.WilsonOlderFreshConnectedBirth
import YM.Integration.WilsonOlderFreshUnaryCourse
import YM.Integration.WilsonOlderFreshGraphPointWallet
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshConnectedGross
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology

open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket
open WilsonOriginalReceivedChain Comparison.RG02 WilsonOlderFreshConnectedBirth
variable {G:Gauge}{d Q:ℕ}
def tariff (d Q:ℕ)(g:ℝ):ℝ:=(g^d)⁻¹*2^(Q+d)

theorem summand {n:Side}{σ g:ℝ}(T:Copy G d Q σ)(ranked:∀z:T.Roster,((T.roll z.1).leg z.2.1).r ≤ z.1.val+d)(site:Site n)(A:Unit → Set ℂ)
    (t:Wallet A)(s₀:0 ≤ σ)(hg:0<g)(small:g ≤ 1)(U:Config G n)(z:T.Roster):
    let M:=T.rows (WilsonOlderFreshGraphPointWallet.point site) A
    ‖(M z).nominal g t U‖ ≤ (‖value A t‖*tariff d Q g)*(M z).height σ:=by
  let S:=WilsonOlderFreshGraphPointWallet.point site
  let M:=T.rows S A
  let Y:=(T.roll z.1).leg z.2.1
  have rank:Y.r ≤ z.1.val+d:=ranked z
  have degree:z.1.val ≤ Q:=Nat.le_of_lt_succ z.1.isLt
  have low:-(↑d:ℤ) ≤ (z.1.val:ℤ)-Y.r:=by omega
  have lag:|g^((z.1.val:ℤ)-Y.r)| ≤ (g^d)⁻¹:=by
    rw [abs_of_pos (zpow_pos hg _)]
    simpa only [zpow_neg,zpow_natCast] using zpow_le_zpow_right_of_le_one₀ hg small low
  have mag:Y.atom.magnitude ≤ (M z).salary:=by
    change Y.atom.magnitude ≤ Y.atom.magnitude*Real.exp (σ*Y.atom.length)
    exact le_mul_of_one_le_right z.2.property.le (Real.one_le_exp (mul_nonneg s₀ (Nat.cast_nonneg _)))
  have height:(M z).salary ≤ (M z).height σ:=le_mul_of_one_le_right (M z).sound.le
    (Real.one_le_exp (mul_nonneg s₀ (Nat.cast_nonneg _)))
  have peak:(2:ℝ)^Y.r ≤ 2^(Q+d):=pow_le_pow_right₀ (by norm_num) (by omega)
  have leg:|Y.atom.unmasked U S.center| ≤ (M z).height σ*2^(Q+d):=
    (Y.atom.unmasked_bound U S.center).trans (mul_le_mul (mag.trans height) peak (by positivity) (by exact (z.2.property.le.trans mag).trans height))
  change ‖(M z).nominal g t U‖  ≤  _
  rw [T.group]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  change ‖value A t‖*(|g^((z.1.val:ℤ)-Y.r)| * |Y.atom.unmasked U S.center|) ≤ _
  calc
    _  ≤  ‖value A t‖*((g^d)⁻¹*((M z).height σ*2^(Q+d))):=
      mul_le_mul_of_nonneg_left (mul_le_mul lag leg (abs_nonneg _) (by positivity)) (norm_nonneg _)
    _ = _:=by unfold tariff;ring

theorem posted {n:Side}{σ g:ℝ}(T:Copy G d Q σ)(ranked:∀z:T.Roster,((T.roll z.1).leg z.2.1).r ≤ z.1.val+d)(site:Site n)(A:Unit → Set ℂ)
    (t:Wallet A)(s₀:0 ≤ σ)(hg:0<g)(small:g ≤ 1)(U:Config G n):
    let M:=T.rows (WilsonOlderFreshGraphPointWallet.point site) A
    Summable (fun z=>Spill.raw M g t z U) ∧
    ∀s,‖(Spill.Foundry.uncut M g t U).part s‖ ≤ (‖value A t‖*tariff d Q g)*(∑j,T.fare j):=by
  let S:=WilsonOlderFreshGraphPointWallet.point site
  let M:=T.rows S A
  let C:=‖value A t‖*tariff d Q g
  have c₀:0 ≤ C:=by dsimp [C,tariff];positivity
  have bank:SumBudget (fun z:T.Roster=>(M z).height σ) (∑j,T.fare j):=by
    have funding:=WilsonOlderFreshGraphVote.before_tests S T.roll T.fare σ T.paid T.legal T.positive (value A) s₀
    change SumBudget (fun z:T.Roster=>(M z).height σ) (Real.exp (σ*S.length)*(∑j,T.fare j)) at funding
    have len:S.length=0:=WilsonOriginalStarSceneRows.length ..
    simpa only [len,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] using funding
  have wages:=bank.2.1.mul_left C
  have fee (s:(Stock.census Unit).Mode)(z:T.Roster):‖(Spill.raw M g t z U).part s‖ ≤  C*(M z).height σ:=by
    change ‖(Poly.send (M z).mode ((M z).nominal g t U)).part s‖ ≤ _
    rw [Poly.part_send]
    split_ifs
    · exact summand T ranked site A t s₀ hg small U z
    · rw [norm_zero];exact mul_nonneg c₀ (bank.1 z)
  have summable:Summable (fun z=>Spill.raw M g t z U):=by
    apply Pi.summable.mpr
    exact fun s=>Summable.of_norm_bounded wages (fee s)
  refine ⟨summable,?_⟩
  intro s
  rw [show (Spill.Foundry.uncut M g t U).part s=∑'z,(Spill.raw M g t z U).part s from
    ((Pi.hasSum.mp summable.hasSum) s).tsum_eq.symm]
  have each:=Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fee s) wages
  calc
    _  ≤  ∑' z,‖(Spill.raw M g t z U).part s‖:=norm_tsum_le_tsum_norm each
    _  ≤  ∑' z,C*(M z).height σ:=each.tsum_le_tsum (fee s) wages
    _  ≤  _:=by rw [tsum_mul_left];exact mul_le_mul_of_nonneg_left bank.2.2 c₀

variable {n e j:ℕ}{k D:Fin n  →  ℕ}{S J:Finset (Fin n)}{A δ σ:ℝ}
variable (R:Run G)(Y:Realm G (e+1) Credit.leanC)(lo:Y.anchor  ≤  j)(enrolled:Paid R Y lo D k δ σ)
variable (N:ℕ) (c:Fin n)(X:Input Y lo S k D A)(included:J⊆S)(pin:c∈J)(positive:0  ≤  A)
variable (older:j<N)(deep:0 < mass k J)(sw:0  ≤  σ)(o:Cover)(t:Case D)(u:Frill J c)
local notation "M₀" => R.family.path.levels.clock.hatBeta j^δ*A^J.card


local notation "T" => WilsonOlderFreshConnectedBirth.issued R Y lo enrolled N c X included pin positive older deep sw o t u


theorem ranked(z:(T).Roster):(((T).roll z.1).leg z.2.1).r ≤ z.1.val+mass k J:=by
  let i:=z.2.1.val.1
  have rnk:i.val ≤ mass k J+z.1.val:=Nat.le_of_lt_succ i.isLt
  exact rnk.trans_eq (Nat.add_comm ..)

theorem original {n':Side}{g:ℝ}(site:Site n')(A₀:Unit → Set ℂ)(x:Wallet A₀)
    (pos:0<g)(small:g ≤ 1)(U:Config G n'):
    let B:=(T).rows (WilsonOlderFreshGraphPointWallet.point site) A₀
    Summable (fun z=>Spill.raw B g x z U) ∧ ∀s,‖(Spill.Foundry.uncut B g x U).part s‖ ≤ 
      (‖value A₀ x‖*tariff (mass k J) e g)*
        ((e+1:ℕ)*((mass k J+e+1:ℕ)*((∏v∈J,‖t v‖)*M₀))):=by
  have cap:=posted (T) (ranked R Y lo enrolled N c X included pin positive older deep sw o t u)
    site A₀ x sw pos small U
  refine ⟨cap.1,fun s=>(cap.2 s).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (WilsonOlderFreshConnectedBirth.account R Y lo enrolled N c X included pin positive older deep sw o t u)
    (mul_nonneg (norm_nonneg _) (by unfold tariff;positivity))

end YM.Integration.WilsonOlderFreshConnectedGross
end
