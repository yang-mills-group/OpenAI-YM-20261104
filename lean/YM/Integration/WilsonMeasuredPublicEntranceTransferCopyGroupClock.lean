import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyGroupFare
import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyOpticalBudget
import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyAwardPrice
import YM.Integration.WilsonMeasuredPublicEntranceMeshClock
/-! The per-copy salary at capture on the actual optical interval. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopyGroupClock
open Filter Real Wilson Lattice RG
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open WilsonOriginalPublicTrialPhaseGroup (wage)
open scoped Classical Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "C" => R.family
local notation "H" i:arg => (C).path.levels.clock.hatBeta i
local notation "S" => (C).S
local notation "σ" => G.slopeConstant

include simple in
theorem original {I:Type}[Fintype I][DecidableEq I](i:I)(A p L:ℕ)(T Z:ℝ)(t0:1≤T)(z0:0≤Z+1/2):
    ∀ᶠ c:ℕ in atTop,∀K:ℕ,c+1≤K→H K≤2*H c→(S).a c/(S).a K≤(H K)^A →
    ∃ B:ℝ,1≤B ∧ 7*(H (c+1))^2*B≤exp (H c/(10*σ)) ∧
      ∀{V:Type}[Fintype V][DecidableEq V] (v:V) (w:V×I→ℝ) (z:ℝ) (l:ℕ),
      z≤Z → l≤L → (∀t,0<w (v,t)) →
      (∀t,(w (v,t))⁻¹≤(4*(H c)^2)^(K-(c+1))*(T*(H c)^p)) →
      (wage i w z (renal (C).path.levels (c+1)) l ((),v))⁻¹≤B:=by
  let n:=Fintype.card I
  let E:ℝ:=1+n*16*T*exp ((Z+1/2)*L)
  let D:=2*WilsonMeasuredPublicEntranceMeshClock.allowance A
  have e0:1≤E:=by
    dsimp only [E]
    have t:=zero_le_one.trans t0
    exact le_add_of_nonneg_right (by positivity)
  have d0:0≤D:=mul_nonneg (by norm_num) (WilsonMeasuredPublicEntranceMeshClock.nonneg A)
  have late:=Next.Rank.Station.hat_rate R.family.path.levels simple
  have reserve:=late.eventually (WilsonMeasuredPublicEntranceTransferCopyOpticalBudget.original
    σ D E (Gauge.slopeConstant_pos simple) d0 (zero_le_one.trans e0) (p+2) n)
  obtain ⟨start,steps⟩:=eventually_atTop.mp (RG01.Physical.nextHat simple R.family.path.levels)
  filter_upwards [reserve,eventually_ge_atTop start,late.eventually_ge_atTop (2:ℝ)] with c bound first big
  intro K ck heat apron
  let m:=K-(c+1)
  let dH:=H c
  let B:ℝ:=(E*dH^(p+2)*(4*dH^2)^m)^n
  have h1:1≤dH:=by dsimp [dH];linarith only [big]
  have hp:0<dH:=zero_lt_one.trans_le h1
  have hr:0<H K:=zero_lt_one.trans_le ((C).path.levels.fits.delayed K).le
  have mono:=log_le_log hr heat
  rw [log_mul (by norm_num) hp.ne'] at mono
  have two:log 2≤log dH:=log_le_log (by norm_num) big
  have count:= (WilsonMeasuredPublicEntranceMeshClock.original R (show c≤K by omega) A apron).1
  have length:(m:ℝ)≤D*(1+log dH):=by
    dsimp only [D]
    have a:=WilsonMeasuredPublicEntranceMeshClock.nonneg A
    exact count.trans (by nlinarith only [mul_le_mul_of_nonneg_left mono a,
      mul_le_mul_of_nonneg_left two a,a])
  have mode:1≤(4*dH^2)^m:=one_le_pow₀ (by nlinarith only [one_le_pow₀ h1 (n:=2)])
  have b1:1≤B:=one_le_pow₀ (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le e0 (one_le_pow₀ h1)) mode)
  have left:=steps c first
  have right:=steps (c+1) (by omega)
  have h2:0<H (c+2):=zero_lt_one.trans_le ((C).path.levels.fits.delayed (c+2)).le
  have cool:H (c+2)≤4*dH:=by change _≤4*H c;linarith only [left,right]
  have hNext:0≤H (c+1):=zero_le_one.trans ((C).path.levels.fits.delayed (c+1)).le
  have ren:0<renal (C).path.levels (c+1):=by unfold renal PhysicalNext.Repeat.Mallow.probe;exact Real.rpow_pos_of_pos h2 _
  have inverse:(renal (C).path.levels (c+1))⁻¹≤16*dH^2:=by
    change ((H (c+2))^(-(2:ℝ)))⁻¹≤_
    rw [rpow_neg h2.le,inv_inv]
    simpa only [rpow_two] using (pow_le_pow_left₀ h2.le cool 2).trans_eq (by ring)
  refine ⟨B,b1,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hNext (by change _≤4*H c; linarith only [left,hNext]:H (c+1)≤4*dH) 2) (by norm_num))
      (zero_le_one.trans b1)).trans (bound m length)
  intro V _ _ v w z l zcap sites positive fee
  let E0:=exp ((z+1/2)*l)
  have ec:E0≤exp ((Z+1/2)*L):=exp_le_exp.mpr
    (mul_le_mul (by linarith only [zcap]) (Nat.cast_le.mpr sites) (Nat.cast_nonneg _) z0)
  refine (WilsonMeasuredPublicEntranceTransferCopyGroupFare.inverse i v w z _ _ l ren positive fee).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  change (n:ℝ)*(renal (C).path.levels (c+1))⁻¹*((4*dH^2)^m*(T*dH^p))*E0≤_
  calc _≤n*(16*dH^2)*((4*dH^2)^m*(T*dH^p))*exp ((Z+1/2)*L):=
          mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left inverse (by positivity)) (by positivity))
            ec (exp_pos _).le (by positivity)
       _=(n*16*T*exp ((Z+1/2)*L))*dH^(p+2)*(4*dH^2)^m:=by rw [pow_add];ring
       _≤E*dH^(p+2)*(4*dH^2)^m:=by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp only [E];linarith
end YM.Integration.WilsonMeasuredPublicEntranceTransferCopyGroupClock
end
