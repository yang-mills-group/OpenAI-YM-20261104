import YM.Integration.WilsonThermometerWeakPairCharged
import YM.Integration.WilsonThermometerWeakPairBornFare

/-! Actual three-physical-field bound, with all input grades and the original
oriented exterior.  The logarithmic exponent is fixed before the window. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairBorn
open Function Finset Filter Set Table Spec OPE OPE.Orbits OPE.Prescription OPE.Log EveryPhase OPE.Nesting
open Trace Trace.Pilot RG17 PhysMS PhysMS.Frame GapsContact GapsContact.Ascent GapsContact.Seams
open OPE.Levy Extraction Maxwell XSpace XSpace.Normalize Frontier6 Frontier6.Tale PhysicalNext.Repeat.Legato
open Next.UVStress Trace.Terrace
open WilsonThermometerWeakMovingCorner OPE.Arboreal
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
universe u
local notation "child" => WilsonThermometerWeakPairRooms.near
local notation "sites" => WilsonThermometerWeakPairFork.position
local notation "rent" => WilsonThermometerWeakPairInventory.rent
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {P:Prescription F.sector.derivatives}
theorem original {simple:G.Simple}{L:Almanac F}(H:Roll.{u} F simple L)
    (agency:∀U:Ultrafilter (ℕ×ℕ),(U:Filter _)≤f.fuse→MatrixTicket (C:=R.family) S F.sector.derivatives (U:Filter _))
    (hp:P.Coherent)(bank:LogTrace F P)(J:ℝ→tower S)(V:Store G)(lead:Leading F J)
    (d:↥child→ℕ)(e h:ℕ)(v:∀i,RG17.Free R.family (d i))(w:RG17.Free R.family e)(q:Viewers F)
    {M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃(B:ℝ)(k:ℕ),0≤B ∧ ∀(t:ℝ→ℝ),Tendsto t trail trail→∀ᶠ r in trail,r≤t r→
      ∀(x y z:E4),‖x‖≤M → ‖y‖≤M → ‖z‖≤M → 2*δ≤‖z‖ → δ≤‖x-y‖ → r*M≤(t r)*δ →
        let X:=crop (sites r (t r) x y z) child
        ‖WilsonThermometerWeakPairExpansion.residual (spectator F q) P h X 0 (born J r v)
          ((t r) • z) (far F J e (t r) w).2‖≤B*dock r^k*((t r)+(r/(t r))^(h+1)):=by
  obtain ⟨C,K,cp,stage⟩:=WilsonThermometerWeakPairCharged.original F bank hp h q d e mn dp
  choose N n np wages using fun i=>WilsonThermometerWeakPairBornFare.original F P H agency hp J V lead (d i) (v i)
  obtain ⟨E,l,ep,salary⟩:=WilsonThermometerWeakPairBornFare.reflected F P H agency hp J V lead e w
  refine ⟨(∏i,N i)*E*C,(∑i,n i)+l+2*K,mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _=>np i) ep) cp,?_⟩
  intro t ht
  have small:∀ᶠ u in trail,u≤1:=(ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [ht.eventually stage,eventually_all.mpr wages,ht.eventually salary,
    ht.eventually small,self_mem_nhdsWithin] with r use fee pay top rp
  intro rt x y z hx hy hz fz xy gap
  change 0<r at rp
  have tp:=rp.trans_le rt
  let X:=crop (sites r (t r) x y z) child
  let w':=(far F J e (t r) w).2
  have unit:=dock_valid r ⟨rp,rt.trans top⟩
  have dt:=dock_valid (t r) ⟨tp,top⟩
  have slide:=dock_fold r (t r) rp rt
  have bb (u:ℝ)(up:0<u)(ce:u≤1):0≤badge u ∧ badge u≤dock u:=by
    unfold badge OPE.run dock LogV;rw [Real.log_inv];constructor <;> linarith [Real.log_nonpos up.le ce]
  have a:=bb r rp (rt.trans top)
  have b:=bb (t r) tp top
  have bw: (badge (t r)*badge r)^K≤dock r^(2*K):=by
    rw [pow_mul,sq]
    apply pow_le_pow_left₀ (mul_nonneg b.1 a.1)
    exact mul_le_mul (b.2.trans slide) a.2 a.1 (zero_le_one.trans unit)
  have nw: (∏i:↥child,rent P (d i) r (born J r v i)) ≤ (∏i,N i)*dock r^(∑i,n i):=by
    rw [←Finset.prod_pow_eq_pow_sum,←Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun i _=>Finset.sum_nonneg fun j _=>div_nonneg (norm_nonneg _) (pow_nonneg rp.le _)) (fun i _=>fee i)
  have fw: rent P e (t r) w'≤E*dock r^l:=pay.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans dt) slide _) ep)
  have sf:0≤rent P e (t r) w':=Finset.sum_nonneg fun j _=>div_nonneg (norm_nonneg _) (pow_nonneg tp.le _)
  have money:=use r x y z rp rt hx hy hz fz xy gap (born J r v) w'
  refine money.trans ?_
  calc
    _ ≤ ((∏i,N i)*dock r^(∑i,n i))*(E*dock r^l)*(C*dock r^(2*K)*((t r)+(r/(t r))^(h+1))):=by
      apply mul_le_mul (mul_le_mul nw fw sf (mul_nonneg (Finset.prod_nonneg fun i _=>np i) (pow_nonneg (zero_le_one.trans unit) _)))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bw cp) (by positivity))
      · exact mul_nonneg (mul_nonneg cp (pow_nonneg (mul_nonneg b.1 a.1) _)) (by positivity)
      · exact mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _=>np i) (pow_nonneg (zero_le_one.trans unit) _))
          (mul_nonneg ep (pow_nonneg (zero_le_one.trans unit) _))
    _ = _:=by simp only [pow_add];ring
end YM.Integration.WilsonThermometerWeakPairBorn
end
