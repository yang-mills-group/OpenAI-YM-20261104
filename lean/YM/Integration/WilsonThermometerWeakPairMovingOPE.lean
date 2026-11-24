import YM.Integration.WilsonThermometerWeakPairBorn
import YM.Integration.WilsonThermometerWeakPairSameFrame
import YM.Integration.WilsonThermometerWeakPairNumeric

/-! The measured ordinary OPE of two near fields against one genuine moving
reflected exterior. The denominator power is issued before the detector
distance is selected. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairMovingOPE
open Function Finset Filter Set Table Spec OPE OPE.Orbits OPE.Prescription OPE.Log EveryPhase OPE.Nesting
open Trace Trace.Pilot RG17 PhysMS PhysMS.Frame GapsContact GapsContact.Ascent GapsContact.Seams
open OPE.Levy Extraction Maxwell XSpace XSpace.Normalize Frontier6 Frontier6.Tale PhysicalNext.Repeat.Legato
open WilsonThermometerWeakMovingCorner OPE.Arboreal WilsonThermometerWeakPairClock
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
universe u
local notation "child" => WilsonThermometerWeakPairRooms.near
local notation "sites" => WilsonThermometerWeakPairFork.position
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {P:Prescription F.sector.derivatives}
theorem original {simple:G.Simple}{L:Almanac F}(H:Roll.{u} F simple L)
    (agency:∀U:Ultrafilter (ℕ×ℕ),(U:Filter _)≤f.fuse→MatrixTicket (C:=R.family) S F.sector.derivatives (U:Filter _))
    (hp:P.Coherent)(bank:LogTrace F P)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (book:Foundation F Q)(J:ℝ→tower S)(V:Store G)(lead:Leading F J)(g:ℝ→ℝ)(hg:Coupling G g)
    (d:↥child→ℕ)(e h:ℕ)(v:∀i,RG17.Free R.family (d i))(w:RG17.Free R.family e)(q:Viewers F)
    {M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃(A:ℕ)(C:ℝ),0≤C ∧ ∀(B:ℕ),∀ᶠ r in trail,let t:=scale g B r
      ∀(x y z:E4),‖x‖≤M → ‖y‖≤M → ‖z‖≤M → 2*δ≤‖z‖ → δ≤‖x-y‖ → r*M≤t*δ →
        let X:=crop (sites r t x y z) child
        ‖formula F Q X 0 (born J r v) (sole (t • z))
          (sole ((far F J e t w).2):Labels S (fun _:Unit=>e)) h q‖≤C/(g r)^A*(r/t)^(h+1):=by
  obtain ⟨C,k,cp,owed⟩:=WilsonThermometerWeakPairBorn.original F H agency hp bank J V lead d e h v w q mn dp
  obtain ⟨E,l,ep,change⟩:=WilsonThermometerWeakPairSameFrame.original F H hp Q book J V lead v h e w mn dp
    (show (0:ℝ)<1/4 by norm_num)
  obtain ⟨L₁,lp,tariff⟩:=WilsonThermometerWeakPairNumeric.tariff simple g hg (k+l)
  refine ⟨2*(k+l),(2*C+E)*L₁,mul_nonneg (by linarith) lp.le,?_⟩
  intro B
  let t:=scale g B
  have ht:=WilsonThermometerWeakPairClock.small simple g hg B
  have small:∀ᶠ u in trail,u≤1:=(ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [owed t ht,change t ht,tariff,WilsonThermometerWeakPairClock.ordered simple g hg B,
    WilsonThermometerWeakPairNumeric.errors simple g hg B h,ht.eventually small,self_mem_nhdsWithin] with r bill paid cap rt errs top rp
  change 0<r at rp
  have tp:0<t r:=rp.trans_le rt
  let Z:=(r/t r)^(h+1)
  have zn:0≤Z:=pow_nonneg (div_nonneg rp.le tp.le) _
  have tm:t r≤Z:=errs.1
  have engine:r^((h:ℝ)+1-(1/4:ℝ))/(t r)^((h:ℝ)+(1/4:ℝ))≤Z:=errs.2
  have unit:=dock_valid r ⟨rp,rt.trans top⟩
  have ut:=dock_valid (t r) ⟨tp,top⟩
  have pk:dock r^k≤dock r^(k+l):=pow_le_pow_right₀ unit (by omega)
  have pl:dock (t r)^l≤dock r^(k+l):=(pow_le_pow_left₀ (zero_le_one.trans ut) (dock_fold r (t r) rp rt) _).trans
    (pow_le_pow_right₀ unit (by omega))
  dsimp only
  intro x y z hx hy hz fz xy gap
  let X:=crop (sites r (t r) x y z) child
  let a:=born J r v
  let y':=sole ((t r) • z)
  let b:Labels S (fun _:Unit=>e):=sole (far F J e (t r) w).2
  let U:=spectator F q
  let read:=upon U h 0 y' b
  let raw:=WilsonThermometerWeakPairExpansion.residual U P h X 0 a ((t r) • z) (far F J e (t r) w).2
  have cut:Injective (beside (sole (0:E4)) y'):= (WilsonThermometerWeakPairDistinct.actual rp rt dp hx hy fz xy gap).2.2.2
  have id:formula F Q X 0 a y' b h q=raw+(read (shadowOld P h X 0 a)-read (Q.packet h X a 0)):=by
    rw [formula,←packet_read F Q X 0 a y' b q h cut]
    exact (sub_add_sub_cancel (Orbits.whole U X a y' b) (read (shadowOld P h X 0 a)) (read (Q.packet h X a 0))).symm
  have near:=bill rt x y z hx hy hz fz xy gap
  have extra:=paid X (WilsonThermometerWeakPairRooms.inner rp hx hy xy) z (by linarith) q
  have main:‖raw‖≤(C*dock r^(k+l))*(2*Z):=near.trans (mul_le_mul (mul_le_mul_of_nonneg_left pk cp)
    (by change t r+Z≤2*Z;linarith) (by change 0≤t r+Z;linarith) (mul_nonneg cp (pow_nonneg (zero_le_one.trans unit) _)))
  have toll:‖read (shadowOld P h X 0 a)-read (Q.packet h X a 0)‖≤(E*dock r^(k+l))*Z:=by
    refine extra.trans ?_
    calc
      _ = (E*dock (t r)^l)*(r^((h:ℝ)+1-(1/4:ℝ))/(t r)^((h:ℝ)+(1/4:ℝ))):=by ring
      _ ≤ _:=mul_le_mul (mul_le_mul_of_nonneg_left pl ep) engine (by positivity) (mul_nonneg ep (pow_nonneg (zero_le_one.trans unit) _))
  change ‖formula F Q X 0 a y' b h q‖≤_
  rw [id]
  calc
    _≤ ‖raw‖+‖read (shadowOld P h X 0 a)-read (Q.packet h X a 0)‖:=norm_add_le _ _
    _≤ (C*dock r^(k+l))*(2*Z)+(E*dock r^(k+l))*Z:=add_le_add main toll
    _= (2*C+E)*dock r^(k+l)*Z:=by ring
    _≤ (2*C+E)*(L₁/(g r)^(2*(k+l)))*Z:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left cap (by linarith)) zn
    _=_:=by dsimp only [Z,t];ring
end YM.Integration.WilsonThermometerWeakPairMovingOPE
end
