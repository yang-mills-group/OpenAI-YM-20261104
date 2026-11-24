import YM.Integration.WilsonThermometerWeakPairDetector

/-! One finite roster of true moving detectors, including the vacuum
coordinate if present.  The detector gain survives the horizon decoder with
an arbitrarily preassigned coupling-order margin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairAxes
open Filter Finset Set Spec Table OPE OPE.Log OPE.Orbits OPE.Arboreal OPE.Nesting EveryPhase
open Trace Trace.Pilot RG17 PhysMS PhysMS.Frame GapsContact.Ascent Frontier6 Frontier6.Tale
open PhysicalNext.Repeat.Legato WilsonThermometerWeakMovingCorner WilsonThermometerWeakPairClock
open YM.Integration.WilsonLimitConstruction
open XSpace XSpace.Normalize
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
universe u
local notation "child" => WilsonThermometerWeakPairRooms.near
local notation "sites" => WilsonThermometerWeakPairFork.position
variable {G:Gauge}{R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}{f:Extraction.Order}
    {S:Table R.family.book}(F:Final R.family f S)

theorem refund (simple:G.Simple)(g:ℝ→ℝ)(hg:Coupling G g){C:ℝ}(cp:0≤C)(A o h B:ℕ)(order:A+o+1≤B)
    {ε:ℝ}(ep:0<ε):∀ᶠ r in trail,let t:=scale g B r
      C/(g r)^A*(r/t)^(h+1)≤ε*(g r)^o*(r/t)^h:=by
  have vanishes:Tendsto (fun r=>C*g r) trail (𝓝 0):=by simpa only [mul_zero] using (hg.conforms simple).const_mul C
  filter_upwards [vanishes.eventually (ge_mem_nhds ep),(hg.conforms simple).eventually (ge_mem_nhds zero_lt_one),
    hg.positive,self_mem_nhdsWithin] with r paid top gp rp
  change 0<r at rp
  let t:=scale g B r
  have tp:0<t:=div_pos rp (pow_pos gp _)
  have ratio:r/t=(g r)^B:=by dsimp only [t,scale];field_simp [rp.ne',gp.ne']
  have down:=pow_le_pow_of_le_one gp.le top order
  change _*(r/t)^(h+1)≤_*(r/t)^h
  calc
    _=(C/(g r)^A*(g r)^B)*(r/t)^h:=by rw [pow_succ,ratio];ring
    _≤(C/(g r)^A*(g r)^(A+o+1))*(r/t)^h:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left down (div_nonneg cp (pow_nonneg gp.le _))) (pow_nonneg (div_nonneg rp.le tp.le) _)
    _=((C*g r)*(g r)^o)*(r/t)^h:=by rw [pow_succ,pow_add];field_simp [gp.ne']
    _≤_:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right paid (pow_nonneg gp.le _))
      (pow_nonneg (div_nonneg rp.le tp.le) _)

theorem original {simple:G.Simple}{κ:ℝ}(funded:FundedOriginalProperties.{u} simple κ W)
    (L:Almanac F)(joined:Completed F L)(faculty:Facilities R.family f S)
    (agency:∀U:Ultrafilter (ℕ×ℕ),(U:Filter _)≤f.fuse→MatrixTicket (C:=R.family) S F.sector.derivatives (U:Filter _))
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(book:Foundation F Q)
    (J:ℝ→tower S)(V:Store G)(lead:Leading F J)(g:ℝ→ℝ)(hg:Coupling G g)
    {I:Type}[Fintype I](d:I→↥child→ℕ)(e:I→ℕ)(h:ℕ)(v:∀i j,RG17.Free R.family (d i j))
    (w:∀i,RG17.Free R.family (e i))(view:I→Viewers F){M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃K:ℕ, ∀(o:ℕ)(ε:ℝ),0<ε→∀B:ℕ,K+o+1≤B→∀ᶠ r in trail,let t:=scale g B r
      ∀(i:I)(x y z:E4),‖x‖≤M → ‖y‖≤M → ‖z‖≤M → 2*δ≤‖z‖ → δ≤‖x-y‖ →
        let X:=crop (sites r t x y z) child
        ‖formula F Q X 0 (born J r (v i)) (sole (t • z))
          (sole ((far F J (e i) t (w i)).2):Labels S (fun _:Unit=>e i)) h (view i)‖≤ε*(g r)^o*(r/t)^h:=by
  choose A C cp sells using fun i=>WilsonThermometerWeakPairDetector.original F funded L joined faculty agency Q book J V lead g hg
    (d i) (e i) h (v i) (w i) (view i) mn dp
  refine ⟨∑i,A i,fun o ε ep B paid=>?_⟩
  dsimp only
  apply eventually_all.mpr
  intro i
  have cap:A i≤∑j,A j:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  have order:A i+o+1≤B:=by omega
  filter_upwards [sells i B (by omega),refund simple g hg (cp i) (A i) o h B order ep] with r income bill
  exact fun x y z hx hy hz sep xy=>(income x y z hx hy hz sep xy).trans bill
end YM.Integration.WilsonThermometerWeakPairAxes
end
