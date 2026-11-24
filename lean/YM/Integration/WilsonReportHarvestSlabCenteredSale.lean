import YM.Integration.WilsonReportHarvestSlabCenteredHeld
import YM.Integration.WilsonReportHarvestSlabSingletonCost

/-! Center the three original physical clinics by their actual transported
one-point functions on the held Wilson field, all on the same retained action. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabCenteredSale
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open WilsonReportHarvestSlabLabels WilsonAllDateHarvestPropagation WilsonReportHarvestSlabCenteredPush
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} (R:Run G){b m t per:ℕ}(nm:b+1 ≤ m)(mt:m ≤ t)(nt:b+1<t)
    (s:Fin 3→ℕ)(S:(i:Fin 3)→Emblems R.family (s i))(P:(i:Fin 3)→Sight R.family (s i) per)
    (x:(i:Fin 3)→Palette R.family (s i))(o:Fin 3→Site (R.family.side (b+1) per))(f:Fin 3→Body)
local notation "C"=>R.family
local notation "n"=>b+1
local notation "topN"=>t+1
local notation "E"=>fun _:Fin 3=>(1,false)
local notation "q"=>fun z:ManyStem R.family o (b+1)=>f z.val.1
local notation "roster"=>Stock.census (Fin 3)
local notation "A"=>Mine.tree o E
local notation "J"=>Mine.ward o E roster
local notation "Y"=>R.family.path.rep (t+1) per
local notation "color"=>WilsonAllDateHarvestPhysical.columns o E s q S x m (t+1) (b+1)

def center {u:ℕ}(age:u ≤ topN)(i:Fin 3):ℂ:=
  -actualTransport C (N:=topN)
    (Records.clinic C per topN (s i) (Many.point (S i) (x i) m topN) n (o i) (1,false) (f i)) age 1

def Closed (target:ℝ):Prop:=
  let rows:=imprint R.makes A (headings o E q) (plants (m:=m) s P S x) t t.le_succ
  let real:=gust (C).path topN per topN (birth (J n) (Y topN) color) n (nt.le.trans t.le_succ)
  let gate:=WilsonAllDateHarvestEndpointOpening.opening (WilsonMixedTaggedSeparatedBoard.admitted o E roster nm mt)
    (shadow A s (headings o E q) t)
  let inlet:=fun W=>gate (density (Y t) rows (fun _ _=>0) (fun _ _=>0) W)
  ∃L:∀j,Config G ((C).side j per)→Poly (J j),∃route:Replay A s (le_refl n) t L topN,
    L t=inlet ∧
      (∀j (nj:n ≤ j) (jt:j ≤ t) V, ((Y j).eval V)⁻¹ • L j V=actualTransport C (N:=topN) (fun W=>
        ((Y t).eval W)⁻¹ • WilsonReportHarvestEarlierSlab.route route j nj jt (inlet W)) jt V) ∧
      Integrable (fun W=>baseFold o E roster (L n W)) (prior G ((C).side n per)) ∧
      (∀W,(baseFold o E roster (real W)).part (roster).quiet=(baseFold o E roster (L n W)).part (roster).quiet) ∧
      (∀i W,(baseFold o E roster (real W)).part ((roster).fire i)=(baseFold o E roster (L n W)).part ((roster).fire i)) ∧
      ∀u,(C).ref 0 ≤ u → ∀age:u ≤ b,
        ‖value (C).path topN per (age.trans b.le_succ) (fun W=>baseFold o E roster (real W))
          (fun W=>baseFold o E roster (L n W))
          (center (m:=m) R s S x o f ((age.trans b.le_succ).trans (nt.le.trans t.le_succ))) 1‖ ≤ target

theorem original {gain charge mass room:ℝ}(g0:0 ≤ gain)(q1:1 ≤ charge)(m0:0 ≤ mass)(r1:1 ≤ room)
    (size:∀u,(C).ref 0 ≤ u → ∀age:u ≤ b,∀i,‖center (m:=m) R s S x o f
        ((age.trans b.le_succ).trans (nt.le.trans t.le_succ)) i‖ ≤ mass*room)
    (cash:WilsonReportHarvestSlabCenteredHeld.Paid R nm mt nt t.le_succ s S P x o E q
      (gain/(charge*((1+6*mass)*(1+WilsonPositionSeparatedProfileStableReturn.price))*room))):
    Closed R nm mt nt s S P x o f (gain/charge):=by
  obtain ⟨L,route,initial,travel,live,zero,one,spent⟩:=cash
  refine ⟨L,route,initial,travel,live,zero,one,?_⟩
  intro u ref age
  let c:=center (m:=m) R s S x o f ((age.trans b.le_succ).trans (nt.le.trans t.le_succ))
  have sum:∑i,‖c i‖ ≤ 3*(mass*room):=
    (Finset.sum_le_sum (fun i _=>size u ref age i)).trans_eq (by simp)
  have s:1+2*∑i,‖c i‖ ≤ (1+6*mass)*room:=by linarith
  have pos:0 ≤ WilsonPositionSeparatedProfileStableReturn.price:=
    div_nonneg WilsonPositionSeparatedProfileStableStep.shrink_pos.le (sub_pos.mpr WilsonPositionSeparatedProfileStableStep.shrink_lt).le
  let B:=(1+6*mass)*(1+WilsonPositionSeparatedProfileStableReturn.price)
  have b0:0<B:=mul_pos (by linarith) (by linarith)
  have x0:0<room:=zero_lt_one.trans_le r1
  have q0:0<charge:=zero_lt_one.trans_le q1
  have wallet:0 ≤ gain/(charge*B*room):=div_nonneg g0 (mul_nonneg (mul_nonneg q0.le b0.le) x0.le)
  have paid:=(spent u ref age c)
  apply paid.trans
  calc
    _ ≤ ((1+6*mass)*room)*(1+WilsonPositionSeparatedProfileStableReturn.price)*(gain/(charge*B*room)):=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right s (by linarith)) wallet
    _ = (B*room)*(gain/(charge*B*room)):=by dsimp [B];ring
    _ = _:=by field_simp [b0.ne',q0.ne',x0.ne']

end YM.Integration.WilsonReportHarvestSlabCenteredSale
