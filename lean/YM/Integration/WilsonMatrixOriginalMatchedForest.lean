import YM.Integration.WilsonMatrixOriginalMatchedSites
import YM.Integration.WilsonMatrixOriginalReportingMargin
import YM.Integration.WilsonMatrixTicketLanesRetainedFare
import YM.MatchingR2.Top.Weather

/-! The enrolled two-point test and its two one-point terms on the actual finite one-step forest. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalMatchedForest
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Tree Precision RG17 Source Marker Extraction Spec
open Table Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open RGComparison.Core16 RGComparison.Core16.Spool FVA2.CityHistory Pert.Asymptotics
open WilsonMatrixTicketLanesReportedOneBlock WilsonMatrixTicketLanesRegulatorCoupon
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionCalibratedColumn WilsonMatrixOriginalEarlierPanel
open private volume_bill from YM.Integration.WilsonInvariantActionPromotedPair
open private coupling_bound from YM.Integration.WilsonInvariantActionPromotedRegular
open scoped Classical BigOperators Topology

variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S)
    (J:ℝ→tower S) (Z:WilsonPrescription G) {H:(Bel R.family.book).Hierarchy}
    (L:Layout F) {U:Filter (ℕ×ℕ)}
local notation "β" => R.family.path.levels.clock.hatBeta

def Signed (e:ℕ) (g:ℝ→ℝ) (a b:ℝ→R.family.label 4) (φ:Test 2) : Prop :=
  ∀ (n:ℕ) (pick:Fin n→Fin 2) (q cap:ℕ) (ε:ℝ),0<ε→∀ᶠr in trail,let m:=L.level r
  ∀hr:0<r,∀ᶠz:ℕ×ℕ in U,∃(old:ℕ)(stepDate:m=old+1)(live:m<z.1),∃ large:Bid.Larger (G:=G) (step R z.2 stepDate),
  ∀(T:Forest (step R z.2 stepDate).ratio) (u:Pins G (R.family.side old z.2))
    (tag:(step R z.2 stepDate).Choices) (v:(Descent.nil (top:=R.family.side m z.2)).Tags),
    (∀j,‖u j‖≤(cap:ℝ)+1) →
    let top:=fun i:Fin n=>atRef L 4 r z ((Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (a r) (fun _=>b r)) (pick i))
    let d:=fun _:Fin n=>4
    let order:=q+1+2*((∑_i:Fin n,e)+1)
    let seat:=fun (x:Fin 2→Site (R.family.side z.1 z.2)) (i:Fin n)=>(R.family.S.toDepth live.le z.2).parent (x (pick i))
    let c:=fun x=>WilsonExternalMeshMass.charge R.family (dilate hr φ) x
    ‖(∑x,c x*fresh R d z.1 z.2 top stepDate u (seat x))-
      (∑x,c x*forecast R (k:=m) d z.1 z.2 top
        (WilsonMatrixTicketLanesRetainedFare.reading R (N:=z.1) d order stepDate large T u (seat x) tag v))‖≤ε*(g r)^q

private theorem at_step {m b p:ℕ} (hm:m=b+1)
    (large:Bid.Larger (G:=G) (R.family.path.levels.clock.op b p)):
    Bid.Larger (G:=G) (step R p hm):=by subst m;exact large

theorem filed (simple:G.Simple) (fund:WilsonMatrixTicketLanesReportedPrepaid.Paid G R.kit) (pace:WilsonWindowReportingPace.Slow R.kit)
    {B:ℕ} (hp:0<B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    (chosen:U≤L.lens) {g:ℝ→ℝ} (coupling:Coupling G g) (e:ℕ)
    (a b:ℝ→R.family.label 4) (φ:Test 2)
    (cover:∀ᶠr in trail,∀i:Fin 2,∀N p,L.level r≤N→
      quota R.family 4 (L.level r) N p (atRef L 4 r (N,p) ((Fin.cons (α:=fun _:Fin 2=>R.family.label 4)
        (a r) (fun _=>b r)) i))≤R.family.S.a (L.level r)^4*β (L.level r)^e):
    Signed (U:=U) F L e g a b φ :=by
  intro n pick q cap ε ep
  let d:=fun _:Fin n=>4
  let M:ℝ:=(∫x,‖φ x‖)+1
  let C:=M*2^(q+1)
  have mp:0≤M:=by dsimp only [M];positivity
  have grow:Tendsto L.level trail atTop:=by rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple B hp
  have prev:Tendsto (fun r=>L.level r-1) trail atTop:=tendsto_atTop.2 fun k=>
    (grow.eventually_ge_atTop (k+1)).mono fun r h=>by change k≤L.level r-1;omega
  have sale:=prev.eventually (WilsonMatrixTicketLanesRegulatorCoupon.billed R F L simple fund d (fun _=>e)
    (q+1) cap 1 one_pos)
  have plenty:=prev.eventually (MatchingR2.Top.step_shape R.family.path)
  have warm:=(WilsonPhysicalCutoffCurrency.temperature R simple pace hp g coupling).eventually
    (lt_mem_nhds (show (1/2:ℝ)<1 by norm_num))
  have small:Tendsto (fun r=>C*g r) trail (𝓝 0):=by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=C)).mul (coupling.conforms simple)
  filter_upwards [cover,sale,plenty,grow.eventually_ge_atTop (max 1 (R.family.ref 4)),warm,
    coupling.positive,small.eventually (gt_mem_nhds ep)] with r wages spent wide age heat gp loss
  intro m hr
  let old:=m-1
  have st:m=old+1:=by have h:= (le_max_left 1 (R.family.ref 4)).trans age;dsimp only [old,m] at *;omega
  have live:∀ᶠz:ℕ×ℕ in f.fuse,m<z.1:=by
    change ∀ᶠ_:ℕ in atTop,∀ᶠ j:ℕ in atTop,m<f.mesh j
    exact .of_forall fun _=>f.mesh.cofinal.eventually_gt_atTop m
  let ψ:=dilate hr φ
  have total:=(WilsonExternalMeshMass.funded R.family f ψ ψ.continuous ψ.hasCompactSupport
    (show (0:ℝ)<1 by norm_num)).filter_mono (chosen.trans L.certified)
  filter_upwards [live.filter_mono (chosen.trans L.certified),total] with z later budget
  let large:=at_step (p:=z.2) st (wide z.2)
  refine ⟨old,st,later,large,?_⟩
  intro T u tag v bounded
  let top:=fun i:Fin n=>atRef L 4 r z ((Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (a r) (fun _=>b r)) (pick i))
  let ord:=q+1+2*((∑_i:Fin n,e)+1)
  let seat:=fun (x:Fin 2→Site (R.family.side z.1 z.2)) (i:Fin n)=>(R.family.S.toDepth later.le z.2).parent (x (pick i))
  let c:=fun x=>WilsonExternalMeshMass.charge R.family (N:=z.1) (p:=z.2) ψ x
  let actual x:=fresh R d z.1 z.2 top st u (seat x)
  let bill x:=forecast R (k:=m) d z.1 z.2 top
    (WilsonMatrixTicketLanesRetainedFare.reading R (N:=z.1) d ord st large T u (seat x) tag v)
  have unit (i:Fin n):(R.family.S.a m^(d i))⁻¹*quota R.family (d i) m z.1 z.2 (top i)≤β m^e*1:=by
    rw [mul_one,inv_mul_le_iff₀ (pow_pos (R.family.S.a_pos m) _)]
    exact wages (pick i) z.1 z.2 later.le
  have paid:1/2<β m*(g r)^2:=by simpa only [m,level] using heat
  have cold:regulatorRun R.family z.1 z.2 m≤2*g r:=coupling_bound R simple le_rfl later.le gp paid
  let fee:=(2*g r)^(q+1)
  have nonnegative:0≤fee:=by dsimp only [fee];positivity
  have each (x):‖actual x-bill x‖≤fee:=by
    have quoted:=spent m z.1 z.2 st later.le (fun _=>(le_max_right 1 (R.family.ref 4)).trans age)
      top (fun _=>1) unit (fun _=>zero_le_one) large T u (seat x) tag v bounded
    rw [WilsonMatrixTicketLanesRetainedFare.identified R] at quoted
    simp only [Finset.prod_const_one, mul_one, one_mul] at quoted
    exact quoted.trans (pow_le_pow_left₀ (by unfold regulatorRun;positivity) cold _)
  have amount:∑x,‖c x‖≤M:=by simpa only [c,M,ψ,volume_bill] using budget
  change ‖(∑x,c x*actual x)-(∑x,c x*bill x)‖≤ε*(g r)^q
  calc
    _=‖∑x,c x*(actual x-bill x)‖:=by simp only [mul_sub,sum_sub_distrib]
    _≤∑x,‖c x*(actual x-bill x)‖:=norm_sum_le _ _
    _≤∑x,‖c x‖*fee:=sum_le_sum fun x _=>by rw [norm_mul];exact mul_le_mul_of_nonneg_left (each x) (norm_nonneg _)
    _=(∑x,‖c x‖)*fee:=(sum_mul ..).symm
    _≤M*fee:=mul_le_mul_of_nonneg_right amount nonnegative
    _=(C*g r)*(g r)^q:=by dsimp only [C,fee];rw [mul_pow,pow_succ (g r)];ring
    _≤ε*(g r)^q:=mul_le_mul_of_nonneg_right loss.le (pow_nonneg gp.le q)

end YM.Integration.WilsonMatrixOriginalMatchedForest
