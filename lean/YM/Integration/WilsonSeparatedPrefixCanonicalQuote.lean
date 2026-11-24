import YM.Integration.WilsonSeparatedPrefixCanonicalMounted
import YM.Integration.WilsonSeparatedPrefixCanonicalTapRate

/-! The true finite original P report and full booked singleton columns at
one separated cut. The two flat ears use this same sale, including the unit. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalQuote
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedSource
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "S₀" => Marks V
local notation "S₂" => Marks (V×Bool)
local notation "V₂" => V×Bool
local notation "X" => Unit×(V×Bool)

theorem original (d:V → ℕ)(simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (cater:Cater (C) R.doors)(bank:WilsonThermometerClusterProjectionBudget.Ready (A))
    (wage:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ j:ℕ in atTop,∀N p k (height:j+2≤k+1) (kn:k<N) (l:ℕ)
      (o:V → Site ((C).side (k+1) p))(w₀ B:V → ℝ)(route:∀t,X → Site ((C).side t p))(anchor:X)
      (q:∀v,Coefficient ((C).labels.level (d v)) ((C).side (k+1) p))(F:Config G ((C).side (k+1) p) → Poly S₀),
    let P:=(C).path.rep N p (k+1)
    let a:=WilsonSeparatedPrefixCanonicalMounted.salary R d (k+1) p q B
    let w:=WilsonSeparatedPrefixCanonicalWallet.seat w₀ a B
    let W:=w ∘ Prod.fst (β:=Bool)
    let φ:=fun v=> (q v).exponentialEntry (o v) ((C).localSection (d v)) P
    let h:=fun v=>profile P.activities (q v).forced
    ((A).params (k+1)).supportExponent=100 → (∀v,0<w₀ v) → (∀v,(C).ref (d v)≤k+1) →
    (∀v,(q v).Format (o v) (C).params P) →
    (∀v,(q v).remBound (o v) P (LocalComparison.forcedDivisor (C) (k+1)) (B v)) →
    Served P φ h F o w₀ P.p.supportExponent 1 → 5≤P.p.B →
    (∀u v:V,u≠v → P.p.B^2+1≤ separation (o u) (o v)) →
    route (k+1)=(o∘Prod.fst) ∘ Prod.snd →
    (∀t,j+1≤t → t<k+1 → route t=((A).clock.op t p).ratio.parent ∘ route (t+1)) →
    (∀i,coverNumber ((C).path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) i}:Support _)≤l) →
    ((A).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
    ∀u:ℕ,(C).ref 0≤u → ∀uj:u≤j,Opened (C) 0 u p → Opened (C) 0 j p → ∀s:(S₀).Mode,
    Poly.toll (fun i=>w i^2) s*
      ‖WilsonThermometerUnitFilingCoarse.reading R (N:=N) (fun U=>(F U).part s) u (uj.trans (by omega))-
       WilsonThermometerUnitFilingCoarse.reading R (N:=N) (fun U=>(P.eval U:ℂ)*(∏v∈s.val,φ v U)) u (uj.trans (by omega))‖≤
      Real.exp (Fintype.card V:ℝ)*((WilsonSeparatedPrefixCanonicalTapRate.value R (k+1))⁻¹*
        WilsonOriginalOccupiedStencil.price (Fintype.card V₂))*
      (∑t:(S₂).Mode,Poly.toll W t*WilsonSeparatedPrefixCanonicalHeard.roof R W t k j l):=by
  obtain ⟨j₀,mounted⟩:=eventually_atTop.mp (WilsonSeparatedPrefixCanonicalMounted.original R d simple pace wage)
  obtain ⟨j₁,taps⟩:=eventually_atTop.mp (WilsonSeparatedPrefixCanonicalTapRate.original R simple (Fintype.card V₂))
  filter_upwards [WilsonSeparatedPrefixCanonicalWithdrawal.original (V:=V) R simple cater bank wage,
    eventually_ge_atTop (max j₀ j₁),(RG01.Physical.hats simple (A)).eventually_ge_atTop 1] with j receiver late warm N p k height kn l o w₀ B route anchor q F P a w W φ h fixed positive ref fit salary stock size apart course parent housing zero
  let μ:=fun v=>w v^2
  let m:=fun v=>μ v*a v
  let cap:=fun v=>(Fintype.card V:ℝ)*m v
  let κ:=LocalComparison.forcedDivisor (C) (k+1)
  let r:=fun v=>μ v*(κ*B v)
  let E:=WilsonSeparatedPrefixCanonicalTapRate.value R (k+1)
  let T:ℂ:=E
  have pos:0<E:=Real.exp_pos _
  have large:1≤E:=Real.one_le_exp (div_nonneg (sq_nonneg _) (by norm_num))
  have low:‖T⁻¹‖=E⁻¹:=by rw [norm_inv];congr 1;exact Complex.norm_real _ |>.trans (Real.norm_of_nonneg pos.le)
  have small:‖T⁻¹‖≤1:=by rw [low];exact inv_le_one_of_one_le₀ large
  have inverse:T*T⁻¹=1:=mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr pos.ne')
  obtain ⟨wp,within,_,_,soft,hard,c,M,quiet,constants,loc,fees,split,flag,keys⟩:=
    mounted (k+1) (by omega) N p (by omega) fixed o q w₀ B positive ref fit salary
  have sumCap:(∑v,cap v)≤(Fintype.card V:ℝ):=by
    change (∑v,(Fintype.card V:ℝ)*m v)≤_
    rw [←Finset.mul_sum]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (soft.trans (by norm_num))
  have paid(z:ℂ)(hz:z∈nodes (Fintype.card V₂) T):
      4*‖z‖≤Real.exp ((P.p.B/8:ℕ):ℝ) ∧ (∑v,‖z‖*r v)+1/4≤1:=by
    have scheduled:=taps (k+1) (by omega) z hz
    have grade:P.p=(A).budget (k+1):=(R.makes.wilson.represents N p (k+1) (by omega)).vac
    refine ⟨grade.symm ▸ scheduled.1,?_⟩
    have identity:(∑v,‖z‖*r v)=(‖z‖*κ)*(∑v,μ v*B v):=by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _=>by dsimp [r];ring)
    rw [identity]
    have cash:=mul_le_mul scheduled.2 hard (sum_nonneg (fun v _=>mul_nonneg (pow_nonneg (wp v).le _) (rem_nonneg (salary v)))) zero_le_one
    linarith
  have base:P.p=(A).budget (k+1):=(R.makes.wilson.represents N p (k+1) (by omega)).vac
  have stocked:Served P φ h F o w₀ ((((A).budget (k+1)).supportExponent-1)+1) 1:=by
    simpa only [←base,sub_add_cancel] using stock
  have backed:=receiver N p k height kn l o w₀ w route anchor φ h F M c m r cap T T⁻¹ stocked positive wp within size apart loc flag
    (by simpa only [←base] using fees) (by simpa only [←base] using keys) (by linarith) quiet constants split inverse small paid
    ⟨_,_,(R.makes.wilson.represents N p (k+1) (by omega)).good.labels⟩ course parent housing zero
  intro u hu uj ou oj s
  have out:=backed u hu uj ou oj s
  rw [low] at out
  refine out.trans ?_
  have debt:0≤WilsonOriginalOccupiedStencil.price (Fintype.card V₂):=Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>norm_nonneg _))
  have ray:0≤E⁻¹*WilsonOriginalOccupiedStencil.price (Fintype.card V₂):=mul_nonneg (inv_nonneg.mpr pos.le) debt
  have toll(t:(S₂).Mode):0≤Poly.toll W t*WilsonSeparatedPrefixCanonicalHeard.roof R W t k j l:=by
    unfold WilsonSeparatedPrefixCanonicalHeard.roof
    have wpos:∀i:V₂,0<W i:=fun i=>wp i.1
    have posT:=Poly.worth wpos t
    have col:0≤((A).params j).columns:=zero_le_one.trans ((A).params j).columns_ge
    have hp:0≤(A).clock.hatBeta j:=zero_le_one.trans warm
    have hq:0≤(A).clock.hatBeta (k+1):=hp.trans (WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos simple).le (by omega))
    positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr sumCap) ray) (sum_nonneg (fun t _=>toll t))

end YM.Integration.WilsonSeparatedPrefixCanonicalQuote
