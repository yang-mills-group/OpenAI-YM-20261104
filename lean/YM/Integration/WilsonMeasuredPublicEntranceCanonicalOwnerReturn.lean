import YM.Integration.WilsonMeasuredPublicEntranceCanonicalEar
import YM.Integration.WilsonMeasuredPublicEntranceHybridSeats
import YM.Integration.WilsonMeasuredPublicEntranceGrossSeats
import YM.Integration.WilsonSeparatedPrefixCanonicalSplit

/-! The actual signed earlier-law charge on each genuine canonical occupied
owner against a finite mixture of original and trial foregrounds. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCanonicalOwnerReturn
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open QuadraticLocal WilsonThermometerMixedCollarSubpower
open WilsonMeasuredCoefficientTransport WilsonMeasuredPublicEntranceOwnerGas
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedSource
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "S₀" => Marks V
local notation "S₂" => Marks (V×Bool)
local notation "V₂" => V×Bool
local notation "X" => Unit×(V×Bool)


private theorem narrow {T I V:Type}[DecidableEq V]{G:Gauge}{n:Side}{P:BudgetPoint}{o:V → Site n}{R:Marker.Census V}{w:V → ℝ}{lower upper fee:ℝ}{B:ℕ} (L:Lamps T I G P o R) (positive:∀v,0<w v) (order:lower≤upper)
    (paid:L.Paid w B upper fee):L.Paid w B lower fee:=by
  obtain ⟨f,fp,read,bill⟩:=paid.budget
  have toll (mode:R.Mode):0≤Poly.toll w mode:=Finset.prod_nonneg fun v _=>(positive v).le
  refine ⟨f,fp,read,fun x=>budget_mono (bill x) ?_ ?_⟩
  · intro i
    split
    · exact mul_nonneg (mul_nonneg (toll _) (fp i)) (Real.exp_nonneg _)
    · exact le_rfl
  · intro i
    split
    · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (toll _) (fp i))
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right order (Nat.cast_nonneg _))
    · exact le_rfl

theorem original (d:V → ℕ)(simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (nested:WilsonPositionProgramNestedLengths.Nested R.rolls)(cater:Cater (C) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(wage:WilsonReportLampForecast.Ready (A))
    (aperture housing power gross:ℕ)(C₀:ℝ)(posC:0≤C₀):
    ∀ᶠ j:ℕ in atTop,∀N p k (height:j+2≤k+1) (kn:k<N) (l:ℕ)
      (o:V → Site ((C).side (k+1) p))(q:∀i,Coefficient ((C).labels.level (d i)) ((C).side (k+1) p))
      (B D w₀ wY:V → ℝ)(route:∀t,X → Site ((C).side t p))(anchor:X),
    let f:=k+1
    let P:=(C).path.rep N p f
    let H:=(A).clock.hatBeta f
    let a:=WilsonSeparatedPrefixCanonicalMounted.salary R d f p q B
    ∀ {arg I:Type},∀ [Countable I],∀(Y:Lamps arg I G P.p o S₀)(x:arg),
    (∃ (raw:V → Config G ((C).side f p) → ℂ), ∃ h, ∃ F:Config G ((C).side f p) → Poly S₀,
      Served P raw h F o w₀ P.p.supportExponent 1) →
    ((A).params f).supportExponent=100 → (∀v,0<w₀ v) → (∀v,0<wY v) → (∀i,0≤D i) →
    (∀i,(C).ref (d i)≤f) → (∀i,(q i).Format (o i) (C).params P) →
    (∀i,(q i).remBound (o i) P (LocalComparison.forcedDivisor (C) f) (B i)) →
    Y.Paid wY P.p.B (P.p.supportExponent+2) 1 →
    (∀v,(w₀ v)⁻¹≤H^gross) → (∀v,a v+D v≤H^gross) →
    (∀v,(wY v)⁻¹≤Real.exp (C₀*(1+Real.log H)*(scale H)^3)) →
    5≤P.p.B → (∀a b:V,a≠b → P.p.B^2+1 ≤ separation (o a) (o b)) →
    (C).S.a j/(C).S.a f≤H^aperture → l≤housing →
    route f=(o∘Prod.fst) ∘ Prod.snd →
    (∀t,j+1≤t → t<f → route t=((A).clock.op t p).ratio.parent ∘ route (t+1)) →
    (∀i,coverNumber ((C).path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) i}:Support _)≤l) →
    ((A).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
    ∀(trial:Finset V)(owner:V)(d₀:ℕ)(h:Coefficient ((C).labels.level d₀) ((C).side f p)),
    h.Format (o owner) (C).params P → h.remBound (o owner) P (LocalComparison.forcedDivisor (C) f) (D owner) →
    let field:=fun i U=>if i∈trial then (Y.log x U).part ((S₀).fire i)
        else (q i).exponentialEntry (o i) ((C).localSection (d i)) P U
    ∀u:ℕ,(C).ref 0≤u → ∀uj:u≤j,Opened (C) 0 u p → Opened (C) 0 j p →
    ∀s:(S₀).Mode,owner∈s.val →
      ‖reading R (N:=N) (fun U=>account h P U*(∏i∈s.val.erase owner,field i U)) u (uj.trans (by omega))‖≤(H^power)⁻¹:=by
  let n:ℝ:=Fintype.card V
  obtain ⟨j₀,hire⟩:=eventually_atTop.mp (WilsonMeasuredPublicEntranceHybridSeats.original R d simple pace wage)
  obtain ⟨j₁,grossPaid⟩:=eventually_atTop.mp ((RG01.Physical.hats simple (A)).eventually
    (WilsonMeasuredPublicEntranceGrossSeats.original (J:=S₀) gross C₀ posC))
  filter_upwards [WilsonMeasuredPublicEntranceCanonicalEar.original (V:=V) R simple cater bank wage,
    WilsonSeparatedPrefixCanonicalSplit.original (I:=V₂) R simple pace nested aperture 0 housing power (n*n),
    eventually_ge_atTop (max j₀ j₁)] with j ear rate late N p k height kn l o q B D w₀ wY route anchor f P H a arg I count Y x stock fixed fresh yp dn ref form fee prior initial income trialGross wide apart span bounded routeF parent close center trial owner d₀ h shape cost field u opened uj ou oj s includes
  letI:Countable I:=count
  let cash:=fun v=>a v+(wY v)⁻¹
  let w:=WilsonSeparatedPrefixCanonicalWallet.seat w₀ cash D
  let μ:=fun v=>w v^2
  have bn(i):0≤B i:=rem_nonneg (fee i)
  have positive(i):0≤a i:=by
    dsimp [a,WilsonSeparatedPrefixCanonicalMounted.salary]
    exact add_nonneg (mul_nonneg (by positivity) (by unfold Frame.coeffSize;positivity)) (mul_nonneg (sq_nonneg _) (bn i))
  have cashpos(i):0≤cash i:=add_nonneg (positive i) (inv_nonneg.mpr (yp i).le)
  have grade:P.p=(A).budget f:=(R.makes.wilson.represents N p f (by dsimp [f];omega)).vac
  have good:P.p.supportExponent=100:=by rw [grade];exact fixed
  obtain ⟨wp,within,income',each,soft,allPeers⟩:=hire f (by dsimp [f];omega) N p (by dsimp [f];omega)
    fixed o q B D w₀ wY Y x fresh yp dn ref form fee (narrow Y yp (by linarith) prior)
  have mp(i):0<μ i:=sq_pos_of_pos (wp i)
  obtain ⟨c,M,quiet,caps,loc,words,split⟩:=allPeers trial
  have minor(i):μ i*cash i≤1/8:=(Finset.single_le_sum (fun v _=>mul_nonneg (mp v).le (cashpos v)) (Finset.mem_univ i)).trans soft
  have charges(i):Poly.price μ (c i)≤n:= (caps i).trans (mul_le_of_le_one_right (Nat.cast_nonneg _) ((minor i).trans (by norm_num)))
  have receipt:=ear N p k height kn l o w₀ w route anchor owner d₀ h (D owner) field M c (fun v=>μ v*cash v) (fun _=>n)
    stock fresh wp within (by linarith) wide apart shape cost ((each owner).trans (by norm_num)) loc words (by linarith) quiet charges split
    routeF parent close center u opened uj ou oj s includes
  have haircut:=grossPaid f (by dsimp [f];omega) w₀ a D wY fresh positive dn yp initial income trialGross s
  have bigger:Real.exp ((Real.log H)^2/128) ≤ WilsonSeparatedPrefixCanonicalSplit.reserve R f:=by
    apply Real.exp_le_exp.mpr;nlinarith only [sq_nonneg (Real.log H)]
  let weight:=Poly.toll μ s
  let rest:=(WilsonSeparatedPrefixCanonicalTapRate.value R f)⁻¹*WilsonOriginalOccupiedStencil.price (Fintype.card V₂)
  let bundle:=∑t:(S₂).Mode,Poly.toll (w∘Prod.fst (β:=Bool)) t*WilsonSeparatedPrefixCanonicalHeard.roof R (w∘Prod.fst (β:=Bool)) t k j l
  let value:=‖reading R (N:=N) (fun U=>account h P U*∏i∈s.val.erase owner,field i U) u (uj.trans (by omega))‖
  have readingPaid:weight*value≤Real.exp (n*n)*rest*bundle:=by
    simpa only [sum_const,card_univ,nsmul_eq_mul] using receipt
  have reservePaid:=rate k l (by omega) bounded span (w∘Prod.fst (β:=Bool)) (fun i=>wp i.1)
  have reserveP:0≤WilsonSeparatedPrefixCanonicalSplit.reserve R f:=Real.exp_nonneg _
  have wt:0<weight:=Poly.worth mp s
  calc value=weight⁻¹*(weight*value):=by rw [←mul_assoc,inv_mul_cancel₀ wt.ne',one_mul]
       _≤WilsonSeparatedPrefixCanonicalSplit.reserve R f*(Real.exp (n*n)*rest*bundle):=
         mul_le_mul (haircut.trans bigger) readingPaid (mul_nonneg wt.le (norm_nonneg _)) reserveP
       _≤(H^power)⁻¹:=by simpa only [pow_zero,one_mul] using reservePaid

end YM.Integration.WilsonMeasuredPublicEntranceCanonicalOwnerReturn
end
