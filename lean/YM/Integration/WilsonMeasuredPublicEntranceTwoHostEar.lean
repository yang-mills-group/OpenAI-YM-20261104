import YM.Integration.WilsonMeasuredPublicEntranceCanonicalShares
import YM.Integration.WilsonMeasuredPublicEntranceTrialShares
import YM.Integration.WilsonMeasuredPublicEntranceSignedEar
/-! Both genuine contacted owners are bought at the same earlier Wilson
reading, on their own deposits, before the two physical regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 950000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTwoHostEar
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open QuadraticLocal WilsonThermometerMixedCollarSubpower WilsonMeasuredCoefficientTransport WilsonMeasuredPublicEntranceOwnerGas
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedSource WilsonOriginalOccupiedCorridor QuadraticLocal.Advent
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open WilsonMeasuredPublicEntranceOrderedPeers WilsonMeasuredPublicEntrancePeerShares WilsonMeasuredPublicEntranceOrder
open WilsonMeasuredPublicEntranceSignedEar WilsonMeasuredPublicEntranceCheapOrder
open Pert.Asymptotics
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "S₀" => Marks V
local notation "X" => Unit×(V×Bool)

theorem original (deg:V → ℕ)(simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (nested:WilsonPositionProgramNestedLengths.Nested R.rolls)(cater:Cater (C) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(wage:WilsonReportLampForecast.Ready (A))
    (n apron box power gross:ℕ)(np:0<n)(size:Fintype.card V ≤ n)(C₀ gap ε:ℝ)(cp:0≤C₀)(gp:0≤gap)(ep:0<ε):
    ∀ᶠ j:ℕ in atTop,∀N per k (_height:j+2≤k+1) (_live:k<N) (l:ℕ)
      (o:V → Site ((C).side (k+1) per))(q:Bool → ∀i,Coefficient ((C).labels.level (deg i)) ((C).side (k+1) per))
      (B:Bool → V → ℝ)(w₀ wY:V → ℝ)(route₀:∀t,X → Site ((C).side t per))(anchor:X),
    let f:=k+1
    let b:=j+1
    let P:=(C).path.rep N per f
    let H:=(A).clock.hatBeta f
    let a:=fun z=>WilsonSeparatedPrefixCanonicalMounted.salary R deg f per (q z) (B z)
    ∀(m school:ℕ)(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
      (Q:D.Tab R.rolls)(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀t,Rep G ((C).side t per)),
    Concourse R.alloy R.kit R.T π Γ m N per school Ψ → TicketP R.alloy R.kit D Q →
    ∀{arg I:Type}[Countable I],∀(Y:Lamps arg I G (Ψ f).p o S₀)(x:arg),
    (∃raw:V → Config G ((C).side f per) → ℂ,∃ω,∃F:Config G ((C).side f per) → Poly S₀,
      Served P raw ω F o w₀ P.p.supportExponent 1) →
    ((A).params f).supportExponent=100 → (∀v,0<w₀ v) → (∀v,0<wY v ∧ wY v≤1) → (∀z v,0≤B z v) →
    (∀i,(C).ref (deg i)≤f) → (∀z i,(q z i).Format (o i) (C).params P) →
    (∀z i,(q z i).remBound (o i) P (LocalComparison.forcedDivisor (C) f) (B z i)) →
    Y.Paid wY (Ψ f).p.B ((Ψ f).p.supportExponent+2) 1 →
    (∀v,(w₀ v)⁻¹≤H^gross) → (∀v z t,a z v+B t v≤H^gross) →
    (∀v,(wY v)⁻¹≤Real.exp (C₀*WilsonMeasuredPublicEntranceCropClock.span H)) →
    5≤P.p.B → (∀v v':V,v≠v' → P.p.B^2+1 ≤ separation (o v) (o v')) →
    (C).S.a j/(C).S.a f≤H^apron → l≤box → route₀ f=(o∘Prod.fst) ∘ Prod.snd →
    (∀t,j+1≤t → t<f → route₀ t=((A).clock.op t per).ratio.parent ∘ route₀ (t+1)) →
    (∀v,coverNumber ((C).path.rep N per b).p.B ({route₀ b anchor,route₀ b v}:Support _)≤l) →
    ((A).clock.op j per).ratio.parent (route₀ b anchor)=0 →
    ((f-b:ℕ):ℝ) ≤ gap*(1+Real.log H)^4 → (Ψ b).p.supportExponent ≤ 100 →
    ∀(h:∀v,Coefficient ((C).labels.level (deg v)) ((C).side f per))(M:V → ℝ),
    (∀v,(h v).Format (o v) (C).params (Ψ f)) →
    (∀v,(h v).remBound (o v) (Ψ f) (LocalComparison.forcedDivisor (C) f) (M v)) →
    (∀v,(h v).x=0) → (∀v,(h v).regular=0) →
    (∀v U,‖(h v).density (o v) ((C).localSection (deg v)) (Ψ f) U/((Ψ f).eval U:ℂ)‖ ≤
      Real.exp (C₀*WilsonMeasuredPublicEntranceCropClock.span H)) →
    (∀v,2*(wY v*M v) ≤ Real.exp 1) →
    ∀(u:ℕ),m≤u → (C).ref 0≤u → ∀uj:u≤j,Opened (C) 0 u per → Opened (C) 0 j per →
    WilsonSingleHardRadius.first R simple ≤ u →
    ∀(Z:Support ((C).side b per))(center:Site ((C).side b per))(L:ℕ),center∈Z → coverNumber (Ψ b).p.B Z ≤ L →
    ∀s:(S₀).Mode,(∀v∈s.val,sites R o (by dsimp [b,f];omega : b≤f) v∈Z) →
    let soft:=fun z=>incidence (N:=N) R deg o (q z)
    let trial:=fun v U=>(Y.log x U).part ((S₀).fire v)
    let hard:=WilsonMeasuredPublicEntranceFlatShares.contact R s.val (soft false) trial (soft true)
      (fun v=>account (q false v) P) (fun v=>account (h v) (Ψ f)) (fun v=>account (q true v) P)
    let ear:=fun F=>reading R (N:=N) F u (uj.trans (show j≤f by omega))
    let amount:=((shares s.val.toList).length:ℝ)*((H^power)⁻¹+
      ((H^power)⁻¹+ε*(regulatorRun (C) N per f)^power*WilsonMeasuredPublicEntranceCropRoof.roof s L)+(H^power)⁻¹)
    Integrable hard (prior G _) ∧ ‖ear hard‖≤amount ∧
      ∀(smooth δ:V → ℝ),(∀v U,‖soft false v U‖ ≤ smooth v) → (∀v U,‖soft true v U‖ ≤ δ v) →
      (∀v U,(P.eval U:ℂ)*(trial v U-(soft false v U-soft true v U))=
        account (q false v) P U-account (h v) (Ψ f) U-account (q true v) P U) →
      let xprod:=weighted (N:=N) R (factors (soft false) s.val.toList)
      let yprod:=weighted (N:=N) R (factors trial s.val.toList)
      ear xprod-ear yprod=ear (weighted (N:=N) R (cheap R (soft false) (soft true) s.val.toList))-ear hard ∧
        ‖ear xprod-ear yprod‖≤route smooth (fun v=>smooth v+δ v) δ s.val.toList+amount:=by
  obtain ⟨start,trial⟩:=WilsonMeasuredPublicEntranceTrialShares.original R simple S₀ deg pace wage
    n gross power np size C₀ gap ε cp gp ep
  obtain ⟨t₀,trialPaid⟩:=eventually_atTop.mp trial
  filter_upwards [WilsonMeasuredPublicEntranceCanonicalShares.original R deg simple pace nested cater bank wage
    apron box power gross C₀ cp,eventually_ge_atTop t₀,eventually_ge_atTop start] with j original t₁ s₁
  intro N per k high live l o q B w₀ wY path anchor f b P H a m school way D Q π Γ Ψ course ticket arg I inst
    Y x filed sup wp yp bp ref fit remn lamps orig both toll big apart ap rooms top lineage paired home window oldp
    h M hf hm hx hr thermal hprice u mu ref₀ uj first last early Z center L present covered s supported soft y hard ear amount
  have fn:f≤N:=live
  have bf:b<f:=high
  have mf:m≤f:=by dsimp [f];omega
  have equal:(Ψ f).p=P.p:=(WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course mf fn).1.symm
  have tk:t₀≤k:=by dsimp [f,b] at *;omega
  have loss (z v):a z v≤H^gross:=(le_add_of_nonneg_right (bp z v)).trans (both v z z)
  have payP:=original N per k high live l o q B w₀ wY path anchor (Ψ f) equal Y x filed sup wp
    (fun v=>(yp v).1) bp ref fit remn lamps orig both (by simpa only [WilsonMeasuredPublicEntranceCropClock.span,mul_assoc] using toll)
    big apart ap rooms top lineage paired home u ref₀ uj first last s
  have payY:=trialPaid k tk N per m school b fn bf (s₁.trans (Nat.le_succ _)) way D Q π Γ Ψ course ticket
    o q wY B arg I Y x sup yp bp ref fit remn loss toll lamps window oldp h M hf hm hx hr thermal hprice
    u u mu le_rfl (uj.trans (Nat.le_succ _)) early Z center L present covered s supported
  have α:0≤(Ψ f).p.supportExponent+2:=by
    rw [equal,show P.p.supportExponent=100 from (R.makes.wilson.represents N per f fn).vac ▸ sup];norm_num
  have legal:=QuadraticLocal.Advent.later R π Γ Ψ course mf fn
  have softPaid (z:Bool)(v:V):BoundedAt (C) (soft z v):=WilsonMeasuredPublicEntrancePeerTests.canonical R P o v (q z v) (fit z v) (remn z v)
  have yp₀(v:V):BoundedAt (C) (y v):=(WilsonMeasuredPublicEntrancePeerTests.trial R (Ψ f) o v Y x wY (fun j=>(yp j).1) α lamps).1
  have aq (z:Bool)(v:V):BoundedAt (C) (account (q z v) P):=
    WilsonMeasuredPublicEntranceOwnerIntegrable.account_at R fn (q z v) (o v) (fit z v) (remn z v)
  have ah(v:V):BoundedAt (C) (account (h v) (Ψ f)):=
    WilsonMeasuredPublicEntrancePeerTests.hard R (Ψ f) o v (h v) (hf v) (hm v) legal.truep.valid (hx v) (hr v)
  have charged:=WilsonMeasuredPublicEntranceFlatShares.original R s.val (soft false) y (soft true)
    (uj.trans (show j≤f by omega)) _ _ _ (softPaid false) yp₀ (softPaid true) (aq false) ah (aq true) _ _ _
    (fun a h₀=>⟨payP a h₀ false,payY a h₀,payP a h₀ true⟩)
  refine ⟨charged.1,charged.2,?_⟩
  intro smooth δ px pe sheet
  exact WilsonMeasuredPublicEntranceSignedEar.original R fn _ s.val (soft false) y (soft true) _ _ _
    (softPaid false) yp₀ (softPaid true) sheet smooth δ px pe amount charged.1 charged.2

end YM.Integration.WilsonMeasuredPublicEntranceTwoHostEar
end
