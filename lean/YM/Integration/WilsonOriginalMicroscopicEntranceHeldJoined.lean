import YM.Integration.WilsonOriginalMicroscopicEntranceHeldTwoHosts
import YM.Integration.WilsonMeasuredPublicEntranceJoinedEar

/-! Nonconstant hearing on the original fitted X,E and the joined trial on their own contemporaneous inventories. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldJoined
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

open RG05Readout RG05Readout.Address WilsonThermometerUnitFilingFieldRange WilsonReflectedFundedHearing WilsonReflectedPublicGuardedColumns
open WilsonReflectedPublicTrialRoster WilsonMeasuredPublicEntranceJoinedWage
open WilsonSeparatedPrefixCanonicalClearConvolution (readingAt)
theorem original (deg:V → ℕ)(simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (nested:WilsonPositionProgramNestedLengths.Nested R.rolls)(cater:Cater (C) R.doors)
    (wage:WilsonReportLampForecast.Ready (A))
    (n apron power gross:ℕ)(np:0<n)(size:Fintype.card V ≤ n)(C₀ gap ε:ℝ)(cp:0≤C₀)(gp:0≤gap)(ep:0<ε):
    ∀ᶠ j:ℕ in atTop,∀N per k (height:j≤k+1) (_live:k<N)
      (K:ℕ)(fk:k+1≤K)(kn:K≤N)(arms:∀i,Arm R (deg i) N per (k+1) K)(q₀:V → ℕ)
      (dose:V → ℂ)(rows:V → Three G ((C).side (k+1) per))(X₀ E₀:∀i,Coefficient ((C).labels.level (deg i)) ((C).side (k+1) per))
      (w₀ wY:V → ℝ)(route₀:∀t,X → Site ((C).side t per)),
    let f:=k+1
    let b:=j
    let P:=(C).path.rep N per f
    let H:=(A).clock.hatBeta f
    let o:=fun v=>(arms v).o
    let q:=printed R deg X₀ E₀
    (∀i,let Ω:=orbitCost ((C).labels.level (deg i))
      let w:=WilsonReflectedPublicMountedInvoice.wage R f
      WilsonReflectedPublicGuardedColumns.Joined R (arms i) fk kn (dose i) (rows i) w (Ω*(1+w))
        ((2+Ω)*(H^(q₀ i+deg i))⁻¹) (X₀ i) (E₀ i)) →
    ∀(m school:ℕ)(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
      (Q:D.Tab R.rolls)(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀t,Rep G ((C).side t per)),
    Concourse R.alloy R.kit R.T π Γ m N per school Ψ → TicketP R.alloy R.kit D Q →
    ∀{arg I:Type}[Countable I],∀(Y:Lamps arg I G (Ψ f).p o S₀)(x:arg),
    (∃raw:V → Config G ((C).side f per) → ℂ,∃ω,∃F:Config G ((C).side f per) → Poly S₀,
      Served P raw ω F o w₀ P.p.supportExponent 1) →
    ((A).params f).supportExponent=100 → (∀v,0<w₀ v) → (∀v,0<wY v ∧ wY v≤1) →
    (∀i,(C).ref (deg i)≤f) →
    Y.Paid wY (Ψ f).p.B ((Ψ f).p.supportExponent+2) 1 →
    (∀v,(w₀ v)⁻¹≤H^gross) →
    (∀v,(wY v)⁻¹≤Real.exp (C₀*WilsonMeasuredPublicEntranceCropClock.span H)) →
    5≤P.p.B → (∀v v':V,v≠v' → P.p.B^2+1 ≤ separation (o v) (o v')) →
    (C).S.a j/(C).S.a f≤H^apron → route₀ f=(o∘Prod.fst) ∘ Prod.snd →
    (∀t,j≤t → t<f → route₀ t=((A).clock.op t per).ratio.parent ∘ route₀ (t+1)) →
    2≤((A).budget j).supportExponent →
    ((f-b:ℕ):ℝ) ≤ gap*(1+Real.log H)^4 →
    ∀(h:∀v,Coefficient ((C).labels.level (deg v)) ((C).side f per))(M:V → ℝ),
    (∀v,(h v).Format (o v) (C).params (Ψ f)) →
    (∀v,(h v).remBound (o v) (Ψ f) (LocalComparison.forcedDivisor (C) f) (M v)) →
    (∀v,(h v).x=0) → (∀v,(h v).regular=0) →
    (∀v U,‖(h v).density (o v) ((C).localSection (deg v)) (Ψ f) U/((Ψ f).eval U:ℂ)‖ ≤
      Real.exp (C₀*WilsonMeasuredPublicEntranceCropClock.span H)) →
    (∀v,2*(wY v*M v) ≤ Real.exp 1) →
    (∀i U,(h i).density (o i) ((C).localSection (deg i)) (Ψ f) U/((Ψ f).eval U:ℂ)=
      actualTransport (C) (N:=N) (WilsonOriginalAlternativeTrialSource.arm R deg N per K
        (root R deg arms fk) (weight R deg arms) (factor R K deg dose) i) fk U-
          (Y.log x U).part ((S₀).fire i)) →
    m≤b → ∀endpoint:Config G ((C).side b per),flags ((C).path.rep N per b).p.threshold endpoint=∅ →
    ∀s:(S₀).Mode,
    let soft:=fun z=>incidence (N:=N) R deg o (q z)
    let trial:=fun v U=>(Y.log x U).part ((S₀).fire v)
    let hard:=WilsonMeasuredPublicEntranceFlatShares.contact R s.val (soft false) trial (soft true)
      (fun v=>account (q false v) P) (fun v=>account (h v) (Ψ f)) (fun v=>account (q true v) P)
    let ear:=fun F=>readingAt R (N:=N) F height endpoint
    let amount:=((shares s.val.toList).length:ℝ)*((H^power)⁻¹+
      ((H^power)⁻¹+ε*(regulatorRun (C) N per f)^power*(Multi.shards (S₀) s).card)+(H^power)⁻¹)
    Integrable hard (prior G _) ∧ ‖ear hard‖≤amount ∧
      let smooth:=fun i=>WilsonReflectedPublicCommonSoftLaw.gross R (deg i) f
      let δ:=fun i=>WilsonReflectedPublicCommonSoftLaw.net R (deg i) f (q₀ i)
      let xprod:=weighted (N:=N) R (factors (soft false) s.val.toList)
      let yprod:=weighted (N:=N) R (factors trial s.val.toList)
      ear xprod-ear yprod=ear (weighted (N:=N) R (cheap R (soft false) (soft true) s.val.toList))-ear hard ∧
        ‖ear xprod-ear yprod‖≤route smooth (fun v=>smooth v+δ v) δ s.val.toList+amount:=by
  obtain ⟨start,earned⟩:=eventually_atTop.mp (WilsonMeasuredPublicEntranceJoinedWage.original R deg simple)
  filter_upwards [WilsonOriginalMicroscopicEntranceHeldTwoHosts.original R deg simple pace nested cater wage
    n apron power (max gross 9) np size C₀ gap ε cp gp ep,eventually_ge_atTop start] with j sale gate
  intro N per k high live K fk kn arms q₀ dose rows X₀ E₀ w₀ wY path f b P H o q owned
    m school way D Q π Γ Ψ course ticket arg I inst Y x filed sup wp yp ref lamps orig toll big apart ap
    head line cap window h M hf hm hx hr thermal hprice source mb endpoint clear s
    soft trial hard ear amount
  have mf:m≤f:=mb.trans high
  have win:=earned f (gate.trans (by dsimp [f]; omega)) per K N fk kn arms q₀ dose rows X₀ E₀ owned
  obtain ⟨positive,fit,remn,paid,price⟩:=win
  have oneH:1≤H:=((A).fits.delayed f).le
  have raw(v): (w₀ v)⁻¹≤H^(max gross 9):=(orig v).trans (pow_le_pow_right₀ oneH (le_max_left ..))
  have both(v z t):WilsonSeparatedPrefixCanonicalMounted.salary R deg f per (q z) (money R deg f q₀ z) v+
      money R deg f q₀ t v≤H^(max gross 9):=(paid v z t).trans (pow_le_pow_right₀ oneH (le_max_right ..))
  have fixed:(Ψ f).eval=P.eval:=(course.1.walk f mf (show f≤N from live)).view
  have equal (i:V)(U:Config G ((C).side f per)):
      (P.eval U:ℂ)*(trial i U-(soft false i U-soft true i U))=
        account (q false i) P U-account (h i) (Ψ f) U-account (q true i) P U:=by
    apply WilsonReflectedPublicTrialExchange.one R deg arms X₀ E₀ h (Ψ f) trial i U ⟨hx i,hr i⟩
    apply WilsonReflectedPublicTrialExchange.sheet R deg arms fk kn dose rows
      (fun _=>WilsonReflectedPublicMountedInvoice.wage R f)
      (fun i=>orbitCost ((C).labels.level (deg i))*(1+WilsonReflectedPublicMountedInvoice.wage R f))
      (fun i=>(2+orbitCost ((C).labels.level (deg i)))*(H^(q₀ i+deg i))⁻¹) X₀ E₀ h (Ψ f) trial fixed i
      (owned i) U (source i U)
  have exactEar:=sale N per k high live o q (money R deg f q₀) w₀ wY path
    m school way D Q π Γ Ψ course ticket Y x filed sup wp yp positive ref fit remn lamps raw both toll big apart
    ap head line cap window h M hf hm hx hr thermal hprice mb endpoint clear s
  refine ⟨exactEar.1,exactEar.2.1,?_⟩
  intro smooth δ
  exact exactEar.2.2 smooth δ (fun i U=>(price i U).1) (fun i U=>(price i U).2) equal


end YM.Integration.WilsonOriginalMicroscopicEntranceHeldJoined
end
