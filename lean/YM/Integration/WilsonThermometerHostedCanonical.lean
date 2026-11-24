import YM.Integration.WilsonThermometerHostedPeers
import YM.Integration.WilsonOriginalCompanionPeerRefund
import YM.Integration.WilsonMeasuredCompanionTest
import YM.Integration.WilsonMeasuredCompanionSoft

/-! The full canonical one-mark density on its own Wilson law, tested against the same two measured ordinary peer rows. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerHostedCanonical
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source QuadraticLocal QuadraticLocal.Earn Marker
open Push Ac GridApprox.Nil MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open RG05Readout RG05Readout.Native RG05Readout.Many PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Mallow Motion Bandage Next.Foundations Trace.Physical.GermGraph Pert.Asymptotics
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection
open WilsonMeasuredCompanionFace WilsonMeasuredCompanionWage WilsonThermometerUnitFilingCoarse
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){T I:Type}[Countable I]{d:ℕ}
local notation "CF"=>R.family
local notation "F"=>R.family.labels.level d
local notation "S"=>R.family.localSection d
local notation "A"=>(CF).path.levels
local notation "X"=>Unit×(Fin 3×Bool)
local notation "J"=>Stock.census (Fin 3)
theorem original (simple:G.Simple)(cater:Cater (CF) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(book:WilsonReportLampForecast.Ready (A))(c l q:ℕ):
    ∀ᶠ j:ℕ in atTop,∀N p f (height:j+2≤f) (_:f≤N),
    (f-(j+2):ℕ)≤(c:ℝ)*Real.log (RG16.Lambda (A) f)+2 →
    let P:=(CF).path.rep N p f
    let κ:=LocalComparison.forcedDivisor (CF) f
    ∀(o:Fin 3→Site ((CF).side f p))(v:Fin 3)(h:Coefficient (F) ((CF).side f p))(W:Rep G ((CF).side f p))(_:P.p=W.p)
      (E:Lamps T I G W.p o (J))(w:Fin 3→ℝ)(B δ:ℝ)(route:∀k,(X)→Site ((CF).side k p))(anchor:(X)),
    (∀i,0<w i) → 0≤B → 0<δ → route f=(o ∘ Prod.fst) ∘ Prod.snd →
    (∀k,j+1≤k → k<f → route k=((A).clock.op k p).ratio.parent ∘ route (k+1)) →
    0≤((A).budget f).supportExponent-2 → h.Format (o v) (CF).params P → h.remBound (o v) P κ B →
    (∀a:ℝ,E.Paid (wage v w a) W.p.B W.p.supportExponent 1) →
    (∀i,coverNumber ((CF).path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) i}:Support _)≤l) →
    ((A).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
    ∀u:ℕ,(CF).ref 0≤u → ∀uj:u≤j,Opened (CF) 0 u p → Opened (CF) 0 j p →
    ∀(x:T)(s:(J).Mode),v∈s.val →
    let K:=fun U=>h.density (o v) (S) P U*peers E v s x U
    Integrable K (prior G _) ∧ companions v w s*‖reading R (N:=N) (p:=p) K u (uj.trans (by omega))‖ ≤
      companions v w s*((WilsonThermometerUnitFilingFieldRange.cost G d P.p.threshold*(F).coeffSize h.x+B)*
        (WilsonMeasuredCompanionSoft.expense 1*w v/Poly.toll w s))+
        WilsonOriginalCompanionPeerRefund.tariff*(B+δ)*(regulatorRun (CF) N p f)^q:=by
  filter_upwards [WilsonOriginalCompanionPeerRefund.original (T:=T) (I:=I) R (CF).params (S) simple cater bank book c l q]
    with j refund N p f height fn span P κ o v h W same E w B δ route anchor pos bp dp home path expo fmt bill allWidths close fixed
    u ref uj ou oj x s inside K
  let E₀:=WilsonThermometerHostedPeers.transport same E
  have rooms (a:ℝ):E₀.Paid (wage v w a) P.p.B P.p.supportExponent 1:=by
    rw [show P.p.B=W.p.B from congrArg BudgetPoint.B same,
      show P.p.supportExponent=W.p.supportExponent from congrArg BudgetPoint.supportExponent same]
    exact WilsonThermometerHostedPeers.paid same E (allWidths a)
  have reset:wage v w (w v)=w:=by funext i;by_cases eq:i=v <;> simp [wage,eq]
  have room:E₀.Paid w P.p.B P.p.supportExponent 1:=by simpa only [reset] using rooms (w v)
  have samePeer:peers (W:=P) E₀ v s x=peers (W:=W) E v s x:=funext (WilsonThermometerHostedPeers.peers_eq same E v s x)
  let C₀:=fun U=>h.density (o v) (S) P U*peers (W:=P) E₀ v s x U
  let C₁:=fun U=>(soft h).density (o v) (S) P U*peers (W:=P) E₀ v s x U
  have id:C₀=K:=by dsimp only [C₀,K];rw [samePeer]
  have quiet:P.eval=((CF).path.rep N p f).eval:=rfl
  have law:=((R.T.sticks N p).prices f (Nat.zero_le _) fn).1.valid
  have pay:Integrable C₀ (prior G _):=WilsonMeasuredCompanionTest.integrable E₀ v s x h fmt bill law w pos room P.p.exponent_pos.le le_rfl
  have paysoft:Integrable C₁ (prior G _):=WilsonMeasuredCompanionTest.integrable E₀ v s x (soft h)
    (WilsonPhysicalMarkedDefect.RegularProjection.format h (o v) P (CF).params fmt)
    (WilsonPhysicalMarkedDefect.RegularProjection.bill h (o v) P bill) law w pos room P.p.exponent_pos.le le_rfl
  have softread:=WilsonMeasuredCompanionSoft.heard R d quiet fn v h bill E₀ w pos room P.p.exponent_pos.le le_rfl s x u (uj.trans (by omega))
  obtain ⟨_,hardread⟩:=refund N p f height fn span o v h (fun _=>1) E₀ w B δ route anchor pos bp dp
    home path expo fmt bill (fun _=>by simp) rooms close fixed u ref uj ou oj x s inside
  simp only [one_mul] at hardread
  have diff : (fun U=>(h.density (o v) (S) P U-(soft h).density (o v) (S) P U)*peers E₀ v s x U)=fun U=>C₀ U-C₁ U:=by
    funext U;dsimp only [C₀,C₁];ring
  rw [diff,WilsonMeasuredCompanionTransport.subtract R C₀ C₁ pay paysoft (uj.trans (by omega))] at hardread
  rw [←id];refine ⟨pay,?_⟩
  have fee0:0≤companions v w s:=Finset.prod_nonneg (fun z _=>(pos z).le)
  calc
    _ ≤ companions v w s*(‖reading R (N:=N) (p:=p) C₁ u (uj.trans (by omega))‖+
      ‖reading R (N:=N) (p:=p) C₀ u (uj.trans (by omega))-reading R (N:=N) (p:=p) C₁ u (uj.trans (by omega))‖):=by
        apply mul_le_mul_of_nonneg_left _ fee0
        let y:=reading R (N:=N) (p:=p) C₁ u (uj.trans (by omega))
        let z:=reading R (N:=N) (p:=p) C₀ u (uj.trans (by omega))
        exact (show ‖z‖=‖y+(z-y)‖ by congr 1;abel).le.trans (norm_add_le y (z-y))
    _ ≤ _:=by rw [mul_add];exact add_le_add (mul_le_mul_of_nonneg_left softread fee0) hardread

end YM.Integration.WilsonThermometerHostedCanonical
