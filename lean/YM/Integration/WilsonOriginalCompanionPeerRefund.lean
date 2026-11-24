import YM.Integration.WilsonOriginalCompanionSignedTwin
import YM.Integration.WilsonOriginalCompanionCorridorCurrency
import YM.Integration.WilsonMeasuredCompanionWage

/-! Only the original ordinary peer tolls remain in the physically normalized signed hard hearing. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionPeerRefund
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source QuadraticLocal QuadraticLocal.Earn Marker
open Push Ac GridApprox.Nil MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open RG05Readout RG05Readout.Native RG05Readout.Many PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Mallow Motion Bandage Next.Foundations Trace.Physical.GermGraph Pert.Asymptotics
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection
open WilsonMeasuredCompanionFace WilsonMeasuredCompanionWage WilsonThermometerUnitFilingCoarse
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){T I:Type}[Countable I]{d:ℕ}{F:Frame G d}(hol:Hol G)(sectionData:SectionData F)
local notation "CF"=>R.family
local notation "A"=>(CF).path.levels
local notation "X"=>Unit×(Fin 3×Bool)
local notation "J"=>Stock.census (Fin 3)
def tariff:ℝ:=4*WilsonOriginalCompanionClearReturn.premium*WilsonOriginalCompanionCorridorCurrency.constant

private theorem refund (v:Fin 3)(w:Fin 3→ℝ)(s:(J).Mode)(inside:v∈s.val)
    {κ B δ fee rate z:ℝ}(kp:0<κ)(bp:0≤B)(dp:0<δ)
    (fee_paid:κ*fee≤WilsonOriginalCompanionCorridorCurrency.constant*rate)
    (paid:Poly.toll (elected v w (κ*B) (κ*δ)) s*z≤2*WilsonOriginalCompanionClearReturn.premium*fee):
    companions v w s*z≤tariff*(B+δ)*rate:=by
  let W:=elected v w (κ*B) (κ*δ)
  have nonzero:0<2*(κ*B+κ*δ):=by positivity
  have valid:W v=(2*(κ*B+κ*δ))⁻¹:=by simp [W,elected,wage]
  have total:Poly.toll W s=companions v w s*(2*(κ*B+κ*δ))⁻¹:=by
    rw [Poly.toll,←Finset.prod_erase_mul s.val W inside,valid]
    congr 1
    exact Finset.prod_congr rfl fun j hj=>by simp [W,elected,wage,(Finset.mem_erase.mp hj).1]
  have premium:0≤WilsonOriginalCompanionClearReturn.premium:=by
    unfold WilsonOriginalCompanionClearReturn.premium WilsonOriginalCompanionClearRange.ceiling;positivity
  calc _=(2*(κ*B+κ*δ))*(Poly.toll W s*z):=by rw [total];field_simp
       _≤(2*(κ*B+κ*δ))*(2*WilsonOriginalCompanionClearReturn.premium*fee):=
          mul_le_mul_of_nonneg_left paid nonzero.le
       _=4*WilsonOriginalCompanionClearReturn.premium*(B+δ)*(κ*fee):=by ring
       _≤4*WilsonOriginalCompanionClearReturn.premium*(B+δ)*(WilsonOriginalCompanionCorridorCurrency.constant*rate):=
          mul_le_mul_of_nonneg_left fee_paid (by positivity)
       _=_:=by unfold tariff;ring

theorem original (simple:G.Simple)(cater:Cater (CF) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(book:WilsonReportLampForecast.Ready (A))(c l q:ℕ):
    ∀ᶠ j:ℕ in atTop,∀N p f (height:j+2≤f) (_:f≤N),
    (f-(j+2):ℕ)≤(c:ℝ)*Real.log (RG16.Lambda (A) f)+2 →
    let P:=(CF).path.rep N p f
    let κ:=LocalComparison.forcedDivisor (CF) f
    ∀(o:Fin 3→Site ((CF).side f p))(v:Fin 3)(h:Coefficient F ((CF).side f p))(t:T→ℂ)
      (E:Lamps T I G P.p o (J))(w:Fin 3→ℝ)(B δ:ℝ)(route:∀k,(X)→Site ((CF).side k p))(anchor:(X)),
    (∀i,0<w i) → 0≤B → 0<δ → route f=(o ∘ Prod.fst) ∘ Prod.snd →
    (∀k,j+1≤k → k<f → route k=((A).clock.op k p).ratio.parent ∘ route (k+1)) →
    0≤((A).budget f).supportExponent-2 → h.Format (o v) hol P → h.remBound (o v) P κ B →
    (∀x,‖t x‖≤1) → (∀a:ℝ,E.Paid (wage v w a) P.p.B P.p.supportExponent 1) →
    (∀i,coverNumber ((CF).path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) i}:Support _)≤l) →
    ((A).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
    ∀u:ℕ,(CF).ref 0≤u → ∀uj:u≤j,Opened (CF) 0 u p → Opened (CF) 0 j p →
    ∀(x:T)(s:(J).Mode),v∈s.val →
    let Y:=fun U=>t x*(h.density (o v) sectionData P U-(soft h).density (o v) sectionData P U)*
      peers E v s x U
    Integrable Y (prior G _) ∧ companions v w s*
      ‖reading R (N:=N) (p:=p) Y u (uj.trans (by omega))‖≤
        tariff*(B+δ)*(regulatorRun (CF) N p f)^q:=by
  obtain ⟨start,coin⟩:=eventually_atTop.mp (WilsonOriginalCompanionCorridorCurrency.reserve R simple c l q)
  filter_upwards [WilsonOriginalCompanionSignedTwin.original (T:=T) (I:=I) R hol sectionData simple cater bank book,
    eventually_ge_atTop start] with j signed js
  intro N p f height fn span P κ o v h t E w B δ route anchor pos bp dp home same expo legal bound unit
    cover close fixed u ref uj ou oj x s inside Y
  have kp:0<κ:=Real.sqrt_pos.mpr (Real.exp_pos _)
  let W:=elected v w (κ*B) (κ*δ)
  let halves:=fun i=>Real.sqrt (W i)
  have hv:=admitted v w pos (mul_nonneg kp.le bp) (mul_pos kp dp)
  have hx:∀i,0<halves i:=fun i=>Real.sqrt_pos.mpr (hv.1 i)
  have square:(fun i=>halves i^2)=W:=funext (fun i=>Real.sq_sqrt (hv.1 i).le)
  have cap:halves v^2*(κ*B)≤1/2:=by rw [congrFun square v];exact hv.2
  have paid:E.Paid (fun i=>halves i^2) P.p.B P.p.supportExponent 1:=by rw [square];exact cover _
  obtain ⟨integral,full⟩:=signed N p f height fn l o v h t E halves B route anchor hx home same expo
    legal bound unit cap paid close fixed u ref uj ou oj x s
  refine ⟨integral,?_⟩
  rw [square] at full
  exact refund v w s inside kp bp dp (coin f (by omega) j span N p fn) full

end YM.Integration.WilsonOriginalCompanionPeerRefund
end
