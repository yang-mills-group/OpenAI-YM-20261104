import YM.Integration.WilsonOriginalCompanionBeforeRoster
import YM.Integration.WilsonOriginalCompanionPeerRefund

/-! One physical date for all future test sets, all countable rent lists and every admitted frame. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionBeforePeer
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source QuadraticLocal QuadraticLocal.Earn Marker
open Push Ac GridApprox.Nil MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open RG05Readout RG05Readout.Native RG05Readout.Many PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Mallow Motion Bandage Next.Foundations Trace.Physical.GermGraph Pert.Asymptotics
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection
open WilsonMeasuredCompanionFace WilsonMeasuredCompanionWage WilsonThermometerUnitFilingCoarse
open scoped Classical BigOperators Topology
open WilsonOriginalCompanionLinearFiling WilsonOriginalCompanionTwinCredit WilsonOriginalCompanionClearReturn
open WilsonOriginalCompanionPeerRefund WilsonOriginalCompanionTwinIntake WilsonOriginalDepositedHard
open private refund from YM.Integration.WilsonOriginalCompanionPeerRefund
open private sub from YM.Integration.WilsonOriginalCompanionSignedTwin
variable {G:Gauge}(R:Run G)
local notation "CF"=>R.family
local notation "A"=>(CF).path.levels
local notation "X"=>Unit×(Fin 3×Bool)
local notation "J"=>Stock.census (Fin 3)
theorem original (simple:G.Simple)(cater:Cater (CF) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(book:WilsonReportLampForecast.Ready (A))(c l q:ℕ):
    ∀ᶠ j:ℕ in atTop,∀ (T I:Type) [Countable I] {d:ℕ} {F:Frame G d} (hol:Hol G)(sectionData:SectionData F),∀N p f (height:j+2≤f) (_:f≤N),
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
        WilsonOriginalCompanionPeerRefund.tariff*(B+δ)*(regulatorRun (CF) N p f)^q:=by

  obtain ⟨start,coin⟩:=eventually_atTop.mp (WilsonOriginalCompanionCorridorCurrency.reserve R simple c l q)
  obtain ⟨age,house⟩:=eventually_atTop.mp ((WilsonMeasuredOwnerReserve.room R simple).and
    (WilsonOriginalCompanionHardCurrency.reserve R simple))
  filter_upwards [WilsonOriginalCompanionBeforeRoster.original R simple cater bank book,
    eventually_ge_atTop start,eventually_ge_atTop age] with j paid js ja
  intro T I inst d F hol sectionData N p f height fn span P κ o v h t E w B δ route anchor pos bp dp home
    same expo legal bound unit cover close fixed u ref uj ou oj x s inside Y
  have kp:0<κ:=Real.sqrt_pos.mpr (Real.exp_pos _)
  let W:=elected v w (κ*B) (κ*δ)
  let halves:=fun i=>Real.sqrt (W i)
  have hv:=admitted v w pos (mul_nonneg kp.le bp) (mul_pos kp dp)
  have hx:∀i,0<halves i:=fun i=>Real.sqrt_pos.mpr (hv.1 i)
  have square:(fun i=>halves i^2)=W:=funext (fun i=>Real.sq_sqrt (hv.1 i).le)
  have cap:halves v^2*(κ*B)≤1/2:=by rw [congrFun square v];exact hv.2
  have paidE:E.Paid (fun i=>halves i^2) P.p.B P.p.supportExponent 1:=by rw [square];exact cover _

  let atm:=((R.T.sticks N p).prices f (Nat.zero_le _) fn).1
  let cash:=(A).clock.forcedAllowance f
  let rent : Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent cash:=
    Hard.rentValid atm.valid.labels.forced atm.valid.labels.boundK
  let base:Hard T P.p P.activities.forced P.activities.K o (J):=Hard.rent rent
  let lo:Gallery T I o P (J):=⟨E,base⟩
  let hi:Gallery T I o P (J):=⟨E,joined base v h legal t⟩
  have params:P.p=(A).budget f:=(R.makes.wilson.represents N p f fn).vac
  have within:((A).budget f).supportExponent-2≤P.p.supportExponent:=by rw [params];linarith
  have money:=house f (by omega)
  have small:cash≤1/2:=money.1.trans (div_le_div_of_nonneg_right
    (money.2.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _)))) (by norm_num))
  obtain ⟨old,new,_clear,field⟩:=WilsonOriginalCompanionTwinIntake.received rent v h legal sectionData t E halves hx
    atm.valid unit bound (small.trans (by norm_num)) (by linarith only [small,cap]) paidE expo within x
  let uf:u≤f:=by omega
  have total:0≤WilsonOriginalCompanionTwinCredit.fare R f j l:=by
    unfold WilsonOriginalCompanionTwinCredit.fare
    have good:0≤(A).clock.hatBeta f:=zero_le_one.trans ((A).fits.delayed f).le
    positivity
  have each(D:Gallery T I o P (J))(issued:Admitted D x halves (((A).budget f).supportExponent-2)):
      Poly.toll (fun i=>halves i^2) s*‖(amount R (N:=N) (D.density x) uf).part s‖≤premium*WilsonOriginalCompanionTwinCredit.fare R f j l:=by
    exact WilsonOriginalCompanionClearReturn.original R D x halves hx expo issued.1 issued.2.1 issued.2.2.1 uf total
      (paid T I N p f height fn l o D x halves route anchor hx home same expo issued.1 issued.2.1 issued.2.2.1
        close fixed u ref uj ou oj) s
  have iden:Y=fun U=>(hi.density x U).part s-(lo.density x U).part s:=by
    funext U
    dsimp only [Y]
    linear_combination field s U
  have ih:Integrable (fun U=>(hi.density x U).part s) (prior G _):=(Poly.get s).integrable_comp new.2.2.1
  have ib:Integrable (fun U=>(lo.density x U).part s) (prior G _):=(Poly.get s).integrable_comp old.2.2.1
  have integral:Integrable Y (prior G _):=by rw [iden];exact ih.sub ib
  refine ⟨integral,refund v w s inside kp bp dp (coin f (by omega) j span N p fn) ?_⟩
  change Poly.toll W s*‖reading R (N:=N) (p:=p) Y u uf‖≤_
  rw [←square,iden,sub R _ _ ih ib uf,←coordinate R _ new.2.2.1 s uf,←coordinate R _ old.2.2.1 s uf]
  have wp:=(Poly.worth (fun i=>pow_pos (hx i) 2) s).le
  calc _≤Poly.toll (fun i=>halves i^2) s*
           (‖(amount R (N:=N) (hi.density x) uf).part s‖+‖(amount R (N:=N) (lo.density x) uf).part s‖):=
             mul_le_mul_of_nonneg_left (norm_sub_le ..) wp
       _≤_:=by rw [mul_add];linarith only [each lo old,each hi new]

end YM.Integration.WilsonOriginalCompanionBeforePeer
end
