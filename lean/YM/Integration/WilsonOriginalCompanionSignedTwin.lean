import YM.Integration.WilsonOriginalCompanionTwinCredit
import YM.Integration.WilsonOriginalCompanionClearReturn
import YM.Integration.WilsonOriginalCompanionCanonicalSeat

/-! A complete P-side marked hard account tested against its two real ordinary peers. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionSignedTwin
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source QuadraticLocal QuadraticLocal.Earn Marker Push
open Ac GridApprox.Nil MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open RG05Readout RG05Readout.Native RG05Readout.Many PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Mallow Motion Bandage Next.Foundations Trace.Physical.GermGraph
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection WilsonOriginalDepositedHard
open WilsonOriginalCompanionLinearFiling WilsonOriginalCompanionTwinCredit WilsonOriginalCompanionClearReturn
open WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionTwinIntake
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){T I:Type}[Countable I]{d:ℕ}{F:Frame G d}(hol:Hol G)(sectionData:SectionData F)
local notation "CF"=>R.family
local notation "A"=>(CF).path.levels
local notation "X"=>Unit×(Fin 3×Bool)
local notation "J"=>Stock.census (Fin 3)

private theorem sub {N p f u:ℕ}(a b:Config G ((CF).side f p)→ℂ)(ha:Integrable a (prior G _))
    (hb:Integrable b (prior G _))(uf:u≤f):
    reading R (N:=N) (p:=p) (fun U=>a U-b U) u uf=reading R (N:=N) a u uf-reading R (N:=N) b u uf:=by
  have field:(fun U=>a U-b U)=a+(-1:ℂ) • b:=by funext U;simp [sub_eq_add_neg]
  rw [field,WilsonThermometerUnitFilingRaw.add R _ _ ha (hb.smul _) uf,
      WilsonThermometerPepperDifference.scaled R (-1) _ hb uf]
  ring

theorem original (simple:G.Simple)(cater:Cater (CF) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(wage:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ j:ℕ in atTop,∀N p f (height:j+2≤f) (fn:f≤N)(l:ℕ),
    let P:=(CF).path.rep N p f
    let κ:=LocalComparison.forcedDivisor (CF) f
    ∀(o:Fin 3→Site ((CF).side f p))(v:Fin 3)(h:Coefficient F ((CF).side f p))(t:T→ℂ)
      (E:Lamps T I G P.p o (J))(w:Fin 3→ℝ)(B:ℝ)(route:∀k,(X)→Site ((CF).side k p))(anchor:(X)),
    (∀i,0<w i) → route f=(o ∘ Prod.fst) ∘ Prod.snd →
    (∀k,j+1≤k → k<f → route k=((A).clock.op k p).ratio.parent ∘ route (k+1)) →
    0≤((A).budget f).supportExponent-2 → h.Format (o v) hol P → h.remBound (o v) P κ B →
    (∀x,‖t x‖≤1) → w v^2*(κ*B)≤1/2 → E.Paid (fun i=>w i^2) P.p.B P.p.supportExponent 1 →
    (∀i,coverNumber ((CF).path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) i}:Support _)≤l) →
    ((A).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
    ∀u:ℕ,(CF).ref 0≤u → ∀uj:u≤j,Opened (CF) 0 u p → Opened (CF) 0 j p →
    ∀(x:T)(s:(J).Mode),
    let Y:=fun U=>t x*(h.density (o v) sectionData P U-(soft h).density (o v) sectionData P U)*
      WilsonMeasuredCompanionFace.peers E v s x U
    Integrable Y (prior G _) ∧ Poly.toll (fun i=>w i^2) s*
      ‖reading R (N:=N) (p:=p) Y u (uj.trans (by omega))‖≤2*premium*fare R f j l:=by
  obtain ⟨start,seat⟩:=eventually_atTop.mp (WilsonOriginalCompanionCanonicalSeat.original (V:=Fin 3)
    (T:=T) (I:=I) R simple hol sectionData)
  filter_upwards [WilsonOriginalCompanionTwinCredit.original (T:=T) (I:=I) R simple cater bank wage,
    eventually_ge_atTop start] with j paid js
  intro N p f height fn l P κ o v h t E w B route anchor pos home same expo legal bound unit cap reg
    close fixed u ref uj ou oj x s Y
  have dated:start≤f:=by omega
  obtain ⟨rent,book⟩:=seat f dated N p fn
  let base:Hard T P.p P.activities.forced P.activities.K o (J):=Hard.rent rent
  let lo:Gallery T I o P (J):=⟨E,base⟩
  let hi:Gallery T I o P (J):=⟨E,joined base v h legal t⟩
  have params:P.p=(A).budget f:=(R.makes.wilson.represents N p f fn).vac
  have within:((A).budget f).supportExponent-2≤P.p.supportExponent:=by rw [params];linarith
  obtain ⟨old,new,_cleared,field⟩:=book o v h legal t E w B pos unit bound cap reg _ expo within x
  let uf:u≤f:=by omega
  have wpos:∀i,0<w i^2:=fun i=>pow_pos (pos i) _
  have total:0≤fare R f j l:=by
    unfold WilsonOriginalCompanionTwinCredit.fare
    have good:0≤(A).clock.hatBeta f:=zero_le_one.trans ((A).fits.delayed f).le
    positivity
  have each (D:Gallery T I o P (J))(issued:Admitted D x w (((A).budget f).supportExponent-2)):
      Poly.toll (fun i=>w i^2) s*‖(amount R (N:=N) (D.density x) uf).part s‖≤premium*fare R f j l:=by
    exact WilsonOriginalCompanionClearReturn.original R D x w pos expo issued.1 issued.2.1 issued.2.2.1 uf total
      (paid N p f height fn l o D x w route anchor pos home same expo issued.1 issued.2.1 issued.2.2.1
        close fixed u ref uj ou oj) s
  have iden:Y=fun U=>(hi.density x U).part s-(lo.density x U).part s:=by
    funext U
    dsimp only [Y]
    linear_combination field s U
  have ih:Integrable (fun U=>(hi.density x U).part s) (prior G _):=(Poly.get s).integrable_comp new.2.2.1
  have ib:Integrable (fun U=>(lo.density x U).part s) (prior G _):=(Poly.get s).integrable_comp old.2.2.1
  rw [iden]
  refine ⟨ih.sub ib,?_⟩
  rw [sub R _ _ ih ib uf,←coordinate R _ new.2.2.1 s uf,←coordinate R _ old.2.2.1 s uf]
  have wp:=(Poly.worth wpos s).le
  calc _≤Poly.toll (fun i=>w i^2) s*
            (‖(amount R (N:=N) (hi.density x) uf).part s‖+‖(amount R (N:=N) (lo.density x) uf).part s‖):=
              mul_le_mul_of_nonneg_left (norm_sub_le ..) wp
       _≤_:=by rw [mul_add];linarith only [each lo old,each hi new]

end YM.Integration.WilsonOriginalCompanionSignedTwin
end
