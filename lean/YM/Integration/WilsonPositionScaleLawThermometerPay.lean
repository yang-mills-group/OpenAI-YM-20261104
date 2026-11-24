import YM.Integration.WilsonPositionScaleLawThermometerBill
import YM.Integration.WilsonPositionScaleLawThermometerRegular

/-! A numerical producer for the actual bounded-ratio coupling law. The inputs
are seven ordinary near-home marginal errors measured against an independent
fixed profile. The target far coupling is computed by the same physical route. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawThermometerPay
open Function Filter Set Finset PowerSeries MeasureTheory Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawThermometerProfile (row)
open WilsonPositionScaleLawThermometerChart (marginal)
open WilsonPositionScaleLawIndependent (ψ)
open WilsonPositionThermometerConnected (value)
open private weight from YM.Integration.WilsonPositionScaleLawHome
open scoped Topology BigOperators Classical Polynomial
variable [W:RangeSpec]{G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)

omit W in
private theorem integrate {n:ℕ}(φ:Test n)(f b:Points n→ℂ)(hf:ContinuousOn f (conf n))(hb:ContinuousOn b (conf n)):
    φ.applyTo f-φ.applyTo b=φ.applyTo (fun x=>f x-b x):=by
  unfold Test.applyTo;simp_rw [mul_sub];rw [integral_sub (φ.smearing hf) (φ.smearing hb)]

omit W in
private theorem normalized (c:ℝ)(hc:c≠0)(a p:ℂ):|a.re/c-p.re|≤‖a-(c:ℂ)*p‖/|c|:=by
  have e:a.re/c-p.re=(a-(c:ℂ)*p).re/c:=by
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    field_simp
  rw [e,abs_div];exact div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (abs_nonneg _)

def target (q:ℕ)(z:ℝ×Ratio):ℂ:=
  (trunc (q+1) (ψ Z M ν (WilsonPositionScaleLawCompactIndependent.time z.2))).eval (kinetic Z F J z.1:ℂ)

def Fits (q:ℕ)(z:ℝ×Ratio)(e:ℝ):Prop:=∀x∈tsupport (Rose.test Z.criterion),∀v:Badge,v.Nonempty→
    ‖marginal Z F J z x v-(trunc (q+1) (row Z M ν z.2 x v)).eval (kinetic Z F J z.1:ℂ)‖≤e

variable (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
include H lead paid in
theorem original (q:ℕ)(raw:WilsonPositionScaleLawCompactBranch.Raw J 6):∃L T:ℝ,0≤L ∧ 0≤T ∧ ∀ᶠ z in sweep,
    ∀e:ℝ,0≤e→e≤1→Fits Z M ν F J q z e→
    |kinetic Z F J (z.2.val*z.1)-(target Z M ν F J q z).re|≤L*e+T*|kinetic Z F J z.1|^(q+1):=by
  let φ:=Rose.test Z.criterion
  let C:=∫x,‖φ x‖
  let c:=Rose.cT Z.criterion.cut G Z.criterion.image
  have hC:0≤C:=integral_nonneg (fun _=>norm_nonneg _)
  have hc:c≠0:=Z.criterion.fresh.ne
  obtain ⟨L,T,hL,hT,quote⟩:=WilsonPositionScaleLawThermometerBill.original Z M H ν q
  have tiny:Tendsto (fun z:ℝ×Ratio=>kinetic Z F J z.1) sweep (𝓝 0):=
    (WilsonPositionPrescribedZero.measured F J Z.store lead paid hG Z.criterion).comp tendsto_fst
  have hr:∀ᶠz:ℝ×Ratio in sweep,0<z.1:=tendsto_fst (show Ioi (0:ℝ)∈trail from self_mem_nhdsWithin)
  refine ⟨C*L/|c|,C*T/|c|,by positivity,by positivity,?_⟩
  filter_upwards [hr,Metric.tendsto_nhds.mp tiny 1 zero_lt_one,WilsonPositionScaleLawThermometerChart.reading Z F J lead raw,
    WilsonPositionScaleLawThermometerChart.seated Z F J lead raw] with z age small reading seats e he he1 fits
  let u:ℂ:=kinetic Z F J z.1
  let s:=WilsonPositionScaleLawCompactIndependent.time z.2
  let A(x:Points 3):=value (marginal Z F J z x)
  let p(x:Points 3):=(trunc (q+1) (Select.Single (WilsonPositionScaleLawThermometerChart.response Z M ν s) x)).eval u
  have normu:‖u‖=|kinetic Z F J z.1|:=by simp [u,Real.norm_eq_abs]
  have hu:‖u‖≤1:=by rw [normu];simpa only [dist_zero_right,Real.norm_eq_abs] using small.le
  have Aeq:A=(fun x=>value (WilsonPositionThermometerReading.sample F (WilsonPositionScaleLawHome.positioned F J Z.store) (z.2.val*z.1) x)):=by
    funext x;exact congrArg WilsonPositionThermometerConnected.value (funext (seats x))
  have live:ContinuousOn A (conf 3):=by
    rw [Aeq];exact WilsonPositionScaleLawThermometerRegular.original _ _ (mul_pos (WilsonPositionScaleLawCompactNative.positive z.2) age)
  have data:ContinuousOn p (conf 3):=by
    dsimp only [p];simp_rw [WilsonPositionScaleLawThermometerSmeared.paper]
    exact continuousOn_finsetSum _ (fun k _=>(WilsonPositionScaleLawThermometerSmeared.smooth Z M H ν s k).mul_const _)
  have bill:=weight φ (fun x=>A x-p x) (L*e+‖u‖^(q+1)*T)
    (fun x hx=>quote z.2 x hx u hu (marginal Z F J z x) e he he1 (fits x hx))
  rw [←integrate φ A p live data] at bill
  have stamp:φ.applyTo p=(c:ℂ)*target Z M ν F J q z:=WilsonPositionScaleLawThermometerSmeared.original Z M H ν s q u
  rw [stamp] at bill
  rw [reading]
  calc _≤‖φ.applyTo A-(c:ℂ)*target Z M ν F J q z‖/|c|:=normalized c hc _ _
       _≤(C*(L*e+‖u‖^(q+1)*T))/|c|:=div_le_div_of_nonneg_right bill (abs_nonneg c)
       _=(C*L/|c|)*e+(C*T/|c|)*|kinetic Z F J z.1|^(q+1):=by rw [normu];ring

end YM.Integration.WilsonPositionScaleLawThermometerPay
end
