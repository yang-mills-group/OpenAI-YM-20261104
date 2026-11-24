import YM.OPE.Compatible.Soup.Came
/-!
# Epoch growth. Limited trajectory tape. variance observables without spectral cost loss
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.OPE.Owl.HillZ
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset
open Silt Libra Coin Rill Silt.Float Votive PertExtension Series GaussianScore Radial Next.Foundations
open Merchant Merchant.Aloof Merchant.Sleeve Merchant.SiteL
open Next.Free Next.Scheduling Stroke Spells Lass Lass.Zest Pill CardinalQ
variable {I:Type}{φ:Filter I}{G:Gauge} {K:Sponsor G}{T:Seasons K}
variable {β:I→ℝ}{n:I→Side}{S:Stage}{i j d r k:ℕ}{τ s a B:ℝ}
variable {A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x)}{U: Scaffold φ (Counters β) n (Mnd i S A) r}
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop) (A U)
open Cinders Metric Set Zeph Jargon
variable {N:ChartRatio G} {s c:ℝ}(H:Sweep N s c)(hN:LocalRatio N) (x:∀ i,Bid.Dir G (n i))(g:ℂ→L[ℝ]ℝ)
local notation "E!"=>Merchant.Chamber G r
local notation "X!"=> Palace G r
noncomputable abbrev Yfar (j:I)(v:E!) := x j + Stair A U j v
private lemma Cah {n:Side}(P:Board n (r+1))(x:Bid.Dir G n)(z:Merchant.Chamber G r)(t:ℝ):install P (represent (t • x)) (put (t • (z+PinT G x)))=represent (t • (x+sailT G P z)):=by
       funext i; by_cases h:i∈ fringe r n; swap; · rw [inF _ _ _ _ h,arkL,arkL]; simp only [Pi.smul_apply, Pi.add_apply,silly G P z i h, add_zero]
       obtain ⟨j,rfl⟩:= from_port P i h; rw[inSeat,arkL]
       have he:t • (z j+PinT G x j)= t • (x (arkE (dig P j)) + sailT G P z (arkE (dig P j))):=by rw [PinS G P x j,add_comm]; rw [show arkE (dig P j)=terr P j from rfl, tide G P z j]
       exact congr_arg G.lieExp he
lemma chatE (i:I)(p:E!): install (Punched A U i) (EC A i (x i)) (put (et A i • (p+Odds (r:=r) x i))) = EC A i (Yfar A U x i p):=Cah ..
noncomputable def ConV (N:ChartRatio G)(i:I)(p:E!):= Bo A U g x i (put (et A i • (p+Odds (r:=r) x i)))*Real.exp (feeX N (et A i • (p+Odds x i))+(D i).P p p / 2) -- arg g binder order maybe reversed
private lemma pMeterZ {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X](μ:Measure X)[μ.IsAddHaarMeasure] (L:Law X)(x:X)(s D:Set X)(hp:D=(fun y=>y+x) ⁻¹' s)(f g:X→ℝ)(hs:MeasurableSet s)(k:ℝ)(he:∀ y∈ D,f (y+x)=k*(g y*L.kern y)):
     (∫ i in s,f i ∂μ)= k*(rentF L μ*∫ i in D,g i ∂ quart L μ):=by
          subst D; let D:=(fun y=>y+x) ⁻¹' s; have hv :MeasurableSet D:= hs.preimage (show Measurable (fun y:X=> y+x) by fun_prop); let p:=D.indicator g
          have hz(y:X): s.indicator f (y+x)=k*(p y*L.kern y):=by
             by_cases h:y ∈ D
             · unfold p; rw [indicator_of_mem h, indicator_of_mem (show y+x∈s from h)]; exact he y h
             unfold p; rw [indicator_of_notMem (show y+x ∉ s from h),indicator_of_notMem h,zero_mul,mul_zero]
          rw[← integral_indicator hv,← integral_indicator hs,← integral_add_right_eq_self (s.indicator f) x (μ:=μ)]; simp_rw[hz]; change _= _*(rentF _ μ*∫ y,p y ∂ quart L μ); rw [integral_const_mul,has_p,Law.average,mul_div_cancel₀];rfl; exact (Jargon.spent μ L).ne'
noncomputable def FareV (N:ChartRatio G) (i:I):= (et A i)^(Module.finrank ℝ (Merchant.Chamber G r))*N.scale^(fieldP r).card*rentF (D i) (onH G r)
variable (P:I→ℝ)
include H hN
set_option maxHeartbeats 200000
lemma quoted (i:I)(hP:et A i*P i ≤ c)(ht:0 < et A i):
      (∫ y in storm A P i, Bo A U g x i y ∂(Duo G r))= FareV A D N i*∫ y in ChartS A x P s i,ConV A U D x g N i y ∂ ShoreP D i:=by -- binder order
           let B:=et A i*P i; let T:=et A i; let v:=D i; let q:= Bo A U g x i; let S:= storm A P i; let a:= S.indicator q; have hc:Measurable q:=(show Continuous q from (g.continuous.comp ((A i).realm.comp (monoInst ..))).div_const _).measurable; let Y:=CapeQ G (fieldP r) B T s; let f(y:E!):=Chart.jacobian N (T • y)*a (put (T • y)); let b:=ChartS A x P s i; let m:=Odds (r:=r) x i; let μ:=onH G r; let u:=ConV A U D x g N i
           have he : (∫ y in Y,f y∂μ)= N.scale ^ (fieldP r).card*(rentF v μ*∫ y in b,u y ∂ShoreP D i):=by
                 refine pMeterZ μ v m Y b rfl f u capeMeas _ ?_; intro y hy; let z:=T • (y+m); change Chart.jacobian N z*a (put z)= _; change y+m∈ CapeQ G (fieldP r) B T s at hy; rw [pay hN H z hy.2, Fintype.card_coe,show a (put z)=q _ from indicator_of_mem (show put z∈ S from hy.1) _]; let t:=feeX N z; let w:=q (put z); change (_*Real.exp t)*w=_*(w*Real.exp (t+v.P y y/2)*Real.exp (-(v.P y y)/2)); rw [mul_assoc w,← Real.exp_add,show t+v.P y y/2+-(v.P y y)/2=t from by ring]; ring
           rw [← integral_indicator chamberMeas]; rw [show (∫ y,a y ∂Duo G r)= T^Module.finrank ℝ (Merchant.Chamber G r)* (∫ y in Y,f y∂μ) from giving (F:=↥(fieldP r)) hN H a (hc.indicator chamberMeas) (fun y hy=>indicator_of_notMem hy _) hP ht]; rw[he,FareV]; change _= T^Module.finrank ℝ (Merchant.Chamber G r)*_*rentF _ _*∫ y in b,u y ∂ShoreP D i; ring
include h hs
lemma scaleΞ (hU:Startup A U x P s c D)(he:GaugeD A U D): Wick β φ (fun i=> ∫ y in ChartS A x P s i, ConV A U D x g N i y ∂ ShoreP D i):=by
       intro a; let k:= Module.finrank ℝ (Merchant.Chamber G r); let v:ℝ:=k/2; have ht:Wax β φ (fun i=>(FareV A D N i)⁻¹) v :=by
               let K':=carth h; let p:= ((Tango A h).inv.pays K'); apply RateLE.congr (show _ from (((p.pow k K').mul (RateLE.const (N.scale^((fieldP r).card):ℝ)⁻¹ K')).mul (waitG h (D_purses hs h he))).mono (le_of_eq (show (k:ℝ)* (- (-(1/2):ℝ))+0+0=v from by unfold v;ring))); filter_upwards with i; unfold FareV; simp only [_root_.mul_inv,inv_pow];rfl
       let hv:= sparkW (x:=x) h g hU.V; apply RateLE.congr (((hv (a-v)).mul ht).mono (le_of_eq (by ring))); filter_upwards [hU.agrees,hymn A h] with i hi hx; rw [quoted A U D H hN x g P i hi.2.1 hx.1]; have hh:0 < FareV A D N i:=mul_pos (mul_pos (pow_pos hx.1 _) (pow_pos hN.scale _)) (spent _ _); field_simp
end YM.OPE.Owl.HillZ
