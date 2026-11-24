import YM.OPE.Compatible.Lamb.Pique
import YM.OPE.Compatible.Ocher.Vin
/-! # Sphere density with β*t axis fixed; Haar shift in arithmetic. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Zeph
open Function Filter Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree Push Push.AbsoluteSums Precision Matrix MeasureTheory Exterior
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra GaussianScore Metric Limn Cinders
variable {G:Gauge}{c f:Side}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin Set
open PhysicalNext.Repeat.Aroma
open YM.AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate Sheets Radius.Model
open Woody Next.Free Finset Work.F03 Progress.StationaryScenes AnalyticNext.QuarticMatch.Local Cascade Rill Glass Coin
open Votive Stationary
variable {t r R B b ε x y z C k' R' t' t'' u:ℝ}{m:ℕ}
variable (S:StepData c f)(H:Odd S.ratio.count.val)
local notation "F"=> Woody.forest S.ratio H
local notation "Q" =>(Bid.Dir G c × AxisChart G F)
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u:ℝ}
variable (A:Alps K T i v)(U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g:Bid.Dir G c→ AxisChart G (forest S.ratio H)}(k:S.Choices)
variable (V:FibreRep S H U k A g b)(h:licensed S H U A.clip A.live L A.sky g)
local notation "Σ!"=>pane F k A.clip A.live
open Dew
variable (P:Rep G f)
structure fitsW (P:Rep G f):Prop where
       clip : P.clip=A.clip
       path : P.path=A.live
variable (hA:fitsW A P)
variable (I:Seats (forest S.ratio H))(w: Bid.Dir G c)(a: AxisChart G (forest S.ratio H)){N:ChartRatio G}
local notation "γ"=>PatchM S H A U k V I
local notation "γX"=>onset S H A U k V I a w
local notation "Ω"=>Chart.tangent G (I:Type)
local notation "Ψ"=> Cinders.quart γ Ω
include hA h
lemma polarQ (x:Keys G (↥I)):
     haul S F k P I w a (x+γX)= haul S F k P I w a γX + (γ).P x x/2:=by
             let Z:=V.L.Q; let y:= V.L.M w; let P':= ChartUp S F I Z; let m:= γ; let s:= γX; let v:=a-y; have he:P' v=-s:=by rw[show v= -(y-a) by unfold v; abel,map_neg]
             have hT (q:Keys G (↥I)): haul S F k P I w a q=jet Σ! 2 (w,y)+Z.P (v-stake I (P' v)) (v-stake I (P' v))/2 + m.P (q-s) (q-s)/2:=by
                 unfold haul; rw [hA.clip,hA.path]; rw [show VegaP S F I w a q = (w,y+(v+stake I q)) from Prod.ext rfl (by unfold v VegaP;change _= _+(_-_+_); abel)]; rw [WarpedQ S H A U k V h]; change _+Z.P (v+stake I q) (v+stake I q)/2=_; rw [show Z.P (v+stake I q) (v+stake I q)=Z.P (v-stake I (P' v)) (v-stake I (P' v))+m.P (q+P' v) (q+P' v) from CostV _ _ _ (inflect I Z) _, he]; simp only[sub_eq_add_neg];ring
             change haul _ _ _ _ _ _ _ (x+s)=_; rw [hT,hT,add_sub_cancel_right]; change _=_+m.P (s-s) (s-s)/2+_; rw[sub_self,map_zero];simp;rfl
omit h hA
noncomputable def Dress (N:ChartRatio G)(ε:ℝ)(z:Keys G (↥I)):=
      let x:= z+γX; Real.exp (feeX N (ε • x)+ScoreV F I P k a w ε x+haul S F k P I w a x)
noncomputable abbrev Prism (ε t r:ℝ):Set (Keys G (↥I)):= {x|x+γX∈CapeQ G (↥I) t ε r}
lemma Prism_meas : MeasurableSet (Prism S H A U k V I w a ε t r):= capeMeas.preimage (show Measurable (fun x:Keys G (↥I)=>x+γX) by fun_prop)
include hA h
lemma grain_V (N: ChartRatio G)(ε:ℝ)(x:Keys G (↥I)): Rotary w ε F I k P a N (x+γX)=Real.exp (-(haul S F k P I w a γX))*(Dress S H A U k V P I w a N ε x*(γ).kern x):=by
      unfold Rotary Dress Law.kern; dsimp only; rw [← Real.exp_add,← Real.exp_add,polarQ S H A U k V h P hA]; apply congr_arg; ring
omit h hA in
private lemma pMeter {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X](μ:Measure X)[μ.IsAddHaarMeasure] (L:Law X)(x:X)(s D:Set X)(hp:D=(fun y=>y+x) ⁻¹' s)(f g:X→ℝ)(hs:MeasurableSet s)(k:ℝ)(he:∀ y:X,f (y+x)=k*(g y*L.kern y)):
     (∫ i in s,f i ∂μ)= k*(rentF L μ*∫ i in D,g i ∂ quart L μ):=by
          subst D; let D:=(fun y=>y+x) ⁻¹' s; have hv :MeasurableSet D:= hs.preimage (show Measurable (fun y:X=> y+x) by fun_prop); let p:=D.indicator g
          have hz(y:X): s.indicator f (y+x)=k*(p y*L.kern y):=by
             by_cases h:y ∈ D
             · unfold p; rw [indicator_of_mem h, indicator_of_mem (show y+x∈s from h)]; exact he y
             unfold p; rw [indicator_of_notMem (show y+x ∉ s from h),indicator_of_notMem h,zero_mul,mul_zero]
          rw[← integral_indicator hv,← integral_indicator hs,← integral_add_right_eq_self (s.indicator f) x (μ:=μ)]; simp_rw[hz]; change _= _*(rentF _ μ*∫ y,p y ∂ quart L μ); rw [integral_const_mul,has_p,Law.average,mul_div_cancel₀];rfl; exact (Jargon.spent μ L).ne' -- tmp
lemma peakH (N:ChartRatio G)(ε t r:ℝ)(p:Keys G (↥I)→ℝ):
     (∫ x in CapeQ G (↥I) t ε r, Rotary w ε F I k P a N x*p x ∂Ω)=Real.exp (-(haul S F k P I w a γX)) * (rentF γ Ω *(∫ x in Prism S H A U k V I w a ε t r, Dress S H A U k V P I w a N ε x*p (x+γX) ∂Ψ)):=by
          apply pMeter _ _ (onset S H A U k V I a w) _ _ rfl _ _ capeMeas _; intro y; rw [grain_V S H A U k V h P hA]; ring
end YM.OPE.Zeph
