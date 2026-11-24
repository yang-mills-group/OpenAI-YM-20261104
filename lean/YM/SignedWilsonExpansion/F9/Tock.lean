import YM.SignedWilsonExpansion.F9.AssemblyH
import YM.SignedWilsonExpansion.F9.MvBill
/-! # Payer costs and common ordering: Clothes order through fixed horizon p -/
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b N M i j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace MarqueQ
namespace PorchK
open SignedWilsonExpansion.Commission Method Method.Epic Asymptotics Stair MergeTrip Looms Crops
open Normalize (Sec)
open XSpace.Cirrus
variable {W':Initialize G}{Q':∀ h,Rays G h W'.hol}{Ω:Council F}
variable {P':Hol G}{ι:Type} {L:Filter ι}{Y θ μ ν :ι→ℝ}
variable (x:PorchK W' F Q' Ω R h k u)(q:ι→ PorchK W' F Q' Ω R h k u)(Wn:Normalize.Store G)
variable (K':Rose.Pick Wn)(St:∀ i≤e, Across L Y ℂ (fun j=>(q j).toEpic.tenor W' Wn i))(U':RateQ.Costy L Y (fun i=>(q i).toEpic.voice W' K') e)
variable (Bf:FrontQ q L Y θ μ ν)(w:∀ᶠ i in L,0< θ i)
section timing
abbrev earns0 (x:PorchK W' F Q' Ω R h k u)(K:Rose.Pick Wn)(k:ℕ)(τ:ℝ):ℂ:= calcT τ k (x.χ Wn K) -- binder order
lemma Kconst : constantCoeff (x.χ Wn K')=0:= recall_zero ..
lemma real_level (i:ℕ) : coeff i (x.χ Wn K')= ((coeff i (x.χ Wn K')).re:ℂ):=by
    let Z:=x.χ Wn K'; set a:= coeff i Z
    have hx: star a=a:= realLevel _ (MergeTrip.recall_real ..) i; apply Complex.ext; · simp
    have ht:=congr_arg Complex.im hx; simp at ht; change _=( (↑((_ :ℂ).re):ℂ)).im; rw [Complex.ofReal_im]; linarith
abbrev earnsR (x:PorchK W' F Q' Ω R h k u)(K:Rose.Pick Wn)(k:ℕ)(τ:ℝ):ℝ:= (x.earns0 Wn K k τ).re
lemma real_earns : x.earns0 Wn K' i t=(x.earnsR Wn K' i t:ℂ):=by
    unfold earnsR earns0; rw [timed]; apply Complex.ext; · simp
    rw [ Complex.ofReal_im,Complex.im_sum]; refine Finset.sum_eq_zero (fun j _=>?_); rw [ real_level ]; simp [←Complex.ofReal_pow]
lemma Kfirst_t : coeff 1 (x.χ Wn K')= coeff 1 (Rose.chosen W' K' x.mesh):= recall_one W' K' R.draws R.paid x.mesh x.datum (x.landing.trans x.endo) R.hG R.green -- parameter order
structure TimeQ (L:Filter ι)(θ:ι→ℝ)(ξ:ι→ℝ):Prop where
     τbias : Tendsto (ξ / θ) L (𝓝 1)
private lemma bias_enters {θ g:ι→ℝ}(p:TimeQ L θ g)(v:∀ᶠ i in L,0<θ i): g=O[L] θ:=by
    let H:= (isBigO_const_of_tendsto p.τbias (show (1:ℝ)≠0 from one_ne_zero)).mul (isBigO_refl θ L); exact H.congr' (v.mono (fun i hi=>div_mul_cancel₀ _ hi.ne')) (Eventually.of_forall fun i=>one_mul _)
include Bf
lemma smallG : ∀ᶠ i in L,|θ i|≤1:=by
    have h:= Bf.decays 0; simp only [pow_zero,one_mul] at h; exact h.eventually ((continuous_abs.continuousAt.tendsto).eventually ( eventually_le_nhds (by simp: |(0:ℝ)| < 1) ) )
omit Bf
variable (t':ι→ℝ)(guide:TimeQ L θ t')
include w t' guide
lemma TimeN : (fun i=> (t' i:ℂ))=O[L] θ:=by
    apply (IsBigO.trans ?_ (bias_enters guide w)); exact IsBigO.of_bound' (Eventually.of_forall fun i=> by simp)
include U' Bf
lemma τfit : charge e L μ (1:ι→ℝ) (fun i=> (q i).χ Wn K'):=fun i z=> Wage.transfer (chrono q Wn Bf.pol K' U' i z) Bf.ahead
lemma setting (k:ℕ)(u:k≤e): Taught L μ θ 1 (fun i=> (t' i:ℂ)) k (fun i=> (q i).χ Wn K') (fun i=> (q i).earns0 Wn K' k (t' i)):= Taught.epoch Bf.inside_ (smallG q Bf) _ (TimeN w t' guide) (fun i v=> τfit q Wn K' U' Bf w t' guide _ (v.trans u)) -- omit U progress
lemma timestamp (k:ℕ) (t:0<k)(V:k≤ e): TimeQ L θ (fun i=> (q i).earnsR Wn K' k (t' i)):=by
    let Z(i):= (q i).χ Wn K'; let x(i):= (t' i:ℂ); let ε(i):= (θ i:ℂ); have u1:Taught L μ θ 1 x k Z (fun i=>(q i).earns0 Wn K' k (t' i)):= setting q Wn K' U' Bf w t' guide k V; have ht:= clockQ.dropFee Bf.inside_ (smallG q Bf) x (TimeN w t' guide) Z u1.price 1 k t le_rfl; let f(i):= (q i).earns0 Wn K' k (t' i); have he(i):f i- calcT (x i) 1 (Z i)=f i- coeff 1 ( Z i )*x i:=by rw [timed]; have hv:constantCoeff (Z i)=0:= (q i).Kconst ..; have hh : coeff 0 (Z i)=0:=(coeff_zero_eq_constantCoeff_apply ..).trans hv; simp [ Finset.sum_range_succ,hh ]
    have hK:Tendsto (fun i=> coeff 1 (Z i)) L (𝓝 1):=by simp_rw [Z,Kfirst_t]; exact (Rose.xc W' K' R.hG).comp (goesFront Bf.stretch)
    have hx:Tendsto (fun i=> x i/ε i) L (𝓝 1):=by let p:= guide.τbias; rw [← show ((1:ℝ):ℂ)=1 from Complex.ofReal_one]; apply (Complex.continuous_ofReal.continuousAt.tendsto.comp p).congr; exact fun i=> by change (( ( t' i / θ i):ℝ):ℂ)=_; rw [Complex.ofReal_div]
    have hv:Tendsto (fun i=>(f i-calcT (x i) 1 (Z i))/ε i) L (𝓝 0):=by
       have h0:= Wage.mul ht (Wage.reals.mp (Wage.enroll (u:=μ) (isBigO_refl ( θ⁻¹ ) L))); apply Wage.next_zero (Wage.fix h0 (?_) (?_)) Bf.decays
       · exact Eventually.of_forall fun i=>by change (_ :ℂ)* ((↑ (θ i)⁻¹):ℂ)=_; rw [Complex.ofReal_inv]; rfl
       filter_upwards [w] with i hi; change 1*θ i^(1+1)*(θ i)⁻¹=θ i; rw [one_mul,pow_succ,pow_one,mul_assoc,mul_inv_cancel₀ hi.ne',mul_one]
    let H:= hv.add (hK.mul hx); simp only [one_mul,zero_add] at H; have hh:Tendsto (fun i=> f i/ε i) L (𝓝 1):= H.congr (fun i=>by rw [he]; ring)
    constructor; let L':ℝ:=(1:ℂ).re; change Tendsto (fun i=>_ / _) L (𝓝 L'); convert! Complex.continuous_re.continuousAt.tendsto.comp hh using 1; ext1 i; unfold Function.comp; rw [Complex.div_ofReal_re]
-- norm Projection source evaluation.Test at any θ shapes simultaneously.
end timing
end PorchK
end MarqueQ
end YM.WilsonCoeffUV.Mer.Xa
