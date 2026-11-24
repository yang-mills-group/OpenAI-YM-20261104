import YM.MS.Vane.Zever
/-!
# Connected IR scalar & quantitative tail. Cost carries exp decay of positive rank epsilon. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I W:Type}{G:Gauge}{P:Geo I}{K:Belt I}{F H D:Glade G I}{X: I→ℂ}{d:ℕ}{x:ℝ}{A: K.time→ℝ}
-- R=D.Shell q≥0. Lim an actual blade.Criterion
abbrev scalar (F:Glade G I)(p: K.time):= F p.1 ( tstart p ) []
abbrev blade (F: Glade G I)(i:I):= limUnder atTop (fun t:ℝ=>F i t [])
abbrev Allow (F:Glade G I)(i:I): Prop:= Tendsto (fun t:ℝ=> F i t []) atTop ( 𝓝 ( blade F i ) )
abbrev inlet (i:I): Vista P:= ⟨i,P.θ i,(Set.mem_Ici.mpr le_rfl)⟩
-- any Lease gives scalar pay unless rank-positive.C.
lemma scalar_bill (hp:Here false false K F A): paid K.price (fun i=> ‖scalar F i‖) A:= by obtain ⟨C,hC,k,hP⟩:=hp ℝ [] (fun u=>Bool.noConfusion u) (fun u=> Bool.noConfusion u) |>.norm_cost; refine ⟨ C,hC,k,fun i=>?_⟩; convert hP i 0 trivial using 1; rfl; simp [pitch, fieldDim,Scale.full, Scale.weight] -- β lerp
abbrev tarB (P:Geo I)(i:I):= habitat P i*(1+P.θ i)
abbrev moneyX (P:Geo I)(x:I→ℝ)(d k:ℕ)(i:I):= tarB P i ^ k * exp (( - (d:ℝ) - x i )*P.θ i)
abbrev title (P:Geo I)(x:ℝ)(d:ℕ)(F:I→ℂ): Prop:= ∃ C:ℝ,0<C∧∃ k:ℕ,∀ i,‖F i‖ ≤ C*moneyX P (fun _=>x) d k i
lemma vested (p:Vista P): ( West P ).price.basic p=P.habitat p.1*(1+tstart p) := by change _*(1+|tstart p|)=_; rw [abs_of_nonneg ( le_trans ( P.room p.1 ) ( paidW p))]
local notation "Ψ"=> West P
abbrev move (p:Vista P)(i:ℝ)(h:tstart p < i): Vista P:= ⟨p.fst,i,Set.mem_Ici.mpr ( (paidW p).trans h.le )⟩
def Ψc (p:Vista P)(i:ℝ): ℝ:= exp (-(eps_gain/2)*(i-tstart p))
lemma ζγ {p:Vista P}: Ψc p=fun i=>exp ( ( eps_gain/2)*tstart p )* exp (-(eps_gain/2)*i):= funext fun i=> (by unfold Ψc; rw [ ← Real.exp_add ]; congr 1; ring )
lemma ζint (p:Vista P): IntegrableOn (Ψc p) ( Set.Ioi (tstart p)):= by rw [ζγ]; apply (integrableOn_exp_mul_Ioi (a:=-(eps_gain/2)) (by unfold eps_gain; norm_num) _).const_mul
lemma ζγint (p:Vista P): ∫ i in ( Set.Ioi (tstart p)),Ψc p i= (4:ℝ):= by rw [ζγ, integral_const_mul, integral_exp_mul_Ioi (by norm_num [eps_gain]),neg_mul,exp_neg]; field_simp; ring_nf
lemma vistaJ (p:Vista P)(v:ℝ)(hv:tstart p<v): (West P).price.basic ( move p v hv ) ≤ (West P).price.basic p*(1+(v-tstart p)):= by rw [vested,vested,mul_assoc]; dsimp only [move,tstart]; apply mul_le_mul_of_nonneg_left _ ( show 0≤P.habitat _ from by unfold habitat; positivity ); change 1+v≤ (1+tstart p)*(1+(v-tstart p)); nlinarith [le_trans ( P.room p.1 ) ( paidW p )]
lemma rateR (p:Vista P)(t:ℝ)(ht:tstart p<t): far P d x ( move p t ht )= far P d x p * exp ( - eps_gain*(t-tstart p) ):= by simp only [far,ace,sale,tstart]; simp only [ ← exp_add ]; congr 1; ring
lemma O_int (h:Fed P d x H)(hp:Stroll false H): ∃ C:ℝ,0<C ∧ ∃ k:ℕ, ∀ p:Vista P, IntegrableOn (fun i:ℝ=> H p.1 i []) ( Set.Ioi (tstart p)) ∧ ‖∫ i in Set.Ioi (tstart p), H p.1 i []‖ ≤ C*(West P).price.basic p^k*far P d x p := by
   obtain ⟨C,hC,k,hX⟩:= scalar_bill ( K:=West P ) h; obtain ⟨b,hb,hL⟩:= Belt.capped p_gain k; refine ⟨4*C*b,by positivity,k,fun p=>?_⟩; let f i:= H p.1 i []; let B:=(West P).price.basic; let A:= C*(B p)^k*far P d x p; have hs:= FarBasis P d x; have ht i:0<B i:= (West P).price.basic_pos _; have hu:=hs p; have he:0≤ A:= by unfold A; have hh:=ht p; positivity
   let μ:= volume.restrict ( Set.Ioi ( tstart p ) ); let q (t:ℝ) := A*b* Ψc p t; have hz:Integrable q μ:= ( ζint p ).const_mul _; have h0 : ∀ᵐ t ∂μ,‖f t‖ ≤ q t := by
       filter_upwards [ show ∀ᵐ x ∂μ, tstart p<x from ae_restrict_mem measurableSet_Ioi ] with t hP; let v:= move p t hP; have hv:= hX v; apply hv.trans; obtain hV:=hs v; calc
          _ ≤ C*( B p*(1+ (t-tstart p)) )^k* far P d x v:= by
             gcongr; · apply (ht ( move p t hP ) ).le
             exact vistaJ ..
          _ = A*((1+(t-tstart p))^k * exp (-(eps_gain)*(t-tstart p))) := by rw [rateR,mul_pow]; unfold A; ring
          _ ≤ q t:= by unfold q Ψc; rw [mul_assoc A b]; exact mul_le_mul_of_nonneg_left ( hL _ ( sub_nonneg.mpr hP.le )) he
   have hw: Integrable f μ:= hz.mono' (hp p.1 [] (fun h=>Bool.noConfusion h)|>.aestronglyMeasurable ) h0; refine ⟨hw,( norm_integral_le_integral_norm f|>.trans ( integral_mono_ae hw.norm hz h0 ))|>.trans_eq ?_⟩; unfold μ q; rw [integral_const_mul, ζγint]; unfold A B; ring
lemma saleable (hp:Fits false F H)(he:Fed P d x H): (∀ i, Allow F i ) ∧ paid (West P).price (fun p=> ‖blade F p.1 - scalar F p‖ ) ( far P d x ):= by
    obtain ⟨C,hC,k,hk⟩:= O_int he hp.stroll; have hu (i:I): Allow F i:= tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (fun t _=> hp.pace i [] (fun u=>Bool.noConfusion u) t) ( hk (inlet ( P:=P ) i )|>.1 ); refine ⟨ hu, C,hC,k,fun i=>?_⟩; obtain ht:= integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _=> hp.pace i.1 [] (fun h=>Bool.noConfusion h) t ) ( hk i|>.1 ) ( hu i.1 ); dsimp only [scalar]; rw [ ← ht ]; exact hk i|>.2
end YM.MS.Vane
