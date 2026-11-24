import YM.MS.Rake.Stone
/-!
# Low0 budget closure for joins.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake.Geo
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook
open scoped Topology ContDiff Interval
variable {I J:Type}{G: Gauge}{b c:Bool}{x:I→QP}(P: Geo I){K L:Planet G I}{F H: Glade G I}
local notation "Ψ"=> east P b
variable (h:Stage K L P b)
include h
omit h in lemma Coherent : Cohere planeF := ⟨⟨5,Tall ( Job.single Unit ) 5 (by omega)|>.integrable ()⟩⟩
lemma ready : Duty ( birthTar P ) ( K:=east P b ) (sailP (fun _=>planeF) L) := control (m:=fun (_:I)=>planeF) (born P G b) (fun _=> Coherent) h.pool (fun i j=> (h.well i j).monotone fun k=>mul_le_mul_of_nonneg_left (lampC P k) (length_p ..)) (fun E _=> tom (Ψ).price 5 (by omega)) (Tall _ 5 (by omega))
abbrev Came (P:Geo I)(b:Bool): Glade G I→Prop:= fun F=>CabinF (K:=east P b) ( birthTar P ) F ∧ collect F
abbrev Tip (P:Geo I)(b c:Bool)(h:ℕ)(F:Glade G I): Prop:= collect F ∧ Warm F c∧ Here c true ( east P b ) F (rateS ( east P b ) h)
variable {P}
lemma cone (hp:Came P b H)(ht:Tip P b true 4 F): Came P b (fun i t=> tree parity ( K i t ) ( F i t ) ( H i t )):= by
    refine ⟨⟨?_, walk_tree h.pinC ht.2.1 hp.1.mood⟩,collect_tree K ht.1 hp.2⟩; intro i; apply Lease.sticks ( trunks h.market ht.2.2 (Lease.highp (hp.1.pick i)) (fun i=>zero_le_one) (rateC _ _ ) ( tollB P i b )); intro z; simp only [positive,Pi.mul_apply, Pi.one_apply,one_mul, rateS ]; rw [← mul_assoc,zpow_neg,zpow_natCast, mul_inv_cancel₀ (pow_ne_zero 4 ( (Ψ).price.pos z|>.ne' )),one_mul]; -- fix inverse
structure CoverSep (P:Geo I)(x:I→QP) : Prop where
    full: ∃ C:ℝ,0<C∧∀ i, ‖x i‖ ≤ C * P.roots i
    floor: ∃ C:ℝ,0<C∧∀ i,C*P.roots i≤‖x i‖
omit h in
lemma money (k n m:ℕ):∃ l:ℕ,∀ i:(Ψ).time, lamp b i*( rateS Ψ n i*rateS Ψ m i )*( (Ψ).price.length i/P.roots i.1)^l ≤ birthTar P k i:= by
    cases b
    case true=> refine ⟨k,fun i=>?_⟩; simp only [ lamp,rateS, if_true,unitE,one_zpow, birthTar, Real.exp_neg, one_mul,one_div,roots]; rw [mul_one] -- Rf
    case false=>
       refine ⟨ k + (n+m+1),fun p=>?_⟩; simp only [ lamp,Bool.false_eq_true, ↓reduceIte, one_mul,rateS,birthTar,coldE,roots,div_pow,Real.exp_neg]; let t:= tstart p; let L:= exp ( tstart p ); let U:=exp ( P.θ p.1 ); have hu:1≤U:= Real.one_le_exp (P.room _); have h':L≤1:= seasonE P p; have hL:L>0:= exp_pos _; have ht: 0<U:=exp_pos _;
       change L^( -(n:ℤ))*( L^( -(m:ℤ))) * (L ^ _ / U^_ ) ≤ _; rw [zpow_neg,zpow_neg,zpow_natCast,zpow_natCast]; calc
          _ = L * U⁻¹^k * (L^k * ( U⁻¹ )^(n+m+1)):= by simp only [pow_add,pow_one,inv_pow]; field_simp
          _ ≤ _:= mul_le_of_le_one_right (by positivity) (mul_le_one₀ (pow_le_one₀ hL.le h') ( by positivity ) ( pow_le_one₀ (by positivity) ( inv_le_one_of_one_le₀ hu))) -- syntax R.h
lemma touch (hz: CoverSep P x){n m:ℕ}(he: Tip P b false n F)(hx:Tip P b false m H): Came P b ( fun i t=> Cabin (x i) ( L i t ) planeF ( F i t ) ( H i t )):= by
    refine ⟨⟨?_, warmJoin (fun _=>Coherent) h.pool he.2.1 hx.2.1⟩, collect_join _ L he.1 hx.1⟩; intro k; obtain ⟨l,hM⟩:= money (b:=b) ( P:=P ) k n m; obtain ⟨⟨D,hD,hP⟩, C,hC,H⟩:=hz; refine Lease.sticks ( PulseQ ( v:=fun i=>P.roots i.1 ) ( A:=x∘ Sigma.fst ) h.well he.2.2 hx.2.2 ( airLamp _ _ ) (rateC _ _ ) (rateC _ _ ) (fun _=>exp_pos _) (fun i=> (H i.1)) ( rightB P ) ⟨ _,hD,0,fun i=>by rw [ pow_zero,mul_one ]; exact hP _⟩ hC l ) hM
-- widen Came to a Tip-any. shape estimates preserved.S
omit h in
lemma tipby (hp: Came P b F)(j:ℕ): Tip P b false j F:= by refine ⟨hp.2,hp.1.mood,Lease.sticks ( ( hp.1.pick 0).highp ) ?_⟩; exact fun p=> ( lowerB P p 0 ).trans ( rank_e P p j )
omit h in
lemma seamount {S:Finset J}{F:J→ Glade G I}(hp:∀ i∈ S,Came P b (F i)): Came P b (∑ i∈ S, F i):= by refine ⟨ ⟨fun k=> He_here S (fun i hi=>( hp i hi ).1.pick k) (tollB _ _ _), warm_sum S (fun i h=>( hp i h).1.mood ) ⟩, collected S (fun i h=>( hp i h ).2 )⟩
end YM.MS.Rake.Geo
