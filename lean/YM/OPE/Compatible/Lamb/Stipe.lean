import YM.OPE.Compatible.Lamb.Reek
import YM.OPE.Compatible.Limn.Tart
/-!
# phase virage along TRUE beta; additive b difference rebase paid separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Zeph
open Function Filter Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree Push Push.AbsoluteSums Precision Matrix
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra GaussianScore Metric Limn
variable {G:Gauge}{c f:Side}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin Set
open PhysicalNext.Repeat.Aroma
open YM.AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate Sheets Radius.Model
open Woody Next.Free Finset Work.F03 Progress.StationaryScenes AnalyticNext.QuarticMatch.Local Cascade Rill Glass Coin
variable {t r R B b ε C k' R' t' t'' u:ℝ}{m:ℕ}
variable {S:StepData c f} {F: Forest S.ratio} {k:S.Choices}
local notation "Q" =>(Bid.Dir G c × AxisChart G F)
open Dew
section
variable (p:(Bid.Dir G c × AxisChart G F)→ℝ)(v:(Bid.Dir G c × AxisChart G F))
lemma firstY (hp:fderiv ℝ p 0=0)(t:ℝ): ∑ i∈ range 3,t^i*jet p i v=p 0+t^2*jet p 2 v:=by
       change ∑ i∈ Finset.range (2+1), t^i*jet p i v=p 0+t^2*jet p 2 v; simp only [sum_range_succ,sum_range_zero,zero_add,jet_zero,jetNull hp,pow_zero,one_mul,mul_zero,add_zero] -- name?
lemma secondY (hp:fderiv ℝ p 0=0)(t:ℝ): ∑ i∈range 5,t^i*jet p i v=(p 0+t^2*jet p 2 v)+t^3*jet p 3 v+t^4*jet p 4 v:=by rw [show 5=(3+1+1:ℕ) from rfl,sum_range_succ,sum_range_succ,firstY p v hp]
end
variable (S F)(k:S.Choices)(P: Rep G f)
local notation "U!"=> pane F k P.clip P.path
set_option quotPrecheck false
local notation "L!"=>(fun x:Q=> springF F P.path x.2)
variable (I:Seats F)(w: Bid.Dir G c)(v: AxisChart G F) {N:ChartRatio G}(hN: LocalRatio N)
local notation "KI"=>Keys G (I : Type)
abbrev VegaP (z:KI): Bid.Dir G c × AxisChart G F:=(w,v+stake I z)
abbrev haul (z: KI) := jet U! 2 (VegaP S F I w v z)
abbrev haze (z:KI) := -jet U! 3 (VegaP S F I w v z)
abbrev litter (N:ChartRatio G)(z:KI) := jet (feeX N (F:=↥I)) 2 z- jet U! 4 (VegaP S F I w v z)-jet L! 2 (VegaP S F I w v z)
variable {p q: Site f → (Bid.Dir G c ×AxisChart G F) →ℝ}
variable (h1:Pile S F r R t 5 (pane F k P.clip P.path) p)(h2:Pile S F r R' t 3 (fun x:(Bid.Dir G c × AxisChart G F)=>springF F P.path x.2) q)
variable (H:StackP N t' t'' u)
abbrev labor (t R R' u:ℝ)(X:Finset (Site f))(G:ℝ):= (R*(paying X G t)^5+R'*(paying X G t)^3)+(I.card:ℝ)*(u*G^3)
abbrev salary (t R R' u:ℝ)(X:Finset (Site f))(G:ℝ):=(R*(paying X G t)^3)+(I.card:ℝ)*(u*G^2)+R*(paying X G t)^4+R'*(paying X G t)^2
private lemma aket (u y z p q r k h a b:ℝ)(ht:0<ε): u+(-(ε⁻¹^2*(y-z))-(a-b))+p-(ε*(-q)+ε^2*(h-r-k))= -(ε⁻¹^2*(y-((z+ε^2*p)+ε^3*q+ε^4*r)))-(a-(b+ε^2*k))+(u-ε^2*h):=by field_simp; ring
include h1 h2 hN H
lemma salaryP (ht:0<t)(hz:0 ≤ R)(hz':0 ≤ R')(x:KI)(X:Finset (Site f))(hB:‖VegaP S F I w v x‖ ≤ B)(hs:ShadeQ S F (VegaP S F I w v x) X)(he:‖x‖ ≤ B)(hP:0<r):
      ‖haze S F k P I w v x‖+‖litter S F k P I w v N x‖ ≤ salary S F I t R R' u X B:=by
         have hY:0≤B:=(norm_nonneg _).trans he; let y:=VegaP S F I w v x; let p:=Glans X B t; have h'(i):= glansM (t:=t) hs hB i; have hp(i:ℕ)(hi:0 < i)(H':i ≤ 5): ‖jet U! i y‖ ≤ R*(paying X B t)^i:= (h1.atX y hP p (glansHi hY) h' i H').trans (mul_le_mul_of_nonneg_left (fundGlans X ht hY i hi) hz); have hz'': ‖jet L! 2 y‖≤ R'*(paying X B t)^2:= (h2.atX y hP p (glansHi hY) h' 2 (by decide)).trans (mul_le_mul_of_nonneg_left (fundGlans X ht hY 2 two_pos) hz');
         unfold haze litter; rw [norm_neg]; apply (add_le_add (hp 3 (by decide) (by decide)) ((norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add ((feeCapital hN H x (show 2 ≤ 3 from by decide)).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) he _) H.pays.1) (Nat.cast_nonneg _))) (hp _ (by decide) (by decide)))) hz''))).trans_eq; unfold salary; rw [Fintype.card_coe]; ring
lemma stipeT (ht:0<t)(hz:0≤R)(hz':0≤R')(hε:0<ε)(hB:ε*B<r)(hβ:P.beta= ε⁻¹^ (2:ℕ))(hx':fderiv ℝ U! 0=0)(hx:fderiv ℝ L! 0=0)(z:KI)(X:Finset (Site f))(hY: ‖VegaP S F I w v z‖ ≤ B)(hs:ShadeQ S F (VegaP S F I w v z) X)(he: ‖z‖ ≤ B)(hL:ε•z∈ ball 0 t') :
       ‖feeX N (ε • z) + ScoreV F I P k v w ε z + haul S F k P I w v z - (ε*haze S F k P I w v z+ε^2*litter S F k P I w v N z)‖ ≤ labor S F I t R R' u X B*ε^3:=by
           let f:=L!; let p:=U!; let x:=VegaP S F I w v z; let b:=paying X B t; let e:= p (ε •x)-((p 0+ε^2*jet p 2 x)+ε^3*jet p 3 x+ε^4*jet p 4 x); let v':= f (ε • x)-(f 0+ε^2*jet f 2 x); let k':=feeX N (ε•z)-ε^2*jet (feeX N) 2 z; have hz:‖e‖≤ R*b^5*ε^5:=by rw [show e=p (ε • x)-∑ i∈ range (4+1), ε^i*jet p i x from by erw [secondY p x hx']]; exact (sparsity h1 ht hz x X hs hY hε hB 4 (by decide)).1
           have hv : ‖v'‖ ≤ R'*b^3*ε^3:=by rw [show v'= f (ε • x)-∑ i∈range (2+1), ε^i * jet f i x from by erw [firstY f x hx]]; exact (sparsity h2 ht hz' x X hs hY hε hB 2 (by decide)).1
           have hy: ‖-(P.beta*e)‖≤ R*b^5*ε^3:=by rw [norm_neg,norm_mul,hβ,Real.norm_of_nonneg (by positivity)]; apply (mul_le_mul_of_nonneg_left hz (by positivity)).trans_eq; field_simp
           rw [show feeX N (ε • z) + ScoreV F I P k v w ε z +haul S F k P I w v z-(ε*haze S F k P I w v z+ε^2*litter S F k P I w v N z)=-(P.beta*e)-v'+k' from ?_]; apply (norm_add_le ..).trans ((add_le_add ((norm_sub_le ..).trans (add_le_add hy hv)) (feeTime hN H z hε hL he)).trans_eq ?_); rw [Fintype.card_coe]; unfold b labor; ring
           unfold ScoreV haul haze litter e v' k'; rw[hβ]; exact aket _ (p (ε • x)) _ _ _ _ _ _ (f (ε • x)) (f 0) hε
end YM.OPE.Zeph
