import YM.X.Stems.Line
import YM.X.Clear.Null
import YM.Pert.Fourier.Source
/-!
# Exact orbit water and torus direct-link. For replacement at any pure horizon.
Compare Curl along cut for first jets, *all* link covariance phases independent afterwards.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Hinge
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Next.Rank Normal MvPolynomial
open Feyn Gauge LatticePT PertExtension.Orb Chart Stems PertExtension.Series.Tested Finset
open Pert.Orb (formElem covar image takeDiv gZ positiveLinks wilson Potential form formL curL dLin bridgeEquiv)
open scoped Topology ContDiff BigOperators Classical RealInnerProductSpace
variable {G:Gauge} {n:Side} (he:Even n.val) {o : Site n} (x : Potential G n)
local notation "E"=> Potential G n
local notation "J"=> Jam n G
local notation "N"=> Module.Dual ℝ E
local notation "P"=> (Feyn.cost (n:=n) (G:=G))
set_option quotPrecheck false
local notation "T"=> (Feyn.cut (n:=n) (G:=G)).toLinearMap

open Finsupp
include he
lemma nuance {v:E}(H: Feyn.cut v=0)(h : dLin v=0): v=0:= by
   have ht:= cut_pow he v; rw [H] at ht
   have hz (x:Site n): takeDiv x v=0:= congr_fun (congr_arg Subtype.val h) x
   simp_rw [Feyn.glows,hz,inner_zero_left,Finset.sum_const_zero] at ht
   rw [show score (0:Dir G n) 0=0 from ?_, zero_div,mul_zero,add_zero] at ht
   · by_contra hv; exact (Pert.Orb.form_pos hv).ne' ht
   unfold score; simp
lemma cut_split : x=pad he (cut x) + gZ ((bridgeEquiv G n).symm (dLin x)):= by
   apply sub_eq_zero.mp (nuance he _ _); · rw [map_sub,map_add,cut_pad,cut_grad he,add_zero,sub_self]
   rw [map_sub,map_add,pad_div,zero_add,show dLin (gZ _)=_ from (bridgeEquiv G n).apply_symm_apply (dLin x),sub_self]
lemma cut_curl (o:Site n)(s:Atom G) : Slope.leg o s ∘ₗ T = linearCombination ℝ (pier ∘ place o) (iris s):= by
   apply LinearMap.ext; intro v
   let b:=s.1.plaq.val; let a:= s.1.offset;let p:=wrap n a + o; let k:=s.2
   unfold Slope.leg
   rw [LinearMap.comp_apply,Projection.signal_eq,LatticePT.colorBasis,EuclideanSpace.basisFun_inner]
   let c:= (saddle (G:=G) he).P; let u:=cut (n:=n) (G:=G) v; let A:= Pert.Orb.curL p b.1 b.2 (fits he u)
   have heq : letterPolar (Slope.address o s.1) u=A := by change PertExtension.Orb.Curl (variation u) p b.1 b.2= Pert.Orb.cur (variation u) p b.1 b.2; unfold PertExtension.Orb.Curl Pert.Orb.cur; abel
   have hA : A=Pert.Orb.curL p b.1 b.2 v:= by
      conv_rhs=> rw [cut_split he v]
      rw [map_add, curl_grad,add_zero,Feyn.pad, LinearMap.sub_apply,map_sub, LinearMap.comp_apply,curl_grad,sub_zero]
   change _ = LinearMap.applyₗ v (linearCombination ℝ _ (iris s)); rw [LinearMap.map_finsupp_linearCombination]; change (letterPolar (Slope.address o s.1) u) s.2= _; rw [heq,hA]; change _=linearCombination ℝ (text (peat o v)) (Stems.iris s); rw [iris,arc_eq]
   apply congr_arg (fun q:G.Color=> q s.2); change Pert.Orb.cur v.val p b.1 b.2=curl (peat o v) a b.1 b.2; simp [peat,expandAt,p,curl,Pert.Orb.cur,add_right_comm]

lemma marks_wick (o:Site n)(a b: Atom G): (saddle he).wick (Slope.leg o a) (Slope.leg o b)=(P).wick (linearCombination ℝ (pier ∘ place o) (iris a)) (linearCombination ℝ (pier ∘ place o) (iris b)) := by rw [← cut_curl he,← cut_curl he]; unfold GaussianScore.Law.wick; change _= (Slope.leg o b) ((T) ((P).inverse _)); rw [tangent_proj (P) (saddle he) (T) (pad he) (LinearMap.ext (fun x=>cut_pad he x)) (pad_fit he)]

omit he
lemma com_read (x: Hair G→ℝ)(a:Hair G→₀ ℝ) : linearCombination ℂ (Complex.ofReal ∘ x) (com a)=(linearCombination ℝ x a:ℂ):= by
   induction a using Finsupp.induction_linear with
   | zero=>simp [com]
   | add i j hi hj=> unfold com at *; rw [_root_.map_add,_root_.map_add,_root_.map_add,hi,hj,Complex.ofReal_add]
   | single k c=> rw [com_six,linearCombination_single,linearCombination_single]; exact Eq.symm (Complex.ofReal_mul ..)
def scopedK (K:Symmetric J)(o: Site n):Symmetric (Hair G):= scope (fun x=> Finsupp.single (place o x) 1) K
def via (K:Symmetric J)(o: Site n):Symmetric (Atom G):= scope (com ∘ iris) (scopedK K o)
lemma via_val (o: Site n) (a b: Atom G) : (via water o).cov a b=(↑((P).wick (linearCombination ℝ (pier ∘ place o) (iris a)) (linearCombination ℝ (pier ∘ place o) (iris b))):ℂ) := by
   let V:= scopedK (water (G:=G)) o; let q:= linearCombination ℝ (pier ∘ place (G:=G) o); let x:=iris a; let y:=iris b; let f:=linearCombination ℂ V.cov (com x); have hr (i j:Hair G): V.cov i j=(↑((P).wick (pier (place o i)) (pier (place o j))):ℂ):= match_name (place o) _ i j
   have hh (i:Hair G): f i= (↑((P).wick (q x) (pier (place o i))):ℂ):= by
      unfold f; let u j:= ((P).wick (pier (place o j)) (pier (place o i))) ; change (LinearMap.proj i : (Hair G→ℂ) →ₗ[ℂ] ℂ) (linearCombination ℂ V.cov (com x))=_; rw [LinearMap.map_finsupp_linearCombination, ← show linearCombination ℂ (Complex.ofReal ∘ u) (com x)=linearCombination ℂ _ _ from ?_, com_read]; swap; · exact congr_arg (fun q=> linearCombination ℂ q (com x)) (show Complex.ofReal ∘ u =_ from funext (fun j=> (hr j i).symm))
      exact congr_arg Complex.ofReal (LinearMap.map_finsupp_linearCombination ((pier (place o i)).comp ((P).inverse)) (g:=pier ∘ place o) x).symm -- args
   unfold via scope treats; dsimp only [Function.comp_apply];rw [show linearCombination ℂ _ (com (iris a))= _ from funext hh]; exact (com_read _ y).trans (congr_arg Complex.ofReal (LinearMap.map_finsupp_linearCombination (LinearMap.applyₗ ((P).inverse (q x)): N →ₗ[ℝ] ℝ) (g:=pier ∘ place o) y).symm)
include he
lemma agrees (y:Cover)(a b:Atom G) : (via water (wrap n y)).cov a b=(↑(LatticePT.echo n y y (atAddress a) (atAddress b)):ℂ):= by rw [(via _ _).symm,via_val,← marks_wick he,Slope.cov he]
end YM.PositionX.Hinge
