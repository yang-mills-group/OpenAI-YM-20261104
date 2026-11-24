import YM.AlbaMS.Odom.Bill

/-! Transfer before considering Stamp. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Odom.Book
open Set Function Filter Gauge NormedSpace MeasureTheory LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Coil Inlay Inlay.Net Lattice
variable {G:Gauge} {V I W J R L : Type*}[Fintype V][Fintype W][Fintype I][Fintype J]{Ω:Net V I}{H:Net W J}{x:ℝ}
-- Luster weighted pull through global relation. price query not yet authorized. Allows choosing a different chart? here no.
noncomputable def hoist (F: Book Ω G)(x:ℝ)(S:Receipt G Ω H): Book H G:= by
  let Wt:=S.honor F.toLuster
  have hv: fromWax Wt.integrand= (F.toLuster.caseG.val ∘ S.inkmap.toContinuousLinearMap):=funext fun y=> congr_arg F.integrand (S.shineReact y)
  let U : Luster H G:= ⟨fun x'=> x* Wt.integrand x', Wt.smooth.const_smul x, fun a b=> congr_arg (x*·) (Wt.solid a b) ⟩
  have ht : U.caseG.val=x • fromWax Wt.integrand:=rfl
  refine ⟨U,F.patch,F.paid, ?_,?_⟩
  · rw [ht,hv]; change x • F.toLuster.caseG.val (S.inkmap 0)=_; rw [map_zero,F.val0,smul_zero]
  rw [ht,fderiv_const_smul (Wt.smooth.differentiableAt (by simp)), hv, fderiv_comp _ (by rw [map_zero]; exact F.toLuster.smooth.differentiableAt (by simp)) S.inkmap.toContinuousLinearMap.differentiableAt, map_zero,F.slope]; simp

structure Unify (F : Book Ω G)(U : Book H G) (S:Receipt G Ω H)(x:ℝ) : Prop extends Receipt.Accord x S F.toLuster U.toLuster where
  patchEq : U.patch=F.patch
namespace Unify
variable {F:Book Ω G}{U:Book H G}{S:Receipt G Ω H}[CommRing R](P:Tune R)(h:Unify F U S x)
include h
lemma file : U.main=x • S.track F.main:= h.toAccord.adorned
lemma scent : U.ash=x • S.track F.ash:=by unfold Book.ash; have H:= Receipt.Accord.memory (P:=F.patch) (G:=G) h.toAccord.toMeets F.paid; convert H using 3 ; exact h.patchEq
lemma freight : U.charter P=P.D x • P.crossT S (F.charter P):=by unfold Book.charter Tune.fuelT; rw [h.file,h.scent,P.up_smul,P.up_smul,map_sub, P.commute,P.commute,smul_sub] -- congr
lemma fountain : U.fair P = P.D x • P.crossT S (F.fair P):=by
  unfold fair first; rw [h.file]; have he : Tune.kinetic P.a P.ha (x • S.track F.main)=x • S.track (Tune.kinetic P.a P.ha F.main):=by rw [Tune.kinetic_cross]; unfold Tune.kinetic; rw [map_smul,map_smul]
  rw [he,Wind_smul]; exact congr_arg (P.D x • ·) (shot_wind P.D (P.steer S))
lemma feels : U.stim P=P.D x • P.crossT S (F.stim P):=by rw [stim,stim,map_sub,smul_sub,h.freight P,h.fountain P]
end Unify
lemma unity (F:Book Ω G)(x:ℝ)(S:Receipt G Ω H)(h:Receipt.Meets S x): Unify F (hoist F x S) S x:=by refine ⟨?_, rfl⟩; exact ⟨h,fun _=>rfl⟩
variable {n:Side}(c:G.El)(s:Signed)(x:Site n)
lemma parade (A:Precision.ChartRatio G)(hp:Precision.LocalRatio A): Unify (Rack G n A hp) (Rack G n A hp) (conduit s x c) 1:= ⟨amphora s x c,rfl⟩
end YM.MSBar.Odom.Book
