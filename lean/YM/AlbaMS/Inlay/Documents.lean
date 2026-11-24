import YM.AlbaMS.Inlay.Devolve

/-! # Fragments transmit through lenses. include L weighting. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Inlay.Net
open Set Function Filter Gauge NormedSpace MeasureTheory LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Coil
variable {V W I J R : Type*}{G:Gauge} [Fintype V][Fintype W][Fintype I][Fintype J]
variable (Ω :Net V I)
def click (e:V): Heave G V I ℝ:= ∑ i:G.ColorIndex, K ℝ (e,i) * beam Ω.chat (e,i)
def spinS (x:I):Heave G V I ℝ:=∑ j:G.ColorIndex,L ℝ (x,j)* rod (grit G I) (x,j)
def sinG {P:Precision.ChartRatio G} (hp:Precision.LocalRatio P) (e:V) : Heave G V I ℝ:= bare ⟨fun x=>stud P (x e), ContDiffAt.comp (g:=stud P) (f:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : V=> G.Color) e) _ (Quill.lit hp _ (Metric.mem_ball_self hp.patch)) (contDiffAt_apply ..)⟩
lemma whole (F: Grove (ink G V)): superb (grit G I) Ω.chat (bare F)= bare F+(∑ v:V,click Ω v)-∑ i:I,spinS i:=by unfold superb feeds click spinS; rw [Fintype.sum_prod_type (f:=fun i:Flit G V=> K ℝ i *_), Fintype.sum_prod_type (f:=fun i:Flit G I=>L ℝ i*_) ]
omit [Fintype I] in
lemma noted {P:Precision.ChartRatio G}(hp:Precision.LocalRatio P): bare (I:=I) (fragrant (V:=V) hp)=∑ v:V,sinG hp v:=by
  change _ = ∑ v:V, (pathof G V I).shine _; unfold bare; refine (pathof G V I).flash _ _ _ ?_; filter_upwards with x; rw [Finset.sum_apply]; rfl

namespace Receipt
variable {Ω}{H:Net W J}(u:Receipt G Ω H)
--- signed orthogonal receipt
omit [Fintype V] [Fintype I] [Fintype W] [Fintype J] in
private lemma basic_sums (T:G.ColorIndex→ Heave G W J ℝ)(S:G.ColorIndex→ Heave G W J ℝ)(v:Bool) :
    (∑ i:G.ColorIndex, (∑ j:G.ColorIndex,sting v (W_adj u.color i j) • T j)*(∑ j:G.ColorIndex, sting v (W_adj u.color i j) • S j))=∑ j:G.ColorIndex, T j* S j:=by
  let Q:=W_adj u.color
  have he (i j:G.ColorIndex) : (∑ a:G.ColorIndex, Q a i * Q a j) = if i=j then 1 else 0:= by
    change (Q.transpose*Q) i j=_; rw [show Q.transpose*Q=1 from adj_ortho u.color, Matrix.one_apply]
  have hu (a b:ℝ): sting v a* sting v b=a*b:=by cases v<;>simp
  simp_rw [Finset.sum_mul, Finset.mul_sum,smul_mul_assoc,mul_smul_comm,smul_smul,hu]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [Finset.sum_comm]; change (∑ j:G.ColorIndex, ∑ a:G.ColorIndex, (Q a i*Q a j) • (T i*S j))=_; simp_rw [← Finset.sum_smul,he]; simp [ite_smul]
omit [Fintype V] [Fintype I] [Fintype J] in
private lemma farlink (T : Flit G W→Heave G W J ℝ)(x:V)(i:G.ColorIndex):
    (∑ j:Flit G W,u.φ (x,i) j • T j)=∑ j:G.ColorIndex,sting (u.flip x) (W_adj u.color i j) • T (u.parcel x,j):=by rw [Fintype.sum_prod_type, Finset.sum_eq_single (u.parcel x)]; simp_rw [u.phi_rule]; simp; intro j _ hj; simp_rw [u.phi_rule]; simp [Ne.symm hj]; simp
omit [Fintype V] [Fintype W] [Fintype I] in
private lemma farghost (T : Flit G J→Heave G W J ℝ)(x:I)(i:G.ColorIndex):
    (∑ j:Flit G J,u.ε (x,i) j • T j)=(u.node x).elim 0 (fun y=>∑ j:G.ColorIndex,W_adj u.color i j • T (y,j)):=by
  simp_rw [u.eps_rule]; cases h:u.node x with | none=> simp| some v=>
    rw [Fintype.sum_prod_type, Finset.sum_eq_single v]; simp; intro j _ hj; simp [Ne.symm hj]; simp
lemma transmitting (e:V): u.track (click Ω (G:=G) e)=click H (u.parcel e):=by simp_rw [click,map_sum,u.times,u.passK,u.forwarding,u.farlink]; exact basic_sums .. -- explicit args
lemma transpire (x:I): u.track (spinS (G:=G) x) = u.rate x • (u.node x).elim 0 (fun j=>spinS j):=by
  unfold spinS; rw [map_sum]; simp_rw [u.times,u.passL,u.riding, ← Finset.smul_sum, u.farghost,smul_mul_assoc, ← Finset.smul_sum]; congr 1; cases u.node x; simp; next j=> exact basic_sums u (fun i=> L ℝ (j,i)) (fun i=> rod _ (j,i)) false
omit [Fintype J] in
lemma smiling {P:Precision.ChartRatio G}(hp:Precision.LocalRatio P) (x:V): u.track (sinG hp x)=sinG hp (u.parcel x):=by
  unfold sinG; rw [u.action]; unfold bare; refine (pathof G W J).shadow _ _ ?_
  let L:=u.inkmap.toContinuousLinearMap; let C:ink G W→L[ℝ] G.Color:=ContinuousLinearMap.proj (R:=ℝ) (u.parcel x); let B:= (G.adjoint u.color).toContinuousLinearMap.comp C; let D: ink G W→L[ℝ] G.Color:=(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:V=>G.Color) x).comp L
  have he (T: ink G W→L[ℝ] G.Color): ∀ᶠ y:ink G W in 𝓝 0, Quill (T y) ∧ T y∈Metric.ball 0 P.radius:= by have hv:=T.continuous.tendsto (0:ink G W); rw [map_zero] at hv; exact hv.eventually ((quill G).and (show ∀ᶠ y: G.Color in 𝓝 0,y∈Metric.ball 0 P.radius from Metric.ball_mem_nhds _ hp.patch))
  filter_upwards [he C,he B, he D] with y ⟨h,hc⟩ ⟨ht,hb⟩ ⟨hu,hd⟩; change stud P (D y)=stud P (C y)
  rw [stud, stud, h.price hp hc, hu.price hp hd]; congr 1
  have hz : D y=sting (u.flip x) (B y):= u.inkmap_ap y x
  have hp := Quill.mod u.color h ht; rw [show LinearMap.det (M (C y))=_ from hp.symm]; cases hx:u.flip x <;> simp only [hx,sting_true,sting_false] at hz; rw [hz]; rfl; rw [hz]; exact Quill.misty ht (hz ▸ hu)

-- induced gauge-group action -- orientation on links also makes patch core eligible.
def react (U:W→G.El)(v:V): G.El:= u.color * (if u.flip v then (U (u.parcel v))⁻¹ else U (u.parcel v)) * u.color⁻¹
def iris (z:J→G.El)(i:I): G.El:= u.color * boat (u.node i) z * u.color⁻¹
omit [Fintype V] [Fintype I] [Fintype W] [Fintype J] in
lemma concert (z)(i:Option I): boat i (u.iris z)=u.color*boat (i.bind u.node) z*u.color⁻¹:=by cases i<;> simp [boat,iris]
omit [Fintype V] [Fintype I] [Fintype W] [Fintype J] in
lemma shineReact (X : ink G W): u.react (G.lieExp ∘ X)= G.lieExp ∘ u.inkmap X:=by
  ext1 v; rw [Function.comp_apply,u.inkmap_ap,react]; cases u.flip v <;> simp only [Bool.false_eq_true, ↓reduceIte,sting_true,sting_false,Function.comp_apply, Work.F03.exp_neg_color,exp_adjoint]; group
omit [Fintype V] [Fintype I] [Fintype W] [Fintype J] in
lemma homeReact (t:J→G.El)(U:W→G.El): Ω.home (u.iris t) (u.react U)= u.react (H.home t U):=by
  ext1 v; simp only [react, home]; rw [concert,concert,u.start,u.stop]; cases u.flip v <;> simp only [↓reduceIte,Bool.false_eq_true] <;> group

def honor (F : Luster Ω G): Luster H G where
  integrand W:=F.integrand (u.react W)
  smooth:= by
    unfold Queue; have he:= u.shineReact; unfold fromWax at *; simp_rw [he]; exact ContDiffAt.comp (g:=F.caseG.val) (f:=u.inkmap.toContinuousLinearMap) 0 (by rw [map_zero]; exact F.caseG.2) u.inkmap.toContinuousLinearMap.contDiff.contDiffAt
  solid U t:= (congr_arg F.integrand (u.homeReact t U).symm).trans (F.solid _ _)
omit [Fintype J] in
lemma honor_track (F:Luster Ω G): bare (u.honor F).caseG=u.track (bare F.caseG):=by
  rw [u.action]; unfold bare; refine (pathof G W J).shadow _ _ ?_; filter_upwards with x; exact congr_arg F.integrand (u.shineReact x)
end Receipt
end YM.MSBar.Inlay.Net
