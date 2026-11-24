import YM.OPE.Compatible.Nectar.Anther
/-! # Ad and launch facts -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor WithLp
open scoped Topology BigOperators Classical
variable {r d m n:ℕ}{c:ℝ}{V I W:Type*}{G:Gauge}
namespace Script
open Page
-- whole interpretation colors
abbrev hue {G:Gauge}{n:Side} (g:G.El)(v:deck (Shade G) n):deck (Shade G) n:=fun p=> G.adjoint g (toLp 2 (fun t=> v (p.1,p.2.1,t))) p.2.2
abbrev painted {G:Gauge}(p:Script (Shade G) r):Prop:=∀ n:Side,∀ v: Fin r→ deck (Shade G) n,∀ u:G.El,scribe (0:Site n) p (fun i=> hue u (v i))=scribe 0 p v
lemma fromHue {g:G.El}{n:Side}(v:deck (Shade G) n): unfoldX (hue g v)=plumeX g (unfoldX v):=rfl
lemma hueXreal {F:I→Side}{f:Filter I}{x:∀ j:I, deck (Shade G) (F j)}{v:fieldX (Shade G)}(g:G.El)(h:Realized F f v x d): Realized F f (plumeX g v) (fun j=> hue g (x j)) d:=by
    let u(a:Axis)(v:fieldX (Shade G))(b:Cover):G.Color:= heal G a v b; let e:=EuclideanSpace.basisFun G.ColorIndex ℝ
    let w(i j:G.ColorIndex):ℝ:=chin j (G.adjoint g (e i)); have he(p:fieldX (Shade G))(b: Cover×Shade G): plumeX g p b= ∑ t,p (b.1,b.2.1,t)*w t b.2.2:=by
       let x:=u b.2.1 p b.1; change chin b.2.2 (G.adjoint g x)=_; nth_rw 1 [← e.sum_repr x]; rw [map_sum,map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul,map_smul]; rfl -- e
    constructor
    · obtain ⟨b,hb,H⟩:=h.Once; let C:=∑ i,∑ j,‖w i j‖; have hv:0≤C:=sum_nonneg fun i _=>sum_nonneg fun j _=>norm_nonneg _
      refine ⟨b*C,by positivity,fun i p=>?_⟩; rw [fromHue,he]; apply (norm_sum_le ..).trans; let A:= b*poise d p.1; have ht:0 ≤ A:=by unfold A poise; positivity
      have hx(j:G.ColorIndex):‖unfoldX (x i) (p.1,p.2.1,j)*w j p.2.2‖ ≤ A*(∑ t,‖w j t‖):=by
          rw [norm_mul]; apply (mul_le_mul_of_nonneg_right (H i (p.1,p.2.1,j)) (norm_nonneg _)).trans; exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _=>norm_nonneg (w j i)) (mem_univ _)) ht
      apply (sum_le_sum (fun i _=> hx i)).trans; rw [← Finset.mul_sum]; unfold A C; exact le_of_eq (by ring)
    intro j; change Tendsto (fun i=> plumeX g (unfoldX (x i)) j) _ _; simp_rw [he]; apply tendsto_finsetSum univ; exact fun i _=> (h.Onset _).mul_const _
lemma script_color {p:Script (Shade G) r}(hp:soot m p c)(h:p.painted) (g:G.El){v:Fin r→fieldX (Shade G)}{d:Fin r→ℕ}(hx:Glob v d)(hk:∑ i,d i ≤ m): wholeX p (fun i=>plumeX g (v i))=wholeX p v:=by
    let x(j:ℕ)(i):= closeX (v i) (epochX j); have he(i):Realized epochX atTop (v i) (fun j=> x j i) (d i):=received (tendsto_add_atTop_nat 1) (hx i)
    exact tendsto_nhds_unique_of_eventuallyEq (keepX hp (fun j i=>hue g (x j i)) (fun i=>hueXreal g (he i)) hk) (keepX hp x he hk) (Eventually.of_forall fun j=>h ..)
lemma sortedX {p:Script V r}(hp:p.sorted)(v: Fin r→fieldX V)(s:Equiv.Perm (Fin r)):wholeX p (v∘s)=wholeX p v:=by
   let E:Page V r≃Page V r:=Equiv.arrowCongr s (Equiv.refl _); unfold wholeX; nth_rw 2 [← E.tsum_eq]; apply tsum_congr; intro x
   rw [← (show p x=p (E x) from (congr_arg p (E.symm_apply_apply x).symm).trans (congr_fun (hp s) (E x))), wordX, wordX]; apply congr_arg (p x * ·); change (∏ i,v (s i) _)=∏ i,v i _; rw [← Equiv.prod_comp s (fun i=> v i ((E x) i))]; exact prod_congr rfl fun i _=>by rw [show E x (s i)=x i by change x (s.symm (s i))=_; rw [s.symm_apply_apply]]
end Script
end YM.OPE.Flume
