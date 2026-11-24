import YM.SchemeRG11.Saddle.Loads
import YM.PertExtension.BareChart
/-! Haar Jacobian, on arbitrary TREE orientation as well as positive serial convention. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.SchemeRG11.Sway
open scoped Classical ContDiff Topology Matrix.Norms.Frobenius
open Function Filter Lattice Pert.Orb PertExtension.Orb LocalH MeasureTheory Precision Push.Loops
variable {G:Gauge}{n:Side}
def theta(c:G.Color):G.Color→L[ℝ]G.Color:=fderiv ℝ (fun a=>delta (G.lieExp c) (G.lieExp a)) c
lemma theta_diff(c:G.Color):ContDiffAt ℝ ω (fun a=>delta (G.lieExp c) (G.lieExp a)) c:= delta_diff contDiffAt_const G.exp_jet.contDiffAt rfl
lemma theta_cost: ∀ᶠ c in 𝓝 (0:G.Color), cost (theta c)=spin G c:=by
 obtain ⟨P,R,hP⟩:=exists_haar (G:=G)
 filter_upwards [hP, Metric.ball_mem_nhds (0:G.Color) R.patch] with c hc he; exact (exp_delta_det R he).trans hc
lemma theta_steady: ∀ᶠ v:Potential G n in 𝓝 0, ∀ l:Pert.Orb.Links n, cost (theta (v.val l))=spin G (v.val l):=eventually_all.mpr fun l=> ((takeLink l).toContinuousLinearMap.continuous.continuousAt (x:=(0:Potential G n))).tendsto.eventually theta_cost
lemma theta_nz : ∀ᶠ v:Potential G n in 𝓝 0, ∀ l:Pert.Orb.Links n, Injective (theta (v.val l)):= by
 have h: ∀ᶠ c:G.Color in 𝓝 0, cost (theta c)>0:=by
    have hs: ContinuousAt (spin G) 0:= (spin_deriv G 0).continuousAt
    filter_upwards [theta_cost,hs.eventually_mem (Ioi_mem_nhds (by rw [spin_zero]; exact one_pos:0<spin G 0))] with x he hp
    rw [he];exact hp
 refine eventually_all.mpr fun l=> ((takeLink l).toContinuousLinearMap.continuous.continuousAt (x:=(0:Potential G n))).tendsto.eventually (p:=fun i:G.Color=> Injective (theta i)) (h.mono (fun i hi=> ?_))
 obtain ⟨e,he⟩:=cost_iso (theta i) hi.ne'; rw [← he]; exact e.injective
lemma theta_parity(c:G.Color):cost (theta (-c))=cost (theta c):=by
 let u:= G.lieExp c
 let L:= -drift u⁻¹
 let R:= - ContinuousLinearMap.id ℝ G.Color
 have hb: R c=-c:=by simp [R]
 let f(x:G.Color):= delta u (G.lieExp x)
 let g(x:G.Color):= delta (G.lieExp (-c)) (G.lieExp x)
 have hc: Tendsto (fun x=>L (f x)) (𝓝 c) (𝓝 0):= Eq.subst (motive:=fun z=> Tendsto (fun x=>L (f x)) _ (𝓝 z)) (show L (f c)=0 by simp only [u,f,delta_self,map_zero]) <| ContinuousAt.comp (g:=L) (f:=f) L.continuous.continuousAt (theta_diff c).continuousAt
 have hd: (fun x=> g (R x))=ᶠ[𝓝 c] L ∘ f:=by
    filter_upwards [(G.lieExp_cont.tendsto c).eventually (bump_delta u),hc.eventually (delta_bump u⁻¹)] with x hx hu
    have hx: bump u (f x)= G.lieExp x:=hx
    simp only [g, R, neg_apply, ContinuousLinearMap.id_apply]; rw [Work.F03.exp_neg_color,Work.F03.exp_neg_color]; change delta u⁻¹ (G.lieExp x)⁻¹= L (f x); rw [← hu]; congr 1;exact (show _ = _ from hx ▸ (bump_inverse u (f x)).symm) -- careful rewriting
 have hg: HasFDerivAt g (theta (-c)) (R c) := by rw [hb];exact ((theta_diff (-c)).differentiableAt (by simp)).hasFDerivAt
 have hf: HasFDerivAt f (theta c) c:= ((theta_diff c).differentiableAt (by simp)).hasFDerivAt
 have he: cost (theta (-c) ∘L R)=cost (L ∘L theta c):=congrArg cost ((hg.comp _ R.hasFDerivAt).unique ((L.hasFDerivAt.comp c hf).congr_of_eventuallyEq hd))
 rwa [cost_com,cost_com,cost_norm R (fun a=>by simp [R]),cost_norm L (fun a=> by simp [L,drift]),one_mul,mul_one] at he
abbrev ray {I:Type}[Fintype I](L:I→ G.Color→L[ℝ]G.Color): (I→ G.Color)→L[ℝ](I→ G.Color):= ContinuousLinearMap.pi fun i=> (L i).comp (ContinuousLinearMap.proj i)
lemma cost_ray{I:Type}[Fintype I](L:I→ G.Color→L[ℝ]G.Color): cost (ray L)= ∏ i, cost (L i):=by unfold cost; rw [show ContinuousLinearMap.det (ray L)=∏ i,(L i).det from LinearMap.det_pi (fun i=>(L i).toLinearMap),Finset.abs_prod]

def road(v: Potential G n): Dir G n× Twig G n→L[ℝ] Dir G n× Twig G n:= ContinuousLinearMap.prodMap (ray (fun l:Cotree n=>theta (v.val l.val.val))) (ray (fun l:Trees n=>theta (v.val l.val.val)))

lemma two_counts{f:OEdge n→ ℝ}: (∏ i,f i)=(∏ l:Cotree n,f l.val)*∏ l:Trees n, f l.val:=by
 have H:=Finset.prod_filter_mul_prod_filter_not (Finset.univ) (fun i: OEdge n=>Branch i) f
 rw [← H]; nth_rw 1 [mul_comm]; rw [Finset.prod_subtype _ _ f,Finset.prod_subtype _ _ f] <;> simp
lemma orient(hn: Admissible n)(v:Potential G n): (∏ l ∈ positive n,cost (theta (v.val l))) = ∏ l:OEdge n,cost (theta (v.val l.val)):=by
 refine Finset.prod_bij (fun l _=> index l) (fun l h=> Finset.mem_univ _) ?_ ?_ ?_
 · intro i hi j hj h
   have h: eR i=eR j:= congrArg Subtype.val h
   have hs(q r:Pert.Orb.Links n)(hq:q∈positive n)(hr:r∈positive n): q≠Pert.Orb.image r:=fun e=> (switches r hn |>.mp (e ▸ hq)) hr
   rcases eR_spec i with h'|h' <;> rcases eR_spec j with h''|h''
   · rw [← h', ← h'', h]
   · exact ((hs _ _ hi hj) (h'.symm.trans (h.trans h''))).elim
   · exact ((hs _ _ hj hi) (h''.symm.trans (h.symm.trans h'))).elim
   have hv: Pert.Orb.image i=Pert.Orb.image j:= h'.symm.trans (h.trans h''); apply (Function.LeftInverse.injective image_image); exact hv
 · intro i _
   by_cases h:i.val∈positive n
   · exact ⟨i.val,h,Subtype.ext i.property⟩
   exact ⟨Pert.Orb.image i.val,(switches i.val hn).mpr h,Subtype.ext ((eR_reflect i.val).trans i.property)⟩
 intro l hl; change cost _= cost (theta (v.val (eR l))); rcases eR_spec l with h|h
 · rw [h]
 rw [h]; change _=cost (theta (v.val (Pert.Orb.image l)))
 rw [v.property l,theta_parity]
lemma cost_road (hn: Admissible n):∀ᶠ v:Potential G n in 𝓝 0, cost (road v)= Jacob v:=by
 filter_upwards [theta_steady] with v hv
 let f:= ray (fun l:Cotree n=> theta (v.val l.val.val)); let g:= ray (fun l:Trees n=>theta (v.val l.val.val))
 rw [cost_up (road v) f g (fun x=>by change (f x,g 0)=_;rw [map_zero]) (fun y=>rfl),cost_ray,cost_ray, ← two_counts (f:=fun l:OEdge n=>cost (theta (v.val l.val))),← orient hn v]; exact Finset.prod_congr rfl fun i _=>hv i
lemma coat_rate(v:Potential G n): FP v=(resetFP v).det:=by
 let B := Module.finBasis ℝ (Parameter G n)
 have he: FPmatrix v= LinearMap.toMatrix B B (resetFP v).toLinearMap:= by ext i j; rw [LinearMap.toMatrix_apply];rfl
 unfold FP;rw [he,LinearMap.det_toMatrix]
lemma coat_cost : ∀ᶠ v:Potential G n in 𝓝 0,cost (resetFP v)= FP v:=by
 filter_upwards [(FP_diff (G:=G) (n:=n)).continuousAt.eventually_mem (Ioi_mem_nhds (show 0<FP 0 from by simp))] with v hv
 change 0<FP v at hv; rw [←abs_of_pos hv]; conv_rhs => rw [coat_rate]
 rfl

def submerge(A:Dir G n): Dir G n→L[ℝ]Dir G n:= ray (fun i=>theta (A i))
lemma submergence {P:ChartRatio G}(R:LocalRatio P): ∀ᶠ A:Dir G n in 𝓝 0, PertExtension.Chart.jacobian P A = P.scale ^ Fintype.card (Cotree n) * cost (submerge A):=by
 have he: ∀ᶠ A:Dir G n in 𝓝 0, ∀ i:Cotree n,A i∈Metric.ball 0 P.radius:=eventually_all.mpr fun i=> (continuous_apply (A:=fun _:Cotree n=>G.Color) i).continuousAt (x:=0)|>.tendsto.eventually (Metric.ball_mem_nhds _ R.patch)
 filter_upwards [he] with A ha
 unfold submerge PertExtension.Chart.jacobian; rw [cost_ray, show P.scale ^ Fintype.card (Cotree n)=∏ i:Cotree n,P.scale from (Finset.prod_const P.scale).symm, ← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl fun i _=>?_; unfold PertExtension.Chart.fee;change _= P.scale*cost (theta (A i)); rw [max_eq_left (mul_pos R.scale (R.pos _ (ha i))).le,show cost (theta (A i))= P.J (A i) from exp_delta_det R (ha i)]
lemma submerge_flat: cost (submerge (0:Dir G n))=1:=by
 rw [submerge,cost_ray]; simp_rw [Pi.zero_apply]; rw [show cost (theta (0:G.Color))=1 from (mem_of_mem_nhds (s:={x|cost (theta x)=spin G x}) theta_cost).trans (spin_zero G),Finset.prod_const_one]
end YM.SchemeRG11.Sway
