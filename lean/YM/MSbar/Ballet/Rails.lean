import YM.MSbar.Ballet.Palette
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Ballet
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Alto Mosaic Mosaic.Issue
variable {G:Gauge}
open Work.G05
variable {n:Side}{k p m q:ℕ}{B Y K R t:ℝ}{σ:Type}[Fintype σ][DecidableEq σ]{f g:Positions σ→ℝ}
local notation "Q"=>Positions σ
lemma railQ(f:Positions σ→ℝ)(t:ℝ)(E:Finset σ)(h: f ∘ haul σ E=f) (hp:ContDiffAt ℝ p f 0): blockTaylor p f ∘ haul σ E= blockTaylor p f:=by
   let F(u:Unit):= f; let Z:= Finset.univ \ E; have ht : () ∉ Jade.farQ Z (fun (_:Unit)=> E):=by simp only [Jade.farQ, Finset.mem_filter,Finset.mem_univ,true_and,not_not]; unfold Z; exact Finset.disjoint_sdiff
   funext x
   have hz:∀ j∈univ\Z,haul σ E x j=x j:=by
       intro j hj; unfold haul; have hh : j∈ E:=by by_contra hh; exact (mem_sdiff.mp hj|>.2) (mem_sdiff.mpr ⟨mem_univ _,hh⟩)
       rw [if_pos hh]
   exact (Jade.Oscar _ _ (show ∀ i:Unit, F i ∘ haul σ _= F i from fun _=>h) () ht _ hz hp).2
lemma paletteZ (E:Finset σ) : ∃ T : Q →L[ℝ] Q, ⇑T = haul σ E∧∀ x:Q, ‖T x‖≤ ‖x‖:=by
   let P:Q →L[ℝ] Q:= LinearMap.toContinuousLinearMap ({ toFun:=haul σ E
                                                        map_add':= by intro i j; funext x; unfold haul; split <;> simp_all
                                                        map_smul':= by intro i j; funext x; unfold haul; split <;> simp_all } : Q →ₗ[ℝ] Q)
   refine ⟨P,rfl,fun x=> pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr (fun i=> ?_)⟩; change ‖(if i∈E then _ else (0:ℝ))‖ ≤ _; split; next h=> exact norm_le_pi_norm x i
   rw [norm_zero]; exact norm_nonneg _
lemma subscriptions (E:Finset σ)(h:f∘haul σ E=f)(hp:∀ y∈ Metric.closedBall (0: Positions σ) Y,ContDiffAt ℝ q f y)(x:Q)(he:x∈ Metric.closedBall (0:Positions σ) Y)(K:List σ)(hv:buoy f x K≠0)(hk:K.length≤q):∀ j∈K,j∈E:=by
   obtain ⟨W,r,hu⟩:=paletteZ E; have he':W x∈ Metric.closedBall (0:Positions σ) Y:=mem_closedBall_zero_iff.mpr ((hu x).trans (mem_closedBall_zero_iff.mp he))
   intro j hj; by_contra h'; apply hv; have hc : 0 ∈ (K.map Uniform.bolt).map W:=by
       refine List.mem_map.mpr ⟨bolt j,List.mem_map.mpr ⟨j,hj,rfl⟩,?_⟩; funext x; change (W (bolt j)) x=0; rw [show W (bolt j)=haul σ E _ from congr_fun r _]; unfold haul; split; next h=> have hx:x≠j:=fun he=>h' (he▸h); simp [bolt,hx]
       rfl
   unfold buoy; rw [show f= f ∘ W from h.symm.trans (by rw [r]), toe W q _ (hp _ he') (by rw [List.length_map];exact hk)]; exact Lis.emptyF _ _ _ hc (hp _ he') (by simp only [List.length_map,hk])
variable (u:Face (Per n))
noncomputable def quotation(G:Gauge)(K:ℝ)(r:ℕ) := priceCost G (travelCost G r 4 (Uniform.composeCost r K (shade G)))
lemma guns (h:PaintSupply G k K)(x:Positions (Primary n G))(hx:‖x‖<1): Allows k (sitePrice G n u) x (quotation G K k):=by
    let f(v:Positions (Primary n G)):=represent (tint G _ v)
    have ht(i:Edge (Site n)) : Allows k (fun v : Positions (Primary n G)=> G.mat (f v i)) x (Uniform.composeCost k K (shade G)):=by
        let L:Positions (Primary n G)→L[ℝ]G.Color:= (ContinuousLinearMap.proj (i.1,Exterior.coord i.2)).comp (tint G _).toContinuousLinearMap
        have hh:‖L‖≤ shade G:=by apply L.opNorm_le_bound (shade_pos ..|>.le); exact fun x=> (norm_le_pi_norm ((tint G _) x) _).trans (tint_le x)
        have hb:‖L x‖ ≤ shade G:= (L.le_opNorm _).trans (le_trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _)) (mul_le_of_le_one_right (shade_pos ..|>.le) hx.le))
        have hp(v:Positions (Primary n G)): G.mat (f v i) =G.mat (G.lieExp (L v)):=by unfold f; rw [Work.F03.represent_link];rfl
        simp_rw [hp]; exact (h.2 _ hb).comp (allows_linear hh hb)
    apply Allows.price (f:=fun v:Positions (Primary n G)=>faceValue (f v) u); exact travel_jets (U:=f) ht (w:=square _ _) u.1 (by simp [square])
lemma lawn (G:Gauge) : let f:=sitePrice G n u; f ∘ haul (Primary n G) (curbL (chart n G) u.1 4)= f :=by
    intro f; funext x; let v:= haul (Primary n G) (curbL (chart n G) u.1 4) x; let F(v:Positions (Primary n G)):=represent (tint G _ v); change G.price (travel (F v) u.1 _)=_; refine congr_arg G.price (Uniform.path_same (G:=G) (w:=square u.2.val.1 u.2.val.2) ?_); intro i he; unfold F; rw [Work.F03.represent_link, Work.F03.represent_link]; apply congr_arg; ext k
    let j:=primary i k; change v j=x j; unfold v haul; rw [if_pos]; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩; rw [separation_comm]; exact he
end YM.MSbar.Ballet
