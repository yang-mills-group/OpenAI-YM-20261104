import YM.WilsonCoeffUV.Wick.Rank
import YM.WilsonCoeffUV.Root.UV.Peaks
/-!
# Wick through transfer before projection (full G)
Uses cutoff unchanged operations on arterial normalized field. Certifies first Wick
mask assembly. Null issued from actual stencil to exact periods (including
coarse rooted affine preimage positions), via move AFTER full color-cuv.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Carp
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Soil Cosmos
open Exterior Next.Free Tree Precision Power Embroider
open scoped Topology BigOperators ContDiff
variable {c f n:Side}{U V W α β: Type*} {r e j k m D N:ℕ}{G:Gauge}{x s ξ σ A' B:ℝ}
section st
variable (A:Levels G) (Ñ:ChartRatio G)
def blues (N j:ℕ) (n:Side):= ColorStar A.clock.kernel.penalty (location A N j) G n
def sea (N j:ℕ): ropes Cover (Hooks G) (Hooks G):= of fun ⟨x,a,b⟩ ⟨y,c,d⟩=> if b=d then (infiniteStar A.clock.kernel.penalty (location A N j) (x-y) a c).re else 0
lemma foot (n:Side) (x y:Site n)(a c)(b d) : blues A N j n (x,a,b) (y,c,d)= if b=d then (finiteStar A.clock.kernel.penalty (location A N j) (lift x-lift y) a c n).re else 0:= rfl
lemma recruit (N j): SymbolK (blues A N j) (sea A N j):=by
   obtain ⟨C,h,H⟩:= starFumes A.clock.kernel.penalty (A.clock.adm j)
   refine ⟨fun x y=>?_,C,Eventually.of_forall (fun n=> ⟨h,fun ⟨x,a,b⟩ ⟨y,c,d⟩=>?_ ⟩)⟩
   swap
   · rw [foot]; split
     · exact (Complex.abs_re_le_norm ..).trans ((H (location A N j) _ a c).1 n)
     rw [norm_zero]; exact h
   rcases x,y with ⟨⟨x,a,b⟩,y,c,d⟩
   change Tendsto (fun n=> blues A N j n (wrap n x,a,b) (wrap n y,c,d)) atTop (𝓝 _)
   simp_rw [foot (j:=j)]; unfold sea; rw [Matrix.of_apply]; by_cases he:b=d; swap; · simp only [if_neg he]; exact tendsto_const_nhds
   simp only [if_pos he]; apply Tendsto.congr' (f₁:=fun n=> (finiteStar A.clock.kernel.penalty (location A N j) (x-y) a c n).re) _ (Complex.continuous_re.continuousAt.tendsto.comp (starExit A.clock.kernel.penalty (location A N j) (x-y) a c (A.clock.adm _)))
   apply Eventually.of_forall; intro i; exact congr_arg Complex.re (stellar_wrap A.clock.kernel.penalty _ (x-y) _ (by rw [map_sub,map_sub,wrap_lift,wrap_lift]) a c)
lemma tundra (m:ℕ) : ∀ᶠ n:Side in atTop,Bid.Larger (G:=G) (mStep A n m):=by
    let L:=loose A m
    filter_upwards [eventually_ge_atTop (⟨100*Pressure.macroR L + 2,by omega⟩:Side)] with n hn
    have he:100*Pressure.macroR L + 2 ≤ n.val:= hn
    exact ⟨(A.blocks m 0).branches,(Nat.le_of_lt (show 100*Pressure.macroR L< n.val from by omega)).trans (Nat.le_mul_of_pos_right n.val (L.L).pos),by omega⟩

end st
section lin
variable [NormedAddCommGroup V][NormedSpace ℝ V][NormedAddCommGroup W][NormedSpace ℝ W]
lemma icemaps [Fintype U](K:Matrix U U ℝ)(P:Gen V U)(f:V→ₗ[ℝ]W)(u): iceberg K (cloaks f P) u= cloaks f (iceberg K P u):= by induction u with | zero=>rfl | succ i ih=> rw [iceberg,iceberg,map_smul,cloak_ripple,ih]
lemma masonmaps [Fintype U](K:Matrix U U ℝ)(P:Gen V U)(f:V→ₗ[ℝ]W)(u): carve u K (cloaks f P) = cloaks f (carve u K P):= by unfold carve; simp_rw [icemaps,map_sum]
-- translation
lemma stars_step (Q:Gen V (Woods G n))(b:Site n)(A:Levels G)(j N:ℕ)(k): carve k (blues A N j n) (fun i=> revolve b (Q i)) = fun i=> revolve b (carve k (blues A N j n) Q i):=by
    let X:=blues A N j n
    let F:=jog b (α:=Hooks G)

    have ht : allotM F F X=X:=by
       ext ⟨x,a,c⟩ ⟨y,i,t⟩; unfold F allotM; rw [Matrix.submatrix_apply]; change blues _ _ _ _ ((-b)+x,a,c) (-b+y,i,t)=_; unfold X; rw [foot,foot]; congr 2; apply stellar_wrap; simp
    have hz i : bend F (iceberg X Q i)=iceberg X (bend F Q) i:=by
       induction i with
       | zero=> rfl
       | succ i ih=>rw [iceberg,iceberg,bend_smul,bend_ripple, ht,ih]
    change carve k X (fun i=> revolve b (Q i))=fun i=> revolve _ _

    change carve k X (bend F Q)=bend F (carve k X Q)
    unfold carve; simp_rw [bend_sum,hz]
def hemSev [Fintype U](_A:Matrix U U ℝ)(c:U): Gen V U →ₗ[ℝ] Gen V U where
    toFun P:=sever c P
    map_add' x y:=by ext1 v; apply funext; intro i; simp only [sever, prune,Pi.smul_apply,Pi.add_apply,smul_add]
    map_smul' a x:=by ext1 v;apply funext; intro i; simp only [sever, prune,Pi.smul_apply]; apply smul_comm

noncomputable def carveL [Fintype U](A:Matrix U U ℝ):ℕ → Gen V U →ₗ[ℝ] Gen V U
    | 0=> LinearMap.id
    | i+1=> ((i+1:ℕ):ℝ)⁻¹ •(∑ a:U,∑ b:U,(A a b/2) • (hemSev (V:=V) A a).comp (hemSev A b)).comp (carveL A i)
lemma carveM [Fintype U](A:Matrix U U ℝ)(k:ℕ)(P: Gen V U): carveL A k P=iceberg A P k:=by
   induction k with
   | zero=>rfl
   | succ k ih=> rw [iceberg,carveL, LinearMap.smul_apply, LinearMap.comp_apply, ih,LinearMap.sum_apply]; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply]; rfl
def carveLM [Fintype U](A:Matrix U U ℝ)(k:ℕ) : Gen V U→ₗ[ℝ]Gen V U:= ∑ i∈Finset.range (k+1),carveL A i
lemma carveMe [Fintype U](A:Matrix U U ℝ)(k:ℕ)(P:Gen V U): carve k A P=carveLM A k P:=by simp_rw [carveLM,LinearMap.sum_apply,carveM]; rfl
lemma iceSum [Fintype U](A:Matrix U U ℝ)(P:α→Gen V U)(c:ℝ)(S:Finset α)(l:ℕ): carve l A (c•∑ i∈ S,P i)=c • ∑ i∈S,carve l A (P i):=by simp_rw [carveMe,map_smul,map_sum]
end lin
end YM.WilsonCoeffUV.Bank.Carp
