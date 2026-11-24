import YM.FVA2.CoverLift

/-!
# Construct the `Z.L` section actually required by the MS input

It is specified by solving divergence-free in the orbit variables. This is a real
linear section of the quotient edge chart: logarithms in the provided color norm; div
on the full covering torus; tree correspondence fixes the phase space coordinate on it.
Include fixed-point and zero determinant cases (if color/edge dims empty) exactly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Trans
open FormalOPE.RG10 FormalOPE.RG10.BlockGauge Lattice Gauge
open PertExtension PertExtension.Series PertExtension.Orb PertExtension.Chart
open Function Finset Filter Set Metric MeasureTheory Precision Inherit Push.Loops TreeBasis
open Wilson
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable (G : Gauge) (n : Side)
def productCone : Cone G n →ₗ[ℝ] Module.Dual ℝ (Cone G n) :=
 LinearMap.mk₂ ℝ (fun u v=> (∑ i: Edge (Site n), Inner.inner ℝ (coverL G n u i) (coverL G n v i))/2)
    (fun x y z=> by simp [inner_add_left,sum_add_distrib,add_div]) (fun r x y=> by simp_rw [map_smul,Pi.smul_apply, real_inner_smul_left,smul_eq_mul,← Finset.mul_sum,mul_div_assoc])
    (fun x y z=> by simp [inner_add_right,sum_add_distrib,add_div]) (fun r x y=> by simp_rw [map_smul,Pi.smul_apply, inner_smul_right,smul_eq_mul,← Finset.mul_sum,mul_div_assoc])
lemma prod_turn (x y : Cone G n) : productCone G n x y=productCone G n y x:= congr_arg (fun t:ℝ=>t/2) (Finset.sum_congr rfl fun i _=> real_inner_comm (coverL G n y i) (coverL G n x i)) -- check orientation
lemma dot_pos (x:Cone G n)(hx:x≠0): 0 < productCone G n x x := by
   have h : ∃ i: Edge (Site n), coverL G n x i≠0:= by by_contra! h; exact hx ((coverL_inj G n) ((funext h : coverL G n x=0).trans (map_zero _).symm))
   obtain ⟨i,h⟩:=h; apply half_pos; apply Finset.sum_pos'; · exact fun _ _=> real_inner_self_nonneg
   refine ⟨i,Finset.mem_univ _,?_⟩; rw [real_inner_self_eq_norm_sq]; exact pow_pos (norm_pos_iff.mpr h) _
lemma colour_cost (x y : G.Color) : Inner.inner ℝ x y=∑ a:G.ColorIndex, x a*y a:=by rw [PiLp.inner_apply]; exact Finset.sum_congr rfl fun i _=> mul_comm (y i) _ -- order

lemma prod_cost (x y : Cone G n) : productCone G n x y=(∑ a : G.ColorIndex, Green.linkdot (Colour G n x a) (Colour G n y a))/2:= by
     change ((∑ i:Edge (Site n), Inner.inner ℝ _ _)/2)=_; simp_rw [colour_cost]; congr 1; rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun a _=>?_); rw [Fintype.sum_prod_type]; exact Finset.sum_comm

-- Hessian ancestor in ghost sector: based mean-zero parametrization at precisely the same pairing.
local notation "D" => d G (rim n)
def mixed : Cone G n →ₗ[ℝ] Module.Dual ℝ (Param G n) := LinearMap.compl₂ (productCone G n) (d G (rim n))
def ℓ : Param G n →ₗ[ℝ] Module.Dual ℝ (Param G n) := mixed G n ∘ₗ d G (rim n)
lemma pair_ghost (p q:Param G n): ℓ G n p q= productCone G n (D p) (D q) := rfl
lemma ghost_turn (p q:Param G n): ℓ G n p q=ℓ G n q p:=prod_turn G n (D p) (D q)
lemma pos_ghost (p : Param G n)(h:p≠0):0<ℓ G n p p:= dot_pos G n (d G (rim n) p) (fun e => h (d_inj G (staple n) (e.trans (map_zero _).symm)))
lemma inject (p : Param G n) (hp:ℓ G n p=0):p=0:= by by_contra h; apply (pos_ghost G n p h).ne'; rw [hp]; rfl

def poisson : Param G n ≃ₗ[ℝ] Module.Dual ℝ (Param G n) := LinearEquiv.ofBijective (ℓ G n) (by
    have he : Injective (ℓ G n):=LinearMap.ker_eq_bot.mp (bot_unique (fun p hp=> Submodule.mem_bot (R:=ℝ).mpr (inject G n p hp))) -- dot field?
    exact ⟨he,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq ..|>.symm)).mp he⟩)
def literal : Cone G n→ₗ[ℝ] Param G n := (poisson G n).symm.toLinearMap ∘ₗ mixed G n
lemma stream (x:Cone G n) :ℓ G n (literal G n x)=mixed G n x:= LinearEquiv.apply_symm_apply (poisson G n) _
lemma streams (p:Param G n): literal G n (D p) = p:= LinearEquiv.symm_apply_apply (poisson G n) _

def smoothLink := LinearMap.id (R:=ℝ) (M:=Cone G n) - (d G (rim n)) ∘ₗ literal G n
lemma smooth_v (x:Cone G n): smoothLink G n x=x-D (literal G n x):=rfl
lemma solves (x:Cone G n) : literal G n (smoothLink G n x)=0:= by rw [smooth_v,map_sub,streams,sub_self]
def plan : GaugeSlice G n where
   L := smoothLink G n ∘ₗ enter G (staple n)
   agreement v:= by
     change whereL G (staple n) (smoothLink G n (enter G (staple n) v))=v; rw [smooth_v, map_sub, SectionBasis.d_where, sub_zero]
     exact (by simpa using where_apply G (staple n) 0 v)
lemma planned (x:Cone G n) : SectionBasis.projection (plan G n) x= literal G n x:= by
   conv_rhs => rw [← (plan G n).resolves x]; rw [map_add,streams, show literal G n ((plan G n).L ((whereL G (staple n)) x)) = 0 from solves G n (enter G (staple n) ((whereL G (staple n)) x)),add_zero]

abbrev Transverse (x:Cone G n) := ∀ a:G.ColorIndex,Green.div (Colour G n x a)=0
abbrev siteColour (p:Param G n)(a:G.ColorIndex) (i:Site n): ℝ:= siteCover G n p i a
lemma charge_div (x:Cone G n)(p:Param G n) : mixed G n x p=(∑ a:G.ColorIndex,Green.dot (Green.div (Colour G n x a)) (siteColour G n p a))/2 := by change productCone G n x _=_; rw [prod_cost]; simp_rw [grad_color,Green.divergence_adj]

lemma mixed_zero (x:Cone G n)(h:Transverse G n x):literal G n x=0:=by
   change (poisson G n).symm (mixed G n x)=0; suffices he:mixed G n x=0 by rw [he,map_zero]
   apply LinearMap.ext; intro i; simp_rw [charge_div,h, Green.dot_zero, Finset.sum_const_zero,zero_div]; rfl

lemma supported_pos (x : Site n→ℝ) : 0≤Green.dot x x:= Finset.sum_nonneg (fun _ _=> mul_self_nonneg _)
lemma supported_at (x : Site n→ℝ)(h : x≠0): 0<Green.dot x x:= by
   contrapose! h
   funext i; change x i=0
   have hi:= (show x i*x i≤Green.dot x x from Finset.single_le_sum (s:=Finset.univ) (fun j _=> mul_self_nonneg (x j)) (Finset.mem_univ _)).trans h; nlinarith

lemma closed_sum (f:Site n → ℝ)(a:Axis): (∑ i:Site n, Green.back a f i)=0:= by
    have hh:= Green.adjoint a f (fun _ => 1)
    simpa [Green.fwd_of] using hh.symm
lemma finish_landau (x:Cone G n) (hn:_root_.Even n.val)(hp:literal G n x=0): Transverse G n x:= by
   intro a
   let f(b:G.ColorIndex):= Green.div (Colour G n x b)
   let g (i:Site n):G.Color:=WithLp.toLp 2 (fun b:G.ColorIndex=> f b i)
   have he(b:G.ColorIndex)(i:Axis)(z):Colour G n x b i (-z-step i) = -Colour G n x b i z:= congr_arg (fun v:G.Color => v b) (cover_reflect G n hn x (z,i))
   have hh(b:G.ColorIndex) i : f b (-i)=f b i:= by
       unfold f; rw [Green.divergence_v, Green.divergence_v]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [Green.back_of,Green.back_of,he, show Colour G n x b j (-i)= - Colour G n x b j (i-step j) from ?_]; ring
       rw [← show -(i-step j)-step j= -i from (by abel), he]
   have ht(b:G.ColorIndex): (∑ i:Site n, f b i)=0:=by unfold f; simp_rw [Green.divergence_v]; rw [Finset.sum_comm]; exact Finset.sum_eq_zero fun i _=> closed_sum n _ i -- uses G?
   have hG : ∑ i:Site n,g i=0 := PiLp.ext (fun b=> (by change (WithLp.ofLp (∑ i, g i)) b=0; rw [WithLp.ofLp_sum, Finset.sum_apply]; exact ht b))
   obtain ⟨p,h⟩:= in_sector G n (f:=g) (fun i=> PiLp.ext fun b=> hh b i) hG
   have hx: mixed G n x=0:= by rw [← stream, hp,map_zero]; -- `stream` syntax
   by_contra H; have hq : 0 < ∑ b, Green.dot (f b) (f b):= by refine Finset.sum_pos' (fun i _=> supported_pos n (f i)) ⟨a,Finset.mem_univ _,supported_at n _ H⟩
   have hv : 0 < mixed G n x p := by rw [charge_div]; simp_rw [show ∀ a, siteColour G n p a=f a from fun a=> funext fun i=> congr_arg (fun g: Site n→G.Color=> g i a) h]; exact half_pos hq
   rw [hx] at hv; exact lt_irrefl (0:ℝ) hv
lemma gauges (hn:_root_.Even n.val)(x:Wilson.Field G n): Transverse G n ((plan G n).L x):=
     finish_landau G n _ hn (solves ..)
lemma onto (x:Cone G n)(h:Transverse G n x): ∃ u,(plan G n).L u=x:= by
    obtain he := (plan G n).resolves x
    rw [planned,mixed_zero G n x h,map_zero,zero_add] at he; exact ⟨_,he⟩
end YM.FVA2.Trans
