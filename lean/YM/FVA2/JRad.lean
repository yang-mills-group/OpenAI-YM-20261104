import YM.FVA2.UniversalFrame
/-!
# Radial choice of physical representative in dimensional lift

Construct a dictionary **in the actual Gallery** generated only by applying the open-tensor radial prescription. Because the MS machinery permits any representative in that Gallery it will accept
this choice. Use free symbols in installing it; not a claim that arbitrary DR identities
lift. Coefficients needed across all orders (unscaled $g$) generated.
-/
set_option autoImplicit false
set_option maxHeartbeats 440000
noncomputable section
namespace YM.MS.RadL
open Set Function Filter Finset MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local
open Theater Mach Lifting Pole Color
open Complex (I)
open scoped Topology Classical ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{h k n:ℕ}{x:E4}
local notation "X₀"=> Feet G ( k+1 )
-- project A Taylor piece of degree [k+1] at y.Behaves on Orn.Center.
def χ (G:Gauge)(k:ℕ)(i:Axis)(y:E4): Taylor G k →ₗ[ℝ] G.Color where
   toFun t:= Labels.Taylor.value t i y
   map_add' _ _:=rfl
   map_smul' _ _:=rfl
-- contraction formula as functional on ANY incoming vector polynomial homogeneous k+1
lemma contraction (A:X₀) (x:E4)(i:Axis) : Labels.Taylor.value (yard G k A) i x=( (k:ℝ)+2 )⁻¹ • (∑ l:Axis,x l • (diagonal (( stepL G Axis k l A ).val i) x-diagonal ((stepL G Axis k i A).val l) x)):= by
   let P:=fun i :Axis=> Tensor.diagonal ( A.val i ); let a := P i x; let u:=∑ l:Axis,x l • grad l (P i) x; let t:= ∑ l:Axis,x l • grad i (P l) x; let V:= divYear (k+1); let X := radialX G (k+1) A;
   have ht(u v): diagonal ((stepL G Axis k v A).val u)= grad v (P u):= workL _ A _;
   rw [ Theater.projectionY, carveΩ ]; simp_rw [ ht, smul_sub, Finset.sum_sub_distrib ]; change a-V⁻¹ • diagonal (( stepL G Unit (k+1) i X ).val ()) x=((k:ℝ)+2 )⁻¹ • (u-t); have hv:V=(k:ℝ)+2:= by unfold V divYear; push_cast; ring
   have hu:u=( (k:ℝ)+1) • a := ( grad_euler _ ( A.property i ) x ).trans (by push_cast; rfl ); have hx:diagonal ((stepL G Unit (k+1) i X).val ()) x=a+t:= by
       rw [stepL,workL, funext (tBudget A) ]; exact grad_self A.val i x
   rw [ hv,hx,hu ]; have hz: ( (k:ℝ) +2 ) ≠0 := (by positivity); rw [smul_sub,smul_add,← sub_sub,sub_left_inj,smul_smul] -- check tactic signs
   calc
       _ =(1:ℝ) • a- _:= by rw [one_smul] -- meta
       _ = _:= by rw [← sub_smul]; congr 1; field_simp; ring
-- value compute crumb. reorder ofFn.C. amplitude for each Plaq mark leading.Linear.
structure Spray where
   k:ℕ
   ν:Axis
   y:E4
namespace Spray
variable (t:Spray)
abbrev Λ := Axis × ( Fin t.k→ Axis )
def plaq (v:t.Λ) : Lifting.Plaq:= ⟨v.1,t.ν, List.ofFn v.2 ⟩
def factor (v:t.Λ) : ℝ := ((t.k:ℝ)+2 )⁻¹ * (t.y v.1) * Theater.amount t.k * (∏ i:Fin t.k, t.y ( v.2 i ))
lemma level (i:t.Λ): Pole.Grit (t.plaq i)= t.k+2:= by simp [plaq,Pole.Grit,Nat.add_comm]
-- mark is A-compatible *color component i*. 
abbrev mark (i:G.ColorIndex): Local.BV.Grade G:= ∑ j:t.Λ, ( t.factor j:ℂ) • Lifting.Plaq.mark (t.plaq j) i
private lemma diagonal_p (k:ℕ)(p:FourP)(x:E4)(i j:Axis)(v:G.Color): diagonal (( speak k i p v ).val j) x= if i=j then amount k • ((inner ℝ (fixF p) x)^k • v) else 0:= by by_cases h:i=j; subst j; simp only [speak,Tensor.diagonal,if_true, wearing, Finset.prod_const, Finset.card_univ,Fintype.card_fin ]; rw [if_neg h]; unfold speak; rw [ Theater.away k (fixF p) v ( Ne.symm h ) ]; rfl
private lemma evaluated (c b:G.ColorIndex)(i j:Axis)(k:ℕ)(p:FourP)(x:E4): diagonal (( speak k i p ( cl G c ) ).val j) x b = amount k * ( inner ℝ ( fixF p ) x )^k * ( if i=j then 1 else 0 )* ( if b=c then 1 else 0 ):= by
   rw [ diagonal_p k ]; by_cases he:i=j; swap; · rw [if_neg he]; simp [he]
   rw [if_pos he ]; by_cases hp:b=c <;> simp [hp, cl, he ]
lemma finance (z:Spray)(p:FourP): ∑ j:Fin z.k→Axis,(∏ i:Fin z.k,( z.y (j i):ℂ )) * Lifting.deriv ( List.ofFn j ) p= ( I * (inner ℝ (fixF p) z.y:ℂ) ) ^ z.k := by
    rcases z with ⟨k,i,y⟩; dsimp only; let f(j:Axis):ℂ:= (y j:ℂ) * Lifting.inc j p;
    have he: I*( ( inner ℝ ( fixF p ) y ):ℂ )=∑ i: Axis, f i:= by
       nth_rw 1 [show y = ∑ i:Axis,y i • YM.basis i from PiLp.ext fun i=> ( by simp )]; rw [inner_sum,Complex.ofReal_sum, Finset.mul_sum ]; apply Finset.sum_congr rfl; intro i _; simp_rw [real_inner_smul_right,lean_axis]; unfold f Lifting.inc; push_cast; ring
    have ht : ∏ _i: Fin k,(∑ j:Axis,f j )=( I * (( inner ℝ ( fixF p ) y ):ℂ)) ^ k:= by rw [he, Finset.prod_const, Finset.card_univ,Fintype.card_fin ]; -- parent norm
    rw [← ht,Fintype.prod_sum ]; symm; refine Finset.sum_congr rfl fun a _=>?_ ; simp [ f, Lifting.deriv, List.prod_ofFn, Finset.prod_mul_distrib,Function.comp_def ] -- `List.ofFn_eq?`
abbrev α (t:Spray)(i:G.ColorIndex) := (EuclideanSpace.proj i).toLinearMap.comp (χ G t.k t.ν t.y)
-- $s$ cyclic.
def spot (i:G.ColorIndex): Theater.Witness G t.k:= Complex.ofRealCLM.toLinearMap.comp (t.α i)
lemma flare (a c:G.ColorIndex)(i:Axis)(p:FourP): t.mark c ( W i a p )=RowLeg G t.k ( t.spot c ) ( W i a p ):= by
   let r:= t.k; let L:= speak (r+1) i p ( cl G a ); let F(u:Axis)(l:Axis):=diagonal (( stepL G Axis r l L ).val u) t.y c; let T (v:t.Λ):= t.plaq v; let K:=inner ℝ ( fixF p ) t.y;
   change (∑ j:t.Λ, ( t.factor j :ℂ ) • Lifting.Plaq.mark (t.plaq j) c ) _= hitϑ r.succ * ( (Labels.Taylor.value ( yard G t.k L ) t.ν t.y c):ℂ ); rw [Finset.sum_apply, Fintype.sum_prod_type, contraction ];
   have he(l u): F u l=p l*( Theater.amount t.k * K^r * (if i=u then 1 else 0)*( if c=a then 1 else 0 )) := by
       unfold F; rw [step_at ( v:=cl G a ), Submodule.coe_smul,Pi.smul_apply ]; change p l* diagonal ((speak _ i p (cl G a)).val u) _ _ = _; rw [evaluated ];
   let f(l):= t.y l*(F t.ν l-F l t.ν); have hp: ( ( (( t.k:ℝ )+2 )⁻¹ ) • (∑ l:Axis,t.y l • ( diagonal (( stepL G Axis t.k l L ).val t.ν ) t.y-diagonal (( stepL G Axis t.k t.ν L ).val l ) t.y )) ) c= ((t.k:ℝ)+2)⁻¹ * ∑ l:Axis,f l:= by
       simp only [PiLp.smul_apply,smul_eq_mul]; congr 1
   rw [hp ]; push_cast; rw [ Finset.mul_sum, Finset.mul_sum ]; apply Finset.sum_congr rfl; intro ℓ _;
   change (∑ j:Fin t.k→Axis,( t.factor ( ℓ,j ):ℂ) * (gpath ℓ t.ν c (Lifting.deriv ( List.ofFn j )) (W i a p))) = _;
   let X:ℂ:= ((↑t.k:ℂ) +2 )⁻¹; let Z:ℂ:= (t.y ℓ :ℂ); let Y':ℂ:= (amount t.k:ℂ); let U:ℂ:= if a=c then I*((p ℓ:ℝ):ℂ)*( if i=t.ν then 1 else 0) - I*((p t.ν:ℝ):ℂ)*(if i=ℓ then 1 else 0) else 0;
   have ht : (∑ j:Fin t.k→Axis,( t.factor ( ℓ,j ):ℂ) * (gpath ℓ t.ν c (Lifting.deriv ( List.ofFn j )) (W i a p)))= X*Z*Y'* U*(I*(K:ℂ))^r := by
       rw [← show ∑ j:Fin t.k→Axis,(∏ i:Fin t.k,( t.y ( j i ):ℂ )) * Lifting.deriv ( List.ofFn j ) p = (I*(K:ℂ))^r from finance t p, Finset.mul_sum ]; refine Finset.sum_congr rfl fun j _=> ?_ ; unfold gpath factor; by_cases hx:a=c <;> simp only [hx,U,↓reduceIte]; · unfold X Z Y'; push_cast; ring
       simp
   rw [ht ]; unfold f; rw [he,he ]; unfold X Z Y'; by_cases hc:a=c; swap; · unfold U; rw [if_neg hc, if_neg (Ne.symm hc) ]; simp
   unfold U; simp_rw [ if_pos hc, if_pos hc.symm ]; split_ifs <;> simp only [mul_one,mul_zero, Complex.ofReal_mul, Complex.ofReal_sub, hitϑ, pow_succ,mul_pow,Complex.ofReal_pow,Complex.ofReal_zero] <;> ring
lemma trust (c:G.ColorIndex) : t.mark c= RowLeg G t.k ( t.spot c ):= by
    funext z; rcases z with ⟨⟨⟨_|i,_|_⟩,a⟩,p⟩ <;> first | exact flare t ..| ( unfold mark; rw [Finset.sum_apply]; refine Finset.sum_eq_zero ?_; intro i hi; change ( _ * (0:ℂ) )=0; exact mul_zero _ )
end Spray
end YM.MS.RadL
