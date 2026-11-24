import YM.FVAAlt2.Shop.Graph
/-!
# High-engine `Fits` certificate for actual launch
At every stencil use every weight through d, after stripping precisely
the incoming coupling/arity. Linearized gauge potentials only in this
high-Fits check (not changing the continuum scheme). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Shop
open Lattice Function Finset Filter Topology Wilson Labels Source Source.Drops
open Comparison.Stencils.Corona (Crumb Primary Binds Tally demonstrates act_simple plated scape bonded stage_zero printed)
open MS MS.Koszul MS.Native MS.Landau MS.Landau.Detect MS.Plane MS.Tone MS.Theater MS.Book MS.Cylinder MS.Lifting
open Next.Foundations
open MvPolynomial (weightedHomogeneousComponent)
open scoped Topology ContDiff
variable {G:Gauge}{d k:ℕ}{F: Labels.Frame G d}
local notation "Θ"=> Lane4 G
local notation "P"=> hands G
local infix:70 " ⋄ "=> product ( hands G )
local notation "Pr"=> PertExtension.Heat.Ray.print
abbrev H₁ := fun i:Θ=> wfield i.1=1
lemma α_cost (p: wholeSpace G): Uses {i:Θ | H₁ i} (Ψ G p).val:=by
 induction p using MvPolynomial.induction_on with
 | C a=> unfold Ψ; rw [MvPolynomial.aeval_C,cash1]; intro l a h; rcases l with _|⟨x,l⟩; simp at h; exact fun _=>rfl
 | add x y hx hy=> rw [map_add]; exact Uses.add hx hy
 | mul_X p i h=> rw [map_mul, darkM, Ψ, MvPolynomial.aeval_X]; refine Uses.pair h ?_; intro w u hu hv; rcases w with _|⟨a,_|b,w⟩; simp at hu; swap; exact rfl; obtain rfl:=List.mem_singleton.mp hu; exact Classical.byContradiction (fun z=> hv (show _root_.Membership.mem {i:Θ| H₁ i} u from (by change wfield u.1=1; rw [sees_p i u z];rfl))) -- orientation

-- scale law of clipped polynomial transformed before loop. Monomial factor powers exactly
lemma age_read (p:Pol G)(J:Jet G)(t:ℝ): Labels.read J (age t p) = Labels.read (scaleJet J t) p:=by
 induction p using MvPolynomial.induction_on with
 | C a=> simp [age,Labels.read]
 | add x y hx hy=> rw [map_add,map_add,map_add,hx,hy]
 | mul_X p i h=> rw [map_mul,map_mul,h,map_mul]; unfold age zΛ; rw [MvPolynomial.aeval_X, map_smul]; simp [Labels.read,coord_scales,Complex.real_smul]
lemma ageMon (t:ℝ)(v:Key G→₀ℕ)(c:ℂ): age t (MvPolynomial.monomial v c)=(t:ℂ)^(height v) • MvPolynomial.monomial v c:=by
 apply Labels.eval_ext; intro J; rw [age_read,map_smul];
 have hi(i:Key G): (Labels.coord (scaleJet J t) i)^ (v i)=(t:ℂ)^(v i*generation i)*(Labels.coord J i)^(v i):=by rw [coord_scales, Complex.real_smul,Complex.ofReal_pow,mul_pow,← pow_mul,mul_comm (v i) _]
 simp_rw [Labels.read,MvPolynomial.aeval_monomial,Finsupp.prod, hi,Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,height,Finsupp.weight_apply]; simp [Finsupp.sum]; ring
lemma projectAge (p:Pol G)(L:Pol G→ₗ[ℂ] ℂ): ContDiff ℝ ∞ (fun t:ℝ=> L (age t p)) ∧ ∀ k:ℕ,reading k (fun t:ℝ=> L (age t p))=L (Next.Foundations.tier k p):=by
 induction p using MvPolynomial.induction_on' with
 | monomial v c=>
    simp_rw [ageMon,map_smul,smul_eq_mul]; have H:=MvPolynomial.isWeightedHomogeneous_monomial (generation (G:=G)) v c (m:=height v) rfl; refine ⟨registrSmooth _ _ contDiff_const,fun k=>?_⟩; rw [tier,MvPolynomial.weightedHomogeneousComponent_of_mem H,pot_read]; split_ifs <;> first| rfl| simp_all
 | add p r hp hr=> simp_rw [map_add]; exact ⟨hp.1.add hr.1,fun k=>by rw [read_add hp.1 hr.1, hp.2 k, hr.2 k]⟩
lemma scale_hh (i:F.Index)(t:ℝ): age t (F.basis i).val= (t:ℂ)^(F.grades i).1 • (F.basis i).val:=by
 apply Labels.eval_ext; intro J; rw [map_smul,age_read,WardBin.scaled_grade t J (F.basis i) (F.pure i), Complex.real_smul,Complex.ofReal_pow]; rfl
lemma tier_is(i:F.Index)(k:ℕ)(e: List Θ): orbit G (tier k (F.basis i).val) e = if (F.grades i).1=k then orbit G (F.basis i).val e else 0:=by
 let L:= LinearMap.proj (R:=ℂ) (φ:=fun _:List Θ=>ℂ) e ∘ₗ orbit G; obtain ⟨_,H⟩:=projectAge (F.basis i).val L; specialize H k; simp_rw [scale_hh,map_smul,smul_eq_mul,pot_read] at H; exact H.symm

lemma prints_correct (w: List Θ)(p:Primary G)(k:ℕ)(hp:k≤d): reading k (fun t:ℝ=> shaped t (α p) w)=orbit G (tier k (scape G d p)) w :=by
 rw [(builds p w).same k hp,Comparison.Stencils.Corona.printed]; unfold PertExtension.Heat.Ray.clipped; rw [tier_capRead d _ k hp]; exact (projectAge (Pr d p) ( ( LinearMap.proj (R:=ℂ) (φ:=fun _:List Θ=>ℂ) w ) ∘ₗ orbit G )).2 k

open PertExtension PertExtension.LatticePT 
open Comparison.Stencils (columnSeries column_normal)
variable (S:SectionData F){H:Hol G}(h:S.Sound H)(hp:Bid.pop S)
lemma announced (i:F.Index): scape G d ((topMatrix S H h hp).basis i)=(F.basis i).val:=by
 rw [ ← bonded H (plated i h hp), ← stage_zero H (columnSeries S i) d, column_normal S i ( Classical.choice ( Comparison.Stencils.supplied S hp i ) ) _ h ]; rfl
include h hp in
lemma highest (i:F.Index)(w:List Θ)(k:ℕ)(hv:k ≤ d):
  reading k (fun t=> shaped t (Tone.run (Book.levels (F.grades i).2 (origin S i) 0)) w) = if (F.grades i).1=k then orbit G (F.basis i).val w else 0:=by
 -- h hp need include
 rw [read_base S i h hp,show reading _ _= _ from prints_correct w ((topMatrix S H h hp).basis i) k hv, announced, tier_is]
lemma depths_one(w:List Θ): depths 0 w=1:=by induction w with| nil=>rfl| cons a w ih=> exact (congr_arg₂ (·*·) (lensw0 a) ih).trans (one_mul _)
lemma depths_s(w:List Θ): ContDiff ℝ ∞ (fun t=> depths t w):=by induction w with| nil=>exact contDiff_const| cons a w ih=>exact (lenswSmooth a).mul ih

lemma stripCore (w:ℤ)(L f:ℝ→ℂ)(c:ℂ)(h:Rest (fun t=>L t * f t) w c)(hL:ContDiff ℝ ∞ L)(hf:ContDiff ℝ ∞ f)(he:L 0=1): Rest f w c:=by
 refine ⟨hf,h.bottom,?_⟩; intro j; induction j using Nat.strong_induction_on with
 | h j ih=> intro hp; have hz:=h.home j hp; rw [read_mul hL hf, Finset.sum_eq_single_of_mem 0 (by simp),Nat.sub_zero,show reading 0 L=1 from by simp [reading,he]] at hz; simpa only [one_mul] using hz;
            intro i hi hm; rw [ih (j-i) (by simp at hi; omega) (by omega), if_neg (by simp at hi; omega),mul_zero]
lemma less_shape (w:List Θ)(v:Law G)(k:ℕ)(hx:k<w.length)(hs:ContDiff ℝ ∞ (fieldVal v (Wire.ray w))) : reading k (fun t=> shaped t v w)=0:=by
 let f(t:ℝ):= depths t w * fieldVal v (Wire.ray w) t
 have he(t:ℝ):shaped t v w=(t:ℂ)^w.length*f t:=by change ((t:ℂ)^w.length* _)* v _=_; unfold f fieldVal fromt; rw [Wire.ray_go,mul_assoc];rfl
 rw [funext he]; let g(t:ℝ):=(t:ℂ)^w.length*1; rw [ show (fun t:ℝ=> (t:ℂ)^w.length*f t)=fun t=> g t*f t from funext (fun t=>by unfold g; rw [mul_one]), read_mul (registrSmooth _ _ contDiff_const) (show ContDiff ℝ ∞ f from (depths_s w).mul hs) ]; apply Finset.sum_eq_zero; intro i hi; rw [show reading i g=_ from pot_read .., if_neg (by simp at hi;omega),zero_mul]
-- fit certificate EVERY stencil at its own grade (weight w not necessarily d) BEFORE self-subtractions
include h hp in
lemma fitsCore (i:F.Index): Lifting.Face wfield (run (Book.levels (F.grades i).2 (origin S i) 0)) (orbit G (F.basis i).val) (F.grades i).1 false:= by
 intro w _; let d':=(F.grades i).1; let V:=run (Book.levels (F.grades i).2 (origin S i) 0); let f:=fieldVal V (Wire.ray w); let y:=orbit G (F.basis i).val w; let c(t:ℝ):=depths t w
 have hS:ContDiff ℝ ∞ f:= by exact Menus.all_smooth _ (Wire.ray w)
 have H(t:ℝ): shaped t V w=(t:ℂ)^w.length*(depths t w*f t):=by change ((t:ℂ)^_*_)* V _=_; unfold f fieldVal fromt; rw [Wire.ray_go,mul_assoc]; rfl
 have hsub(k:ℕ) (hk:k≤d) : reading k (fun t:ℝ=> (t:ℂ)^w.length*(depths t w*f t)) = if d'=k then y else 0:=by simp_rw [← H]; exact highest S h hp i w k hk
 by_cases he : ∀ a∈w, H₁ a; swap
 · push Not at he; obtain ⟨a,ha,hv⟩:=he; have hf: f=fun _=>0:= by
      funext t; unfold f V fieldVal; rw [read_base S i h hp,Wire.ray_go]; refine α_cost _ _ (fromt t a) ?_ hv; exact List.mem_map_of_mem (f:=fromt t) ha -- comp simp
   specialize hsub d' (F.bound i); rw [ if_pos rfl,hf ] at hsub; change Rest f _ y; rw [hf,show y=0 from Eq.symm (by simpa [reading] using hsub)]; exact Rest.zero _
 rw [ show fieldDim wfield w = w.length from ?_ ]; change Rest f ( (d':ℤ) -w.length ) y; rotate_left
 · unfold fieldDim; rw [show w.map (wfield ∘ Prod.fst) = List.replicate w.length 1 from ?_,List.sum_replicate]; simp; exact List.eq_replicate_iff.mpr ⟨by simp, by intro a h; obtain ⟨b,hb,rfl⟩:=List.mem_map.mp h; exact he b hb⟩
 apply stripCore _ c f y _ (depths_s w) hS (depths_one w); refine ⟨(depths_s w).mul hS, fun ht=>?_, fun j hj=>?_⟩
 · specialize hsub d' (F.bound i); rw [← funext H, less_shape w V d' (by omega) hS] at hsub; simpa using hsub.symm
 rw [ ← registry j w.length (fun t=>c t*f t) ((depths_s w).mul hS),hsub (w.length+j) (le_trans (show w.length+j≤d' from by omega) (F.bound i)) ]; split <;> split <;> first| rfl| omega
end YM.FVAAlt2.Shop
