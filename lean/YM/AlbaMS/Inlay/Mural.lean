import YM.AlbaMS.Inlay.Documents

/-!
# Needy, rank two specialization, overall move packaging

Leave physical coefficients in Tags through whole action if wanted. Rank-two
formula from Ward at order zero classical; compare Hessian of actual energy to
free d1^⋆ d1 separately. Include Haar leading ranks (doesn't change order 0,
size-controlled). Kernel stoice use `keep` traditions from any Luster;
natural for each marking besides couplings.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil.needy
open scoped BigOperators Classical
variable {ι R W : Type*} [CommRing R] {ρ : ι→Bool} {n m : ℕ} {F G:Coil ρ R}
lemma up (h:needy n F)(H:m≤n): needy m F:= fun _ he=>H.trans (h _ he)
lemma founder (F:Coil ρ R): needy 0 F:=fun _ _=>Nat.zero_le _
lemma nil (n:ℕ): needy n (0:Coil ρ R):= by intro l h; exact False.elim (h rfl)
lemma add (h:needy n F)(H:needy n G): needy n (F+G):=by intro l hl; by_cases he:F l=0; exact H l (fun hv=> hl (by simp [he,hv])); exact h l he
lemma sub (h:needy n F)(H:needy n G): needy n (F-G):=by intro l hl; by_cases he:F l=0; exact H l (fun hv=> hl (by simp [he,hv])); exact h l he
lemma smul (h:needy n F)(c:R): needy n (c • F):=fun l hl=> h l (right_ne_zero_of_mul (a:=c) hl)
lemma Dv (h:needy (n+1) F)(i:ι): needy n (D i F):=fun l hl=>Nat.le_of_succ_le_succ (h (i::l) hl)
lemma mul (h:needy n F)(H:needy m G): needy (n+m) (F*G):=by intro l hl; obtain ⟨a,b,hf,hg,he⟩:= occurred F G hl; rw [he.length_eq,List.length_append]; exact Nat.add_le_add (h a hf) (H b hg)
lemma sum (T:Finset W)(f:W→Coil ρ R)(h:∀ i∈T,needy n (f i)): needy n (∑ i∈T,f i):=by induction T using Finset.induction_on with|empty=>simp [nil]|@insert i t ht ih=>rw [Finset.sum_insert ht]; exact add (h i (by simp)) (ih (fun u hu=> h u (by simp [hu])))
lemma empty (h:F []=0): needy 1 F := by intro l hl; cases l; exact False.elim (hl h); exact Nat.succ_le_succ (Nat.zero_le _)
lemma var (i:ι) : needy 1 (varC R ρ i):= empty (var_nil ..)
lemma ranklow (h:needy m F)(H:n<m): rankn n F=0:=by
  ext l; rw [rankn_read]; split
  next he=> exact not_not.1 fun (hl:F l≠0)=> (Nat.not_lt_of_ge (h l hl)) (he ▸ H)
  next=> rfl
end YM.MSBar.Bric.Coil.needy

namespace YM.MSBar.Inlay.Net
open Set Function Filter Gauge NormedSpace MeasureTheory LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Coil
variable {V W I J R : Type*}{G:Gauge} [Fintype V][Fintype W][Fintype I][Fintype J]
variable {Ω :Net V I}{H:Net W J}{F:Grove (ink G V)}
lemma temper (Ω : Net V I)(i:Flit G V): needy 1 (beam Ω.chat i):=needy.sum _ _ (fun j _=> (needy.var (R:=ℝ) (ρ:=ø) (Place.c j)).mul (needy.founder _))
omit [Fintype V] in
lemma cool (i:Flit G I): needy 2 (rod (E:=Flit G V) (grit G I) i):= (needy.sum _ _ (fun x _=> needy.sum _ _ (fun y _=> ((needy.var (R:=ℝ) (ρ:=ø) (Place.c x)).mul (needy.var (Place.c y))).smul _))).smul _
omit [Fintype I] in
lemma bare_rank (h : F.val 0=0)(H:fderiv ℝ F.val 0=0): needy 2 (bare (I:=I) F):= by intro l hv; rcases l with _|⟨x,_|⟨y,l⟩⟩;exact False.elim (hv h);exact False.elim (hv (show fderiv ℝ F.val 0 _=0 from H ▸ rfl)); simp
lemma state (h : F.val 0=0)(he:fderiv ℝ F.val 0=0): needy 2 (superb (grit G I) Ω.chat (bare F)):= (needy.add (bare_rank h he) (needy.sum _ _ (fun i _=> (needy.var (R:=ℝ) (ρ:=ø) (Place.k i)).mul (temper Ω _)))).sub ((needy.sum _ _ (fun i _=> (needy.var (R:=ℝ) (ρ:=ø) (Place.l i)).mul (cool i))).up (by omega))
omit [Fintype I] in
lemma pure_bare (F:Grove (ink G V)): Observe (bare (I:=I) F):=by
  intro l; induction l generalizing F with|nil=>intro _;rfl|cons i l ih=>
    intro he; rw [cons_weight]; rcases i with (i|i)|(i|i); change 0+_= _; rw [zero_add]; exact ih (dx (slabQ i) F) he; all_goals exact False.elim (he (DFunLike.congr_fun (show D (ρ:=ø) _ _=0 from (pathof _ _ I).evaporate F rfl) l)) -- ambiguity
lemma number_beam (i:Flit G V): Pure Loft.number 1 (beam Ω.chat i):= Pure.sum _ _ fun j _=> (var_pure (R:=ℝ) (ρ:=ø) (Place.c j) Loft.number).mul (pure_bare _)
omit [Fintype V] in
lemma number_rod (i:Flit G I): Pure Loft.number 2 (rod (E:=Flit G V) (grit G I) i):= (Pure.sum _ _ (fun x _=> Pure.sum _ _ fun y _=> ((var_pure (R:=ℝ) (ρ:=ø) (Place.c x) Loft.number).mul (var_pure (R:=ℝ) (ρ:=ø) (Place.c y) Loft.number)).smul _)).smul _
lemma number_superb : Observe (superb (grit G I) Ω.chat (bare F)):= (Pure.add (pure_bare F) (Pure.sum _ _ (fun i _=> (var_pure (R:=ℝ) (ρ:=ø) (Place.k i) Loft.number).mul (number_beam i)))).sub (Pure.sum _ _ fun i _=> (var_pure (R:=ℝ) (ρ:=ø) (Place.l i) Loft.number).mul (number_rod i))

-- rank-two click equals nearest diff content. Useful cross for Maxwell.
lemma ghost_rank (Ω:Net V I)(i : Flit G V): rankn 1 (beam Ω.chat i) = ∑ j:Flit G I, Ω.chat j i [] • C ℝ j:=by
  unfold beam; rw [map_sum]; refine Finset.sum_congr rfl fun _ _=>?_; rename_i j hj; ext l
  rw [rankn_read]; split
  next he=>
    rcases List.length_eq_one_iff.mp he with ⟨x,rfl⟩; rw [mul_cons,tap_mul,tap_mul, D_read, Coil.polar, show C (E:=Flit G V) ℝ j []=0 from rfl,sting_zero,zero_mul,add_zero,smul_read,mul_comm] -- tap forms
  next he=> rw [smul_read, show C (E:=Flit G V) ℝ j l=0 from not_not.1 (mt (Heg.var (Place.c (E:=Flit G V) j) l) he),mul_zero]
omit [Fintype I] in
lemma grid (j:Flit G I) (i:Flit G V): Ω.chat j i []=coefQ i.2 (pads (Ω.foot i.1) (slabQ j)-pads (Ω.head i.1) (slabQ j)):=by change coefQ _ (arch _ _) = _; exact congr_arg (coefQ _) (arch_zero _)
omit [Fintype V] in
lemma narrow (i:Flit G I): rankn 2 (L (E:=Flit G V) ℝ i * rod (E:=Flit G V) (grit G I) i)=0:=by apply needy.ranklow ((needy.var (R:=ℝ) (ρ:=ø) (Place.l i)).mul (cool i)) (by omega)
lemma mold (Ω:Net V I)(i:Flit G V): rankn 2 (K ℝ i*beam Ω.chat i)= K ℝ i* rankn 1 (beam Ω.chat i):=by
  let A:=beam Ω.chat i; change rankn 2 (_ * A)=_; have hRank:Heg 2 (K ℝ i* rankn 1 A):=(Heg.var _).mul (rankn.heg A 1)
  rw [← hRank.criterion, ← sub_eq_zero, ← map_sub, ← mul_sub];
  apply needy.ranklow (n:=2) ((needy.var _).mul (show needy 2 (A-rankn 1 A) from ?_)) (by omega)
  intro l h; rcases l with _|⟨x,_|⟨y,l⟩⟩; · rw [sub_read,rankn_read,show A []=0 from not_not.1 fun hn=>by have h:=temper Ω i [] hn; simp at h] at h; simp at h
  · rw [sub_read,rankn_read] at h; simp at h
  simp
lemma sea (Ω:Net V I)(F:Grove (ink G V)): rankn 2 (superb (grit G I) Ω.chat (bare F))= rankn 2 (bare F)+ ∑ i:Flit G V, K ℝ i * ∑ j:Flit G I, coefQ i.2 (pads (Ω.foot i.1) (slabQ j)-pads (Ω.head i.1) (slabQ j)) • C ℝ j:=by unfold superb feeds; rw [map_sub,map_add,map_sum,map_sum]; simp_rw [mold,narrow,ghost_rank,grid]; simp
end YM.MSBar.Inlay.Net
