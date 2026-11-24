import YM.SchemeRG11.Sew.Sheet
/-! Keep all jets T from scheme wave without seminorm assumption. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Sew
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long Air North Wolt
open scoped Classical
variable {I:Type*}{m n:ℕ}
variable (c v:I→ℝ)
def whip : Paper I ℝ →ₐ[ℝ] Polynomial ℝ:= MvPolynomial.aeval fun i=> Polynomial.C (c i)+ Polynomial.X * Polynomial.C (v i)
open Polynomial
lemma flat (p:Paper I ℝ)(x:ℝ): Polynomial.eval x (whip c v p)=MvPolynomial.aeval (c+x • v) p:=by
 have he:(Polynomial.aeval x).comp (whip c v)=MvPolynomial.aeval (R:=ℝ) (c+x • v):=by
    ext i; simp only [AlgHom.comp_apply,whip,MvPolynomial.aeval_X,Pi.add_apply,Pi.smul_apply,smul_eq_mul,map_add,map_mul,aeval_C,aeval_X]; rfl -- check
 exact (show eval x (whip c v p) = Polynomial.aeval x (whip c v p) by simp).trans (DFunLike.congr_fun he _)
lemma slope (p:Paper I ℝ): eval (0:ℝ) (derivative (whip c v p)) =MvPolynomial.aeval c (vent v p):=by
 have he:=(whip c v p).hasDerivAt 0; simp_rw [flat] at he; exact he.unique (tacks c v p)
lemma capsize {p:Paper I ℝ} (h:Page I n p): natDegree (whip c v p) ≤ n:=by induction h with
 | unit=>rw [map_one,natDegree_one]
 | bill t a h=> rw [map_smul]; exact le_trans (natDegree_smul_le _ _) h -- check
 | past a h=> exact le_trans h (by omega)
 | add a b h k=>rw [map_add]; exact natDegree_add_le_of_degree_le h k
 | @germ n p i a h=>
    rw [map_mul,whip,MvPolynomial.aeval_X]; apply natDegree_mul_le.trans (Nat.add_le_add h ?_); apply (natDegree_add_le _ _).trans; refine max_le ?_ ?_
    · simp
    exact natDegree_mul_le.trans (by simp)
abbrev p0 (m:ℕ):= degreeLT ℝ (m+1)
lemma windy{f:ℕ→ Paper I ℝ}(c v:ℕ→I→ℝ)(he:∀i,Page I m (f i))(H:∀t:ℝ, Finishes (fun i=> MvPolynomial.aeval (c i+t • v i) (f i))): Finishes (fun i=>MvPolynomial.aeval (c i) (vent (v i) (f i))):=by
 simp_rw [← slope]
 let a(j:Fin (m+1)):ℝ:=j.val
 let L : (p0 m)→ₗ[ℝ](Fin (m+1)→ℝ):=LinearMap.pi (fun i=> (Polynomial.aeval (a i)).toLinearMap ∘ₗ (p0 m).subtype)
 have hf(p:p0 m):p.val.natDegree < m+1:=by
   by_cases h:p.val=0; · simp [h]
   exact (natDegree_lt_iff_degree_lt h).mpr (mem_degreeLT.mp p.property)
 have hi(j:Fin (m+1))(p:p0 m): eval (a j) p.val=L p j:= by change _=Polynomial.aeval _ _; simp
 obtain ⟨r,R⟩:=LinearMap.exists_leftInverse_of_injective L (LinearMap.ker_eq_bot.mpr (by
   intro p q h; apply Subtype.ext
   refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq p.val q.val (f:=a) ?_ ?_ ?_
   · exact fun i j w=> Fin.ext (Nat.cast_inj (R:=ℝ) |>.mp w)
   · intro i; rw [hi,hi,h]
   rw [Fintype.card_fin]; exact max_lt (hf _) (hf _)))
 let U (i:ℕ):ℝ[X]:= whip (c i) (v i) (f i)
 have he'(i):U i∈p0 m:=by
   by_cases h:U i=0; · rw [h]; exact Submodule.zero_mem _
   exact mem_degreeLT.mpr ((natDegree_lt_iff_degree_lt h).mp (Nat.lt_succ_of_le (capsize _ _ (he i))))
 let k(i:ℕ):p0 m:= ⟨_,he' i⟩
 let V: (Fin (m+1)→ℝ)→ₗ[ℝ] ℝ:= (Polynomial.aeval (0:ℝ)).toLinearMap ∘ₗ derivative ∘ₗ (p0 m).subtype ∘ₗ r
 have ht(i:Fin (m+1)):Finishes (fun n=> L (k n) i):=by
   apply (H (a i)).same; filter_upwards with p; rw [← hi]; exact (flat ..).symm
 apply (liftL V ht).same; filter_upwards with i
 change Polynomial.aeval (0:ℝ) (derivative ((r _).val))=_
 rw [show r (L (k i))=_ from LinearMap.congr_fun R _] ; simp [k,U]
end YM.SchemeRG11.Sew
