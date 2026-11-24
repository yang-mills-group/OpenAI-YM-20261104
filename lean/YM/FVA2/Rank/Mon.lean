import YM.MS.Halo.Mint
import YangMills.WilsonProof.NativeSupport.YM.MS.Book.Mask
/-!
# Slot parity with MS degrees of coupling

All-degree reflection of covariances and vertices. Ghost and antifield components
carry the SAME sign as gauge fields. Does not require parity of an analytic grouping or
of a position frame. Used to certify the power-law form κ(g²) of TaylorOK Team.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Hue
open Function Filter Set Finset MeasureTheory
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Arc MS.Rock MS.Motif MS.Heat MS.Book
open scoped Topology ContDiff Classical BigOperators
variable {n m:ℕ} {A B E: Type} {P:Type} {p:Sector A}
abbrev σ (n:ℕ): ℂ:= (-1)^n
lemma s0 : σ 0=1:= pow_zero _
lemma s1 : σ 1=-1:= pow_one _
lemma sp (a b:ℕ): σ (a+b)= σ a * σ b := pow_add ..
lemma ss (a:ℕ): σ (a+1) = -σ a:= by rw [sp,s1]; simp
lemma s2 (a:ℕ): σ (a+2)=σ a:= by rw [show a+2=a+1+1 from rfl,ss,ss,neg_neg]
lemma s_id (a:ℕ): σ a * σ a=1:= by rw [← mul_pow]; simp
lemma s_bk (a:ℕ): star (σ a)=σ a:= by simp [σ] -- RingHom.star syntax
lemma s_even {a:ℕ} (h:a%2=0) : σ a=1:= by
 rw [show a=a/2+a/2 from (by omega)]; nth_rw 1 [sp]; exact s_id _
lemma s_odd {a:ℕ} (h:a%2=1) : σ a=-1:= by
 rw [show a=a-1+1 from by omega,ss,s_even (by omega: (a-1)%2=0)]
lemma s_he {a b:ℕ} : σ a=σ b ↔ a%2=b%2:= by
 rcases (show a%2=0 ∨ a%2=1 from by omega) with he|he <;> rcases (show b%2=0 ∨ b%2=1 from by omega) with ha|ha <;> first | rw [ s_even he,s_even ha,he,ha ]| rw [s_even he,s_odd ha,he,ha]| rw [s_odd he,s_even ha,he,ha]|rw [s_odd he,s_odd ha,he,ha]
 all_goals norm_num

abbrev flip (A:Type): Op A ℂ where
 toFun X w:= σ w.length * X w
 map_add' X Y:= by ext w; exact mul_add ..
 map_smul' i X:= by ext w; exact mul_left_comm ..
lemma flip_at (w:Legs A) (F:Raw A ℂ) : flip A F w= σ w.length * F w:= rfl
lemma stop (F:Raw A ℂ): flip A (flip A F)= F:= by ext w; rw [flip_at,flip_at,← mul_assoc,s_id,one_mul]
lemma flip_cons (x:A)(F:Raw A ℂ): D x (flip A F)=-(flip A (D x F)):= by ext l; simp only [at_D,flip_at,Pi.neg_apply,List.length_cons,ss,neg_mul]
lemma ranks (F:Raw A ℂ)(h:Book.rank (n:ℤ) F): flip A F=σ n • F:= by
    funext w; by_cases hp:w.length=n; · rw [flip_at,hp]; rfl
    rw [flip_at, Pi.smul_apply,h w (by rw [mod_int]; omega)]; simp
-- Equivalent vanishing at other parity.No claims bound on rank here.
def only (n:ℕ)(F:Raw A ℂ): Prop:= ∀ l:Legs A,n%2≠l.length%2 → F l=0
lemma test_p (n:ℕ)(F:Raw A ℂ): only n F ↔ flip A F=σ n • F:= by
    refine ⟨fun h=>?_,fun h w hp=>?_ ⟩
    · funext w; rw [flip_at,Pi.smul_apply,smul_eq_mul]; by_cases he:n%2=w.length%2; exact congr_arg (· * F w) (s_he.mpr he).symm; simp [h w he]
    by_contra hx; apply hp; apply s_he.mp; apply mul_right_cancel₀ (b:=F w) -- guess
    · exact hx
    exact (congr_fun h w).symm
lemma only_id (n:ℕ)(F:Raw A ℂ): only n F ↔ σ n • flip A F= F:= by
    rw [test_p]; refine ⟨fun h=> by rw [h,smul_smul,s_id,one_smul],fun h=>?_ ⟩; nth_rw 2 [← h]; rw [smul_smul,s_id,one_smul]
-- coloration label basis acts on slots, preserving total count.
section pilot
variable [Fintype A][AddCommGroup P]
abbrev ink (p:Sector A)(P:Type)[AddCommGroup P] : Pilot ℂ P p where
 volp:= AddEquiv.refl _
 fieldC a b:= if a=b then -1 else 0
 pair_zero i j h:= by split at h <;> grind
lemma beam (X: Pilot ℂ P p) (F:Row A P ℂ): X.beam (flip _ F)= flip _ (X.beam F):= by
 funext w; induction w generalizing F with
 | nil=>simp [flip_at]
 | cons x l ih=> rw [Pilot.met,flip_at, Pilot.met]; simp only [List.length_cons, ss, Finset.mul_sum, flip_cons, map_neg, ih,Pi.neg_apply,flip_at]; exact Finset.sum_congr rfl fun i _=> by ring -- parser
lemma black (F:Row A P ℂ): (ink p P).beam F = flip _ F:= by
 funext w; induction w generalizing F with
 | nil=> simp [flip_at]
 | cons x l ih=> rw [Pilot.met]; simp_rw [ink, ite_mul, zero_mul]; rw [ Finset.sum_ite_eq ]; simp only [Finset.mem_univ,if_true,ih,flip_at, at_D, List.length_cons, ss, AddEquiv.refl_apply ]; rcases x with ⟨x,y⟩; simp
lemma port (F: Plane.Flux A P ℂ): (ink p P).Transport F F:= by intro i a b; change _= ∑ c,∑ d,F c d i*(if c=a then -1 else 0)*(if d=b then -1 else 0); simp [mul_ite]
end pilot
end YM.FVA2.Hue
