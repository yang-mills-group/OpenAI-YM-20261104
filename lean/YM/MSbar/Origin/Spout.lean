import YM.MSbar.Origin.Ebony

/-!
# Ghost generators, Chevalley relation and nil on fields

Before encoding charge by body exponent. Structure constants give the
Lie algebra test. Trace test specialized to adjoint generators orthonormal in
colors (strong enough so each diagonal is zero). Use CE plus representation
signs from the actual exponent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Origin.Charm
open Function Filter Topology Super Finset
open scoped BigOperators ContDiff
variable {α β M J : Type*} {p : β→Bool} (K : Charm M J β p)
variable [Fintype J] [DecidableEq β] {V : Canal M J} {D : Beamish J}

def Beats (D : Beamish J) := ∀ i j a,D i j a= - D i a j
-- actually independent Fintype
abbrev crown (D : Beamish J) (a i l k : J) := ∑ j, ((D a i j:ℝ) : ℂ) * ↑(D j l k)
def Chased (D : Beamish J) := ∀ a i l k,crown D a i l k+crown D a l k i+crown D a k i l=0

lemma grade_trunk (D : Beamish J) (i) : Grade p false (K.trunk D i) := (Grade.sum (fun x _ => Grade.sum fun y _ => (K.grade_duplex x y).smul _)).smul _
variable [Fintype M] [DecidableEq M]
omit [Fintype M] [DecidableEq M] [DecidableEq β] in
private lemma savor (U : J→J→Term β) (H : Beats D) (a : J) : (∑ i,∑ j, (D a i j:ℂ) • (U i j-U j i))=(2:ℂ) • ∑ i,∑ j,(D a i j:ℂ) • U i j := by
   have he : (∑ i,∑ j,(D a i j:ℂ) • U j i)= -(∑ i,∑ j,(D a i j:ℂ) • U i j) := by
     rw [sum_comm]; simp only [←sum_neg_distrib]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [H a j i]; simp
   simp only [smul_sub,sum_sub_distrib,he]; module
lemma spout (H : Beats D) (a : J) : K.operate V D (K.trunk D a)= -(∑ i,∑ j,(D a i j:ℂ) • mix p (K.ghost j) (K.trunk D i)) := by
   have he i j : K.operate V D (K.duplex i j)=mix p (K.ghost j) (K.trunk D i) - mix p (K.ghost i) (K.trunk D j) := by
     unfold duplex operate; rw [Canon.guide_mix K.toCanon (K.grade_lift V D) (K.grade_ghost i),show K.guide (K.lift V D) (K.ghost i)= K.trunk D i from K.toCanon.guide_letter (K.lift V D) _,show K.guide (K.lift V D) (K.ghost j)=K.trunk D j from K.toCanon.guide_letter (K.lift V D) _,even_mix_comm (K.grade_trunk D i) (K.grade_ghost j)]; simp [sub_eq_add_neg]
   rw [trunk]; -- both? rw at goal first occurrence
   unfold operate at he ⊢; simp_rw [Canon.guide_smul,Canon.guide_sum,Canon.guide_smul,he]; rw [savor (fun i j => mix p (K.ghost j) (K.trunk D i)) H a]; module

private def cycle (Z : J→J→J→Term β) := ∑ i:J,∑ j:J,∑ k:J,Z i j k
omit [Fintype M] [DecidableEq M] [DecidableEq β] in
private lemma roll (Z : J→J→J→Term β) : cycle Z=cycle (fun j k i => Z i j k) := by unfold cycle; rw [sum_comm]; apply sum_congr rfl; intro x _; exact sum_comm
omit [Fintype M] [DecidableEq M] [Fintype J] in
private lemma triple (i j k : J) : mix p (K.ghost i) (K.duplex j k)=mix p (K.ghost j) (K.duplex k i) := by
   rw [← even_mix_comm (K.grade_duplex j k) (K.grade_ghost i)]; exact grade_mix_assoc (K.grade_ghost j) (K.grade_ghost k) _
omit [Fintype M] [DecidableEq M] in
private lemma evicts (H : Chased D) (x : J) : cycle (fun i j k => crown D x i j k • mix p (K.ghost i) (K.duplex j k))=0 := by
   let P (i j k : J) := mix p (K.ghost i) (K.duplex j k)
   let F : J→J→J→Term β := fun i j k => crown D x i j k • P i j k
   let G : J→J→J→Term β := fun i j k => F k i j
   have hz : cycle F+cycle G+cycle (fun i j k => G k i j)=0 := by
     simp only [cycle,←sum_add_distrib]; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; apply sum_eq_zero; intro k _; unfold G F P; rw [K.triple k i j,← K.triple i j k,←add_smul,←add_smul,add_right_comm,H,zero_smul] -- maybe
   change cycle F=0; rw [← roll G, show G=(fun i j k => F k i j) from rfl,← roll F] at hz; linear_combination (norm:=module) (1/3:ℂ) • hz
lemma nil_trunk (H : Beats D) (J : Chased D) (a) : K.operate V D (K.trunk D a)=0 := by
   rw [K.spout H]; simp only [neg_eq_zero]; rw [sum_comm]
   -- Beats writes coefficient to F rotation
   have he (j : _) (i : _) : (D a i j:ℂ) = -(D a j i:ℂ) := by rw [H a i j, Complex.ofReal_neg]
   simp only [trunk,mix_smul_last,mix_sum_last,smul_sum,smul_smul];
   have hu j : ∑ i, (∑ l,∑ k,(↑(D a i j)*(-(1/2:ℂ) * ↑(D i l k))) • mix p (K.ghost j) (K.duplex l k)) = (1/2:ℂ) • (∑ l,∑ k, crown D a j l k • mix p (K.ghost j) (K.duplex l k)) := by
     simp only [crown,smul_sum,sum_smul,smul_smul]; rw [sum_comm]; apply sum_congr rfl; intro l _; rw [sum_comm]; apply sum_congr rfl; intro k _; apply sum_congr rfl; intro i _; rw [he j i]; congr 1; ring
   -- refactor smul
   simp_rw [hu]; rw [← smul_sum]; exact smul_eq_zero_of_right _ (K.evicts J a)
lemma nil_lift (H : Beats D) (F : Chased D) (h : ∀ j,Eager (V j) 0) (G : TurnsAlong V D) (a : M ⊕ J) : K.operate V D (K.lift V D a)=0 := by cases a; apply K.represents h G; apply K.nil_trunk H F
end YM.MSBar.Origin.Charm
