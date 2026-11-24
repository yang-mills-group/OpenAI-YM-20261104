import YM.Comparison.RG02.Moving.Bill
/-!
# Finite polynomial tests with analytic scalar coefficients

Not a completion for Uniform reading. Costs never infer these test moments are priced in
 any volume-independent way. Use to first establish the algebraic Wick agreement
 (no interpolated inverse costs!) and combine differentiation operations on finite periodic arrays.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Moving
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree YM.Next.Rank
open YM.Precision YM.Next.SectorChange Gaussian Affinity Matrix Cumulants
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I J : Type} {X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
-- analytic polynomial-carrier over any labels; same test weights in summing coefficients
inductive Fibre : (X→Normal.poly I) → Prop
| cell (f : X→ℂ) (hf : ContDiffAt ℝ ω f 0) (p : Normal.poly I) : Fibre (fun x=> f x • p)
| total {f g : X→Normal.poly I} : Fibre f → Fibre g → Fibre (f+g)

namespace Fibre
variable {f g : X → Normal.poly I} (h : Fibre f)
include h in
lemma scale (p : X→ℂ) (hp : ContDiffAt ℝ ω p 0) : Fibre (fun x=>p x • f x):= by
   induction h with
   | cell f h x=> simpa only [smul_smul] using (Fibre.cell (fun y=>p y*f y) (hp.mul h) x)
   | total _ _ l r=> simp_rw [Pi.add_apply, smul_add]; exact l.total r
include h in
lemma bump (p : X→ℂ) (hp : ContDiffAt ℝ ω p 0) (q : Normal.poly I) : Fibre (f*(fun x=>p x • q)):= by
   induction h with
   | cell r l s=>
      simp only [Pi.mul_def,smul_mul_assoc, mul_smul_comm, smul_smul]; exact cell (fun x=>p x * r x) (hp.mul l) (s*q)
   | total _ _ l r=> rw [add_mul]; exact l.total r
include h in
lemma product (he : Fibre g) : Fibre (f*g) := by
   induction he with | cell p hp q=> exact h.bump p hp q | total _ _ l r=> rw [mul_add]; exact l.total r
lemma constant (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] (z : Normal.poly I) : Fibre (fun _:X=> z) := by simpa only [one_smul] using cell (fun _:X=>1) contDiffAt_const z
lemma sum {Y : Type*} (t : Finset Y) (p : Y→X→Normal.poly I) (h : ∀ i∈t, Fibre (p i)) : Fibre (fun x=> ∑ i∈t,p i x) := by
  induction t using Finset.induction with
  | empty=> simp only [sum_empty]; exact constant _ _
  | insert j V hj ih => simp_rw [sum_insert hj]; exact (h _ (mem_insert_self ..)).total (ih (fun i hi=>h i (mem_insert_of_mem hi)))

include h in
lemma maps {T : E→X} (he : T 0=0) (hk : ContDiffAt ℝ ω T 0) : Fibre (f ∘ T):= by
    induction h with
    | cell p h q=> exact cell (p ∘ T) ((he.symm ▸ h : ContDiffAt ℝ ω p (T 0)).comp 0 hk) q
    | total _ _ l r=> exact l.total r
include h in
lemma known (P : Normal.poly I→ₗ[ℂ]ℂ) : ContDiffAt ℝ ω (P ∘ f) 0 := by
    induction h with
    | cell p h q=> simp_rw [Function.comp_def,_root_.map_smul]; exact h.smul contDiffAt_const
    | @total f g _ _ l r=> simp_rw [Function.comp_def,Pi.add_apply,_root_.map_add]; exact l.add r

-- k-order jet test evaluated on **any analytic direction**
include h in
lemma assay (x:X) (k:ℕ) : ∃ p : Normal.poly I, ∀ L : Normal.poly I→ₗ[ℂ]ℂ, Assembly.jet (L ∘ f) k x=L p := by
    induction h with
    | cell f h p =>
      refine ⟨Assembly.jet f k x • p,fun L=>?_⟩
      let Q := ContinuousLinearMap.mul ℝ ℂ (L p)
      have hx : (L ∘ (fun y=> f y • p))= Q ∘ f := funext fun y=> (_root_.map_smul L _ p).trans (mul_comm (f y) (L p)) -- coerces
      rw [hx,_root_.map_smul,← jet_apply_left Q f k (h.of_le le_top)]; exact mul_comm _ _
    | @total f g hf hg l r =>
      obtain ⟨u,hu⟩:=l; obtain ⟨v,hv⟩:=r; refine ⟨u+v,fun L=>?_⟩
      rw [_root_.map_add, ← hu,← hv, show (L∘ (f+g))=(L∘f) + (L∘g) from funext (fun y=> _root_.map_add L _ _)]
      unfold Assembly.jet; rw [iteratedFDeriv_add_apply ((hf.known L).of_le le_top) ((hg.known L).of_le le_top), _root_.add_apply, smul_add]

lemma polynomial (p : Normal.poly J) {A : J→X→Normal.poly I} (ht : ∀ i,Fibre (A i)) : Fibre (fun x=> MvPolynomial.aeval (fun i=> A i x) p) := by
   induction p using MvPolynomial.induction_on with
   | C w=> simp_rw [MvPolynomial.aeval_C]; exact constant _ _
   | add p q hp hq=> simp_rw [_root_.map_add]; exact hp.total hq
   | mul_X p i h=> simp_rw [_root_.map_mul,MvPolynomial.aeval_X]; exact h.product (ht i)
end Fibre

namespace Field
variable [Fintype I] [DecidableEq I] [FiniteDimensional ℝ X]
local notation "δ" => Regulator X
local notation "Pt" => Normal.poly I
variable (C : Field X I) (s : Regulator X)
def leaves (i : I) : Normal.poly I := ∑ j : I, (C.B s i j:ℂ) • MvPolynomial.X j
lemma testify (i : I) (v:I→ℝ) : Cloud.paint v (C.leaves s i) = (↑((C.B s *ᵥ v) i):ℂ) := by
   simp_rw [leaves,_root_.map_sum,_root_.map_smul,MvPolynomial.aeval_X,smul_eq_mul, Matrix.mulVec,dotProduct,Complex.ofReal_sum,Complex.ofReal_mul]
lemma leaves_live (i : I) : Fibre (fun s=>C.leaves s i) := Fibre.sum Finset.univ _ fun j _=> Fibre.cell _ (Complex.ofRealCLM.contDiff.contDiffAt.comp (0:δ) (YM.Push.Loops.matrix_component C.B_smooth i j)) _
-- presentation for Rotation.quote

def sheet (p : Normal.poly I) := MvPolynomial.aeval (C.leaves s) p
lemma sheet_live (p : Pt) : Fibre (fun s=>C.sheet s p) := Fibre.polynomial p fun i=> leaves_live C i
lemma sheet_reads (v:I→ℝ) (p:Pt) : Cloud.paint v (C.sheet s p) = Cloud.paint (C.B s *ᵥ v) p := by
   unfold sheet; induction p using MvPolynomial.induction_on with
   | C w=> simp
   | add p q hp hq=> rw [_root_.map_add,_root_.map_add,_root_.map_add,hp,hq]
   | mul_X p j h=> rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,h,MvPolynomial.aeval_X, testify]; simp -- edit

variable {s}
lemma uses_wick (he : (C.B s).transpose*C.gram s*C.B s=C.gram 0) (h : 0<(C.B s).det) (p : Pt) :
   Cloud.wick (C.Q s) (C.symmetric s) 0 p= Cloud.wick (C.Q 0) (C.symmetric 0) 0 (C.sheet s p) := by
   rw [← Cloud.shift_zero,← (Cloud.paid _ (C.symmetric s) (C.known h.ne' he|>.posSemidef) 0 p).2,← (Cloud.paid _ (C.symmetric 0) C.flat.posSemidef 0 (C.sheet s p)).2]; simp_rw [zero_add,sheet_reads]; exact (C.port he h (fun v=> Cloud.paint v p)).2
lemma wick_stays (p:Pt) : ContDiffAt ℝ ω (fun s=> Cloud.wick (C.Q s) (C.symmetric s) 0 p) 0 := by
   refine ((sheet_live C p).known (Cloud.wick (C.Q 0) (C.symmetric 0) 0)).congr_of_eventuallyEq ?_; filter_upwards [C.rotated,C.B_lives] with x hx h; exact uses_wick C hx h _
end Field
end YM.Comparison.RG02.Moving
