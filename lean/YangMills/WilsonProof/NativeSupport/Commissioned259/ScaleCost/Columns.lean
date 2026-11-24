import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Crop
import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Pick
/-! # Coordinates of compositions in the T-powers iteration of G.1

Here matrices act on vectors (index convention opposite to `Cast` seats). Keep powers
componentwise to reuse the grading and Fare technology.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.ScaleCost
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 Matrix
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale O.Score O.Enh O.Canon Dframe Comparing MS.Book.Program
variable {G : Gauge} {h : ℕ} {V : Arenas G} {B : ℝ → Frames G} {R : ℝ→PowerSeries ℂ}
open Reg.Point
lemma shifted (u : Cn) (s : ℝ) :
    stepV (d:=h) u (conversion (G:=G) B s h) = C (Level.Dial h s) * stepV u (B s h) := by
  ext1 i
  simp only [stepV,coeff_mk, rules,conversion,coeff_C_mul, Finset.mul_sum,mul_smul_comm]
lemma composed (H : Law V R B) (s t : ℝ) :
    conversion B (s+t) h=conversion B s h*stepV (R s) (conversion B t h) := by
  have e := (H.additive s t).2 h
  rw [old_g _ _ (H.ready s h)] at e
  have hz : C (Level.Dial h t)* B s h=B s h * C (Level.Dial h t) := by
    ext1 i; rw [coeff_mul_C, coeff_C_mul, Level.rise _ _ (H.ready s h i)]
  rw [shifted, conversion,conversion,e, ← Level.group, map_mul]
  calc
    _ = C (Level.Dial h s)*(C (Level.Dial h t)*B s h)* stepV (R s) (B t h) := by simp_rw [mul_assoc]
    _ = _ := by rw [hz]; simp_rw [mul_assoc]

def prose (F : Guard G h) (b c : Toon G h) := PowerSeries.mk (fun i=>columns (coeff i F) b c)
lemma prose_mix (F Q : Guard G h) (b c : Toon G h) :
    prose (F*Q) b c=∑ j, prose F b j*prose Q j c := by
  ext1 i
  simp_rw [map_sum, prose, coeff_mk, coeff_mul]
  unfold columns
  rw [LinearMap.sum_apply, map_sum, Finset.sum_comm (s:=Finset.univ)]
  refine Finset.sum_congr rfl fun j _=>Eq.symm ?_
  simp_rw [coeff_mk]; exact congr_arg (fun A:Matrix (Toon G h) (Toon G h) ℂ=>A b c) (Comparing.composition' (coeff j.1 F) (coeff j.2 Q))
lemma prose_subst (F : Guard G h) (u : Cn) (hu : Rooted u) (b c : Toon G h) :
    prose (stepV u F) b c=(prose F b c).subst u := by
  ext1 i; rw [ ← Dframe.Constants.actual_subst _ _ hu]; simp_rw [prose,coeff_mk, rules, stepV,coeff_mk,
    rules,columns,LinearMap.sum_apply,map_sum,LinearMap.smul_apply,_root_.map_smul]
lemma column_composition (H : Law V R B) (s t : ℝ) (b c : Toon G h) :
    badge B (s+t) (theory c) b=∑ j : Toon G h, badge B s (theory j) b * ((badge B t (theory c) j).subst (R s)) := by
  change prose (conversion B (s+t) h) b c=∑ j:Toon G h, prose (conversion B s h) b j * ((prose (conversion B t h) j c).subst _)
  rw [composed H, prose_mix]; simp_rw [prose_subst _ _ (H.led s|>.start)]
lemma fee_matrix (T : ℝ) (b c : Toon G h) (p : ℕ) (t : ℝ) :
    columns (∑ i∈Finset.range (p+1), (t:ℂ)^i • coeff i (conversion B T h)) b c =
      crop p t (badge B T (theory c) b) := by
  unfold columns; simp_rw [LinearMap.sum_apply,map_sum,LinearMap.smul_apply,_root_.map_smul, crop_apply,badge,coeff_mk,smul_eq_mul]

abbrev form (B : ℝ→Frames G) (h : ℕ) (T : ℝ) (p : ℕ) (t : ℝ) : Matrix (Toon G h) (Toon G h) ℂ :=
  fun b c=>crop p t (badge B (-Real.log T) (theory c) b)

-- prefer explicit norm convention ∑_{i,j} |X ij| for presentation (equivalent all through fixed cap)
def stiffness {d e : ℕ} (x : Matrix (Toon G d) (Toon G e) ℂ) := ∑ i : Toon G d, ∑ j : Toon G e, ‖x i j‖
lemma stiffPos {d e : ℕ} (x : Matrix (Toon G d) (Toon G e) ℂ) : 0 ≤ stiffness x := Finset.sum_nonneg fun i _=> Finset.sum_nonneg fun j _=>norm_nonneg _
lemma leanFee {d e : ℕ} (x : Matrix (Toon G d) (Toon G e) ℂ) (i j) : ‖x i j‖ ≤ stiffness x :=
  (Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset (Toon G e)))=>norm_nonneg (x i k)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _=>Finset.sum_nonneg (f:=fun j : Toon G e=> ‖x k j‖) (fun j _=> norm_nonneg _)) (Finset.mem_univ i))
lemma stiffPay {I:Type*} {d e : ℕ} {X : Filter I} {T f : I→ℝ} (ht : ∀ᶠ i in X, 1 ≤ T i) {A : I→Matrix (Toon G d) (Toon G e) ℂ}
    (h : ∀ i j,Fare T X f (fun k=> A k i j)) : Fare T X f (stiffness ∘ A) := by
  apply Fare.sum ht; intro i _; apply Fare.sum ht; intro j _
  obtain ⟨p,h⟩:= h i j; exact ⟨p,isBigO_norm_left.mpr h⟩
lemma matrixPay {I:Type*} {d e : ℕ} {X : Filter I} {f : I→ℝ} {A : I→Matrix (Toon G d) (Toon G e) ℂ} :
    (stiffness ∘ A)=O[X] f ↔ ∀ i j,(fun k=> A k i j)=O[X] f := by
  constructor <;> intro h
  · exact fun i j=> (IsBigO.of_bound' <| Eventually.of_forall fun k=> (leanFee (A k) i j).trans_eq
      (Real.norm_of_nonneg (stiffPos _)).symm).trans h
  exact IsBigO.sum fun i (_:i∈(Finset.univ:Finset (Toon G d))) => IsBigO.sum fun j (_:j∈(Finset.univ:Finset (Toon G e))) => isBigO_norm_left.mpr (h i j)
lemma stiffMul {k d e : ℕ} (x : Matrix (Toon G k) (Toon G d) ℂ) (y : Matrix (Toon G d) (Toon G e) ℂ) :
    stiffness (x*y) ≤ stiffness x * stiffness y := by
  unfold stiffness; simp_rw [ Matrix.mul_apply, Finset.sum_mul ]; refine Finset.sum_le_sum fun i _=>?_
  calc _ ≤ ∑ j, ∑ k, ‖x i k * y k j‖ := Finset.sum_le_sum fun j _=> norm_sum_le ..
       _ = ∑ k, ‖x i k‖ * ∑ j, ‖y k j‖ := by simp_rw [norm_mul,Finset.mul_sum]; exact Finset.sum_comm
       _ ≤ _ := Finset.sum_le_sum fun g _=>mul_le_mul_of_nonneg_left
         (Finset.single_le_sum (fun k _=>Finset.sum_nonneg (fun j _=>norm_nonneg (y k j))) (Finset.mem_univ g)) (norm_nonneg _)
lemma stiffAdd {d e : ℕ} (x y : Matrix (Toon G d) (Toon G e) ℂ) : stiffness (x+y) ≤ stiffness x + stiffness y := by
  unfold stiffness; rw [← Finset.sum_add_distrib]; apply Finset.sum_le_sum; intro i _; rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun j _=> norm_add_le ..
end YM.FVA2.GradedFar259.ScaleCost
