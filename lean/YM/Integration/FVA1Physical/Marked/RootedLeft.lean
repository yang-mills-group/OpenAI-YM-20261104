import YM.Trace.Physicalv2.LogAccuracy
import YM.RGComparison.Core16.Catkin.Thicket
import YM.Corona.Fit
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Term
import YM.LocalLTE.Concourse.Core

/-! Spatially resolved left derivatives of an exact, normalized, grade-zero
source density. The regular representatives are cylindrical before masking.
Every derivative direction that survives must belong to the same support as
the marked origin. The genuine support reserve pays all those distances. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Finset Lattice RG YM.Wilson Source Further.LogJets PhysicalNext.Repeat.Boulevard
open Push.AbsoluteSums RGComparison.Core16.Lam RGComparison.Core16.Catkin
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side} {p : BudgetPoint}

def wordRadius (o : Site n) (l : List (Operand G n)) : ℕ :=
  (l.map (fun x=>separation o (crest x))).sum

private theorem wordRadius_le {o : Site n} {X : Support n} (hx : o ∈ X)
    (l : List (Operand G n)) (all : ∀ a ∈ l, crest a ∈ X) :
    wordRadius o l ≤ l.length * ((6*p.B+2)*coverNumber p.B X) := by
  have one {a : Operand G n} (ha : crest a ∈ X) : separation o (crest a) ≤ (6*p.B+2)*coverNumber p.B X := by
    have HC : 1 ≤ coverNumber p.B X := (Animals.price_pos p.B X).2 ⟨_,hx⟩
    have m:=Corona.extent X p.B hx ha
    nlinarith only [m,Nat.mul_le_mul_left (2*p.B) HC]
  induction l with
  | nil => simp [wordRadius]
  | cons x l ih =>
    change separation o (crest x)+wordRadius o l ≤ (l.length+1)*_
    rw [Nat.add_mul,one_mul]
    exact (Nat.add_le_add (one (all _ List.mem_cons_self)) (ih (fun i h=>all i (List.mem_cons_of_mem _ h)))).trans_eq (Nat.add_comm ..)

private theorem zero_member (f : Config G n → ℂ) (l : List (Directions G n)) (h : 0 ∈ l) :
    leftDerivs f l = 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.mp h with h|h
    · subst a; funext U; simp only [leftDerivs,smul_zero,Work.G07.at_zero_increment,deriv_const',Pi.zero_apply]
    · funext U; simp [leftDerivs,ih h]

private theorem unused_direction {X : Support n} {f : Config G n → ℂ} (h : LocalOn X f)
    (l : List (Operand G n)) {a : Operand G n} (ha : a ∈ l) (off : crest a ∉ X) (U : Config G n) :
    leftDerivs f (l.map compass) U=0 := by
  have hide : Trace.Physical.LogAccuracy.slim X (compass a)=0 := by
    funext e; unfold Trace.Physical.LogAccuracy.slim compass
    split_ifs with he
    · have ne : e ≠ a.1 := by
        intro eq; apply off; change a.1.1 ∈ X; rwa [eq] at he
      exact Pi.single_eq_of_ne ne _
    · rfl
  have cut := Trace.Physical.LogAccuracy.directed_agrees X h (l.map compass) (V:=U) (U:=U) (fun _ _ _=>rfl)
  rw [cut,zero_member f _ (List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨a,ha,rfl⟩,hide⟩),Pi.zero_apply]

private theorem word_factor {o : Site n} {X : Support n} {f : Config G n → ℂ} {v α : ℝ}
    (smooth : p.Regular X f) (bound : p.supBounds o X f v) (hx : o ∈ X) (l : List (Operand G n))
    (length : l.length ≤ p.order) (pos : 0 ≤ α)
    (room : α * l.length * (6*p.B+2:ℝ) ≤ p.supportExponent)
    (U : Config G n) (health : Healthy p.threshold X U) :
    Real.exp (α*wordRadius o l) * ‖leftDerivs f (l.map compass) U‖ ≤
      (p.threshold⁻¹)^l.length * p.mass X v := by
  by_cases all : ∀ a ∈ l, crest a ∈ X
  · have cost : α*(wordRadius o l:ℝ) ≤ p.supportExponent*coverNumber p.B X := by
      have dist : (wordRadius o l:ℝ) ≤ l.length*((6*p.B+2:ℝ)*coverNumber p.B X) := by exact_mod_cast wordRadius_le (p:=p) hx l all
      calc _ ≤ α*((l.length:ℝ)*((6*p.B+2:ℝ)*coverNumber p.B X)) := mul_le_mul_of_nonneg_left dist pos
           _ = (α*l.length*(6*p.B+2:ℝ))*coverNumber p.B X := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_right room (Nat.cast_nonneg _)
    have raw := Push.Local.bound_rescale_dirs bound smooth U health (l.map compass)
      (by simpa using length) p.threshold⁻¹ (inv_pos.mpr p.threshold_pos) (by
        intro Z hz e; obtain ⟨x,_,rfl⟩:=List.mem_map.mp hz
        rw [←mul_assoc,inv_mul_cancel₀ p.threshold_pos.ne',one_mul]
        exact (compass_fee _ e).trans (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))))
    simp only [List.length_map] at raw
    refine (mul_le_mul (Real.exp_le_exp.mpr cost) raw (norm_nonneg _) (Real.exp_pos _).le).trans_eq ?_
    unfold BudgetPoint.mass; ring
  · push Not at all; obtain ⟨a,ha,hn⟩:=all
    rw [unused_direction smooth.sites l ha hn U,norm_zero,mul_zero]
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr p.threshold_pos.le) _) (mul_nonneg (Real.exp_pos _).le bound.1)

theorem complex_termwise {ı : Type*} {o : Site n} {X : ı → Support n} {f : ı → Config G n → ℂ}
    {v : ı → ℝ} {h : ℝ} (smooth : ∀ i,p.Regular (X i) (f i))
    (limits : ∀ i,p.supBounds o (X i) (f i) (v i))
    (credit : SumBudget (fun i=>p.mass (X i) (v i)) h) :
    Termwise p.order (sunny p) f := by
  have hX (i : ı) {U : Config G n} (hu : U ∈ sunny p) : Healthy p.threshold (X i) U := by
    unfold Healthy; rw [smoky hu]; simp
  refine ⟨fun i U hu=>(smooth i).smooth _ (hX i hu),?_⟩
  intro l hl
  let d : ℝ := p.threshold+∑ z ∈ l.toFinset,‖z‖
  have hd : 0 < d := add_pos_of_pos_of_nonneg p.threshold_pos (sum_nonneg (fun _ _=>norm_nonneg _))
  have all {z : Directions G n} (hz : z ∈ l) : ‖z‖ ≤ d :=
    (single_le_sum (fun a _=>norm_nonneg a) (List.mem_toFinset.mpr hz)).trans (le_add_of_nonneg_left p.threshold_pos.le)
  let C:=d/p.threshold
  have cp : 0 < C := div_pos hd p.threshold_pos
  have unweighted:=budget_mono credit (fun i=>(limits i).1) (fun i=>p.loMass _ _ (limits i).1)
  refine ⟨fun i=>C^l.length*v i,unweighted.2.1.mul_left _,fun i U hu=>?_⟩
  apply Push.Local.bound_rescale_dirs (limits i) (smooth i) U (hX _ hu) l hl C cp
  intro z hz e
  have scale : C*p.threshold=d := div_mul_cancel₀ d p.threshold_pos.ne'
  rw [←mul_assoc,scale]
  exact ((norm_le_pi_norm z e).trans (all hz)).trans (le_mul_of_one_le_right hd.le
    (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))))

/-- Every ordered link/color derivative of the whole regular source, with its
true spatial exponential and its original countable support account. -/
theorem rooted_sum {ı : Type*} {o : Site n} {X : ı → Support n} {f : ı → Config G n → ℂ}
    {v : ı → ℝ} {h α : ℝ} (smooth : ∀ i,p.Regular (X i) (f i))
    (limits : ∀ i,p.supBounds o (X i) (f i) (v i)) (root : ∀ i,o ∈ X i)
    (credit : SumBudget (fun i=>p.mass (X i) (v i)) h)
    (l : List (Operand G n)) (length : l.length ≤ p.order)
    (pos : 0 ≤ α) (room : α*l.length*(6*p.B+2:ℝ) ≤ p.supportExponent)
    {U : Config G n} (hu : U ∈ sunny p) :
    Real.exp (α*wordRadius o l)*‖leftDerivs (fun V=>∑' i,f i V) (l.map compass) U‖ ≤ (p.threshold⁻¹)^l.length*h := by
  have L : (l.map compass).length ≤ p.order := by simpa using length
  have exchange:=(complex_termwise smooth limits credit).smooth_exchange (sky _) U hu
  rw [exchange.2 _ L]
  let w:=Real.exp (α*wordRadius o l)
  have price:=budget_mono (budget_scale (pow_nonneg (inv_nonneg.mpr p.threshold_pos.le) l.length) credit)
    (g:=fun i=>w*‖leftDerivs (f i) (l.map compass) U‖) (fun _=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (fun i=>word_factor (smooth i) (limits i) (root i) l length pos room U (by unfold Healthy;rw [smoky hu]; simp))
  have sum:= (complex_termwise smooth limits credit).sums _ L U hu
  refine (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm sum.norm) (Real.exp_pos _).le).trans ?_
  simpa only [tsum_mul_left,w] using price.2.2
end YM.Integration.FVA1Physical.Marked
