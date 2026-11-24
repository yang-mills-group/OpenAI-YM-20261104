import YM.Integration.PhysicalWilsonSignedOutput
import YM.Integration.ZeroAwareCappedCreditPolynomial
import YM.Integration.ActualGradedVacuum

/-! Lower perturbative order on the very same positive Wilson plan and its paid curvature layers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalVacuumOrderRestriction

open Function Filter Finset Lattice Wilson RG Precision Exterior
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global FullQLocal
open Comparison.RG02 Comparison.RG02.Assembly PhysicalWilsonActionConvention
open scoped Topology BigOperators ContDiff Classical

variable {G : Gauge} {n : Side}

def held (S : List (Piece G n)) (p : ℕ) := S.filter fun a => decide (a.power≤p)

def extra (S : List (Piece G n)) (p : ℕ) := S.filter fun a => decide (p<a.power)

def plan {C : Family G} {N t q : ℕ} (P : Plan C N t q) (p : ℕ) : Plan C N t p where
  layers m := held (P.layers m) p
  coefficient := P.coefficient
  alpha := P.alpha
  orders m hm a ha := by
    have h := List.mem_filter.mp ha
    exact ⟨(P.orders m hm a h.1).1,of_decide_eq_true h.2⟩

private theorem split (S : List (Piece G n)) (p : ℕ) (f : Piece G n → ℝ) :
    (S.map f).sum = ((held S p).map f).sum + ((extra S p).map f).sum := by
  induction S with
  | nil => simp [held,extra]
  | cons a S ih =>
    by_cases h : a.power≤p
    · simpa [held,extra,h,show ¬p<a.power from not_lt.mpr h,add_assoc] using congrArg (f a + ·) ih
    · simpa [held,extra,h,lt_of_not_ge h,add_assoc,add_left_comm] using congrArg (f a + ·) ih

/-- The complete original ordinary action is the sum of the low plan and the omitted
whole fields, at each configuration and physical coupling. -/
theorem restored (S : List (Piece G n)) (p : ℕ) (g : ℝ) (U : Config G n) :
    ActualGradedVacuum.restored S g U = ActualGradedVacuum.restored (held S p) g U +
      ActualGradedVacuum.restored (extra S p) g U := split S p _

theorem masked (S : List (Piece G n)) (p : ℕ) (g : ℝ) (b : BudgetPoint) (U : Config G n) :
    Render.renders (Render.prefactor g) b U S = Render.renders (Render.prefactor g) b U (held S p) +
      Render.renders (Render.prefactor g) b U (extra S p) := by
  induction S with
  | nil => simp [Render.renders,held,extra]
  | cons a S ih =>
    by_cases h : a.power≤p
    · simpa [Render.renders,held,extra,h,show ¬p<a.power from not_lt.mpr h,add_assoc]
        using congrArg (Render.prefactor g a * a.packet.amount b U + ·) ih
    · simpa [Render.renders,held,extra,h,lt_of_not_ge h,add_assoc,add_left_comm]
        using congrArg (Render.prefactor g a * a.packet.amount b U + ·) ih

theorem compulsory (S : List (Piece G n)) (weight : Piece G n→ℝ) (E : Activities G n) :
    (Render.adorn weight E S).forced=E.forced ∧ (Render.adorn weight E S).K=E.K := by
  induction S with
  | nil => exact ⟨rfl,rfl⟩
  | cons a S ih => exact ih

private theorem graded_sum (S : List (Piece G n)) {p : ℕ}
    (f : Piece G n → (ℝ × fieldDir G n 1) → ℝ)
    (paid : ∀ a∈S,GradeAt p (f a)) : GradeAt p (fun y => (S.map (fun a=>f a y)).sum) := by
  induction S with
  | nil => exact GradeAt.grade_zero p
  | cons a S ih => exact (paid a List.mem_cons_self).add (ih (fun b hb => paid b (List.mem_cons_of_mem a hb)))

/-- In cleared joint variables the true discarded ordinary action has no coefficient through p+2. -/
theorem joint_grade {S : List (Piece G n)} {b : BudgetPoint} {q rank : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers S b q rank width budget) (hw : 0<width) (p : ℕ) :
    GradeAt (p+3) (fun y : ℝ × fieldDir G n 1 =>
      ActualGradedVacuum.restored (extra S p) y.1 (represent y.2)) := by
  apply graded_sum
  intro a ha
  have h := List.mem_filter.mp ha
  have hdeg : p<a.power := of_decide_eq_true h.2
  have hrank := H.leading_rank a h.1
  have hs := GradeAt.shifts (fun y : ℝ × fieldDir G n 1 => y.1)
    contDiffAt_fst rfl (a.power+2-a.rank)
  have hA := (ActualGradedVacuum.payload_grade H hw a h.1).coarse
    (g:=fun y : ℝ × fieldDir G n 1 => y.2) contDiffAt_snd rfl
  have hk : p+3≤(a.power+2-a.rank)+a.rank := by omega
  simpa only [Function.comp_apply,smul_eq_mul] using (hs.scale hA).lower hk

private theorem weighted_sum (S : List (Piece G n)) (p : ℕ) (f w : Piece G n→ℝ) (t : ℝ)
    (hn : ∀ a∈S,0≤w a) (ht : 0≤t) (owned : ∀ a∈S,p<a.power → f a≤t*w a) :
    ((extra S p).map f).sum ≤ t*(S.map w).sum := by
  induction S with
  | nil => simp [extra]
  | cons a S ih =>
    have rest := ih (fun b hb => hn b (List.mem_cons_of_mem a hb))
      (fun b hb => owned b (List.mem_cons_of_mem a hb))
    by_cases hx : p<a.power
    · simpa [extra,hx,mul_add] using add_le_add (owned a List.mem_cons_self hx) rest
    · simpa [extra,hx,mul_add] using
        rest.trans (le_add_of_nonneg_left (mul_nonneg ht (hn a List.mem_cons_self)))

def debit {S : List (Piece G n)} {b : BudgetPoint} {rank : ℕ} {width budget : ℝ}
    (H : ZeroAwareVacuumPackets S b rank width budget) (p : ℕ) (g : ℝ) : ℝ :=
  ((extra S p).map (fun a => ‖Render.prefactor g a‖*ZeroAwareCappedRenderInvoice.credit H a)).sum

/-- All numerical constants precede all physical periods, original source banks and pieces.
The actual physical coupling and the requested support radius remain displayed. -/
theorem priced (G : Gauge) (rank order distance : ℕ) : ∃ C : ℝ,0<C ∧ ∃ d : ℕ,
    ∀ {n : Side} {S : List (Piece G n)} {b : BudgetPoint} {width budget : ℝ}
      (H : ZeroAwareVacuumPackets S b rank width budget), b.order=order → b.power=distance →
      0<width → Render.permits S b → ∀ (p : ℕ) (g W : ℝ), 0<g → g≤1 → 1≤W → b.threshold/g≤W →
      (∀ a∈extra S p, a.packet.Invoice b (ZeroAwareCappedRenderInvoice.credit H a)) ∧
      debit H p g ≤ C*budget^2*(1+width⁻¹)^d*W^rank*g^(p+1) := by
  obtain ⟨C,hC,d,hCrd⟩ := ZeroAwareCappedCreditPolynomial.credit_bound G rank order distance
  refine ⟨C,hC,d,?_⟩
  intro n S b width budget H ho hd hw permits p g W hg hg1 hW hratio
  refine ⟨fun a ha => ZeroAwareCappedRenderInvoice.invoice H permits hw a (List.mem_filter.mp ha).1,?_⟩
  have hB : 0≤budget := (Real.exp_pos _).le.trans H.cover_cost
  have hwidth : 0≤1+width⁻¹ := by positivity
  let t := C*(1+width⁻¹)^d*budget*W^rank*g^(p+1)
  have ht : 0≤t := by dsimp only [t]; positivity
  have charged (a : Piece G n) (ha : a∈S) (hx : p<a.power) :
      ‖Render.prefactor g a‖*ZeroAwareCappedRenderInvoice.credit H a ≤ t*H.pieceCost a := by
    have hr := H.rank_bounded a ha
    have hm : ‖Render.prefactor g a‖*b.threshold^a.rank = g^a.power*(b.threshold/g)^a.rank := by
      rw [Render.prefactor,Render.stepOrder,Real.norm_of_nonneg (zpow_nonneg hg.le _),
        zpow_natCast_sub_natCast₀ hg.ne',div_pow]
      ring
    have small := pow_le_pow_of_le_one hg.le hg1 hx
    have large := (pow_le_pow_left₀ (div_nonneg b.threshold_pos.le hg.le) hratio a.rank).trans
      (pow_le_pow_right₀ hW hr)
    have tariff := mul_le_mul small large (pow_nonneg (div_nonneg b.threshold_pos.le hg.le) _)
      (pow_nonneg hg.le _)
    calc
      _ ≤ ‖Render.prefactor g a‖*(C*b.threshold^a.rank*(1+width⁻¹)^d*budget*H.pieceCost a) :=
        mul_le_mul_of_nonneg_left (hCrd H ho hd hw a ha) (norm_nonneg _)
      _ = (g^a.power*(b.threshold/g)^a.rank) * (C*(1+width⁻¹)^d*budget*H.pieceCost a) := by
        rw [← hm]; ring
      _ ≤ (g^(p+1)*W^rank) * (C*(1+width⁻¹)^d*budget*H.pieceCost a) :=
        mul_le_mul_of_nonneg_right tariff (by have := H.piece_cost_nonnegative a ha; positivity)
      _ = t*H.pieceCost a := by dsimp only [t]; ring
  exact (weighted_sum S p _ H.pieceCost t H.piece_cost_nonnegative ht charged).trans
    ((mul_le_mul_of_nonneg_left H.total ht).trans_eq (by dsimp only [t];ring))

end YM.Integration.QLocalVacuumOrderRestriction
end
