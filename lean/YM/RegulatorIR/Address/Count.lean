import YM.RegulatorIR.Budget.Order

/-!
Integer root volume. l^-4. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Address
open Finset Function Lattice Budget Budget.Tuple Budget.Packet Budget.Tariff Motion Spatial
open scoped ENNReal NNReal BigOperators Classical Topology
variable {d l:ℝ}

def census (l d:ℝ)(x:Room): Finset Cover:= Fintype.piFinset fun i:Axis=> Finset.Icc (⌈(x i-d)/l⌉) (⌊(x i+d)/l⌋)
lemma enroll (l :ℝ)(hl:0<l)(d:ℝ)(x:Room)(w:Cover): w∈census l d x ↔ dist (slide l w) x≤d := by
 rw [census,Fintype.mem_piFinset, dist_eq_norm,pi_norm_le_iff_of_nonempty]; apply forall_congr'; intro i
 rw [Finset.mem_Icc,Int.ceil_le,Int.le_floor,div_le_iff₀ hl,le_div_iff₀ hl,Real.norm_eq_abs,Pi.sub_apply, slide_apply, abs_le]
 constructor <;> rintro ⟨A,B⟩ <;> constructor <;> linarith
lemma total (l : ℝ)(hl:0<l)(hd:0≤d)(x : Room): ((census l d x).card:ℝ) ≤ (1+2*d/l)^4 := by
 unfold census; rw [Fintype.card_piFinset, Nat.cast_prod]; rw [show (1+2*d/l)^4=∏ _:Axis,(1+2*d/l) from by simp]
 apply Finset.prod_le_prod (fun _ _=> by positivity); intro i _
 let A:=(x i-d)/l; let B:=(x i+d)/l
 rw [Int.card_Icc]; by_cases he: ⌈A⌉ ≤ ⌊B⌋
 · rw [← Int.cast_natCast, Int.toNat_of_nonneg (by change (0:ℤ)≤ ⌊B⌋+1-⌈A⌉;omega)]; push_cast
   have h: B-A=2*d/l:=by unfold A B; ring
   change (⌊B⌋:ℝ)+_-(⌈A⌉:ℝ) ≤ _
   linarith [Int.floor_le B,Int.le_ceil A]
 rw [Int.toNat_eq_zero.mpr (by change (⌊B⌋+1-⌈A⌉:ℤ)≤0;omega),Nat.cast_zero]; positivity
lemma total_enn (l:ℝ)(hl:0<l)(hd:0≤d)(x:Room) : ((census l d x).card:ℝ≥0∞) ≤ ENNReal.ofReal ((1+2*d/l)^4):=by simpa using ENNReal.ofReal_le_ofReal (total l hl hd x)
lemma stars (f:Cover→ℝ≥0∞){l d:ℝ}{x:Room} (hl:0<l)(hd:0 ≤ d){c:ℝ≥0∞}(h:∀ i,f i≠0 → dist (slide l i) x ≤ d ∧ f i≤c) : (∑' i,f i) ≤ ENNReal.ofReal ((1+2*d/l)^4)*c:=by
 rw [tsum_eq_sum (s:=census l d x)]; swap
 · intro b hb; by_contra! hh; exact hb ((enroll _ hl _ _ _).mpr (h b hh).1)
 apply le_trans (Finset.sum_le_sum (g:=fun _=>c) (fun i _=>by by_cases he:f i=0; rw [he]; positivity; exact (h i he).2))
 simp only [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_left (total_enn l hl hd x) _
end YM.RegulatorIR.Address
