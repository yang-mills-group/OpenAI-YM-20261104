import YM.Integration.WilsonLongContactPriorRoots
import YM.MergeProof.Buys

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLongContactPriorModes
open Finset Marker MergeProof Lattice RG
open scoped BigOperators Classical

variable {V ι:Type} [DecidableEq V] [Fintype V] [Fintype ι] {Γ:Census V}
variable {G:Gauge} {n f:Side} {R:Rep G f} (M:ι→Menu.Hat Γ R) (w:V→ℝ)

omit [Fintype V] [Fintype ι] in
/-- Distinct input entries need distinct surviving external labels. -/
theorem degree (s:Finset ι) (v:Γ.Mode) (large:v.val.card<s.card):
    (∏j∈s,Menu.sing (M j) w).part v=0:=by
  classical
  induction s using Finset.induction_on generalizing v with
  | empty => simp at large
  | @insert j s outside ih =>
    rw [Finset.prod_insert outside,mul_comm,Poly.part_mul]
    refine Finset.sum_eq_zero fun x _=>Finset.sum_eq_zero fun y _=>?_
    split <;> rename_i joined
    · by_cases quiet:y=Γ.quiet
      · rw [quiet,(Menu.virtue (M j) w).1,mul_zero]
      have pos:0<y.val.card:=Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (fun h=>quiet (Subtype.ext h)))
      have card:v.val.card=x.val.card+y.val.card:=by rw [←joined.2,Finset.card_union_of_disjoint joined.1]
      rw [Finset.card_insert_of_notMem outside] at large
      rw [ih x (by omega),zero_mul]
    rfl

omit [Fintype ι] in
theorem stopped (s:Finset ι) (large:Fintype.card V<s.card):
    ∏j∈s,Menu.sing (M j) w=0:=by
  ext v
  rw [Poly.part_nil,degree M w s v ((Finset.card_le_univ _).trans_lt large)]

omit [Fintype V] [Fintype ι] in
theorem word (hw:∀v,0<w v) (s:Finset ι):Poly.price w (∏j∈s,Menu.sing (M j) w)≤1:=by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s outside ih =>
    rw [Finset.prod_insert outside]
    refine (Poly.multiplication hw _ _).trans ?_
    exact (mul_le_mul_of_nonneg_left ih (Poly.nonnegative hw _)).trans (by simpa using Menu.paid (M i) hw)

def hard (d:ℕ→Finset ι→ℝ) (i:ℕ):Poly Γ:=
  ∑s:Finset ι,(↑(d i s):ℂ) • ∏j∈s,Menu.sing (M j) w

/-- An input configuration may change every coefficient.  All external modes are summed before the bound. -/
theorem price (hw:∀v,0<w v) (d c:ℕ→Finset ι→ℝ) (bound:∀i s,‖d i s‖≤c i s) (i:ℕ):
    Poly.price w (hard M w d i)≤∑s:Finset ι,if s.card≤Fintype.card V then c i s else 0:=by
  classical
  refine (Poly.batch hw _ _).trans (Finset.sum_le_sum fun s _=>?_)
  by_cases small:s.card≤Fintype.card V
  · rw [if_pos small,Poly.adapted,Complex.norm_real]
    exact (mul_le_mul_of_nonneg_left (word M w hw s) (norm_nonneg _)).trans (by simpa using bound i s)
  · rw [if_neg small,stopped M w s (Nat.lt_of_not_ge small),smul_zero,Poly.zero_price]

theorem rooted (hw:∀v,0<w v) (X:ℕ→Support n) (B:ℕ) {a budget:ℝ} (pos:0≤a)
    (Z:Support n) (selected:Finset ℕ) (d c:ℕ→Finset ι→ℝ) (bound:∀i s,‖d i s‖≤c i s)
    (fee:Ac.Hit X B (fun i=>∑s:Finset ι,if s.card≤Fintype.card V then c i s else 0) a budget):
    ∑i∈Ac.buds X selected Z,Poly.price w (hard M w d i)≤(Z.card:ℝ)*budget:=by
  classical
  apply (Finset.sum_le_sum fun i _=>?_).trans (Ac.demand X B fee Z selected)
  have e:1≤Real.exp (a*coverNumber B (X i)):=Real.one_le_exp (mul_nonneg pos (Nat.cast_nonneg _))
  exact (le_mul_of_one_le_right (Poly.nonnegative hw _) e).trans
    (mul_le_mul_of_nonneg_right (price M w hw d c bound i) (Real.exp_pos _).le)

end YM.Integration.WilsonLongContactPriorModes
