import YM.Integration.WilsonMatrixTicketLanesNormalizedFleetLog

/-! A quadratic joint source differentiates just one member of its actual compatible cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesNormalizedFleetVariation

open Function Finset Marker Extra.Trajectories MergeProof Accent
open private vanishing vanish_mul from YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra
open scoped BigOperators Classical
variable {I V : Type} [DecidableEq I] [DecidableEq V] {J : Census V}

private theorem below {D : Poly J} (high : rises D) (s : J.Mode) (small : s.val.card < 2) :
    D.part s = 0 := by
  by_contra nz
  exact (not_le_of_gt small) (high s nz)

private theorem one_factor (A D : Poly J) (high : rises D) (s : J.Mode) (small : s.val.card ≤ 2) :
    (A * D).part s = A.part J.quiet * D.part s := by
  have zero : (A - Poly.bead J (A.part J.quiet)).part J.quiet = 0 := by
    simp [Poly.bead]
  have high' : vanishing D 1 := fun t small => below high t (by omega)
  have marked := vanish_mul high' zero s small
  rw [mul_sub,part_sub,mul_comm D A,mul_comm D (Poly.bead J _),Poly.product_bead,Poly.part_smul] at marked
  exact sub_eq_zero.mp marked

def variation (A D : I → Poly J) (s : J.Mode) (b : Finset I) : ℂ :=
  ∑ i ∈ b, (D i).part s * ∏ j ∈ b.erase i, (A j).part J.quiet

private theorem variation_insert (A D : I → Poly J) (s : J.Mode) (b : Finset I) (a : I) (ha : a ∉ b) :
    variation A D s (insert a b) =
      (D a).part s * (∏ j ∈ b, (A j).part J.quiet) + (A a).part J.quiet * variation A D s b := by
  simp only [variation,Finset.sum_insert ha,Finset.erase_insert ha,Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have ne : a ≠ i := fun h => ha (h ▸ hi)
  rw [Finset.erase_insert_of_ne ne,Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
  ring

theorem cover (A D : I → Poly J) (high : ∀ i, rises (D i)) (b : Finset I) :
    ∀ s : J.Mode, s.val.card ≤ 2 →
      (∏ i ∈ b, (A i + D i)).part s - (∏ i ∈ b, A i).part s = variation A D s b := by
  induction b using Finset.induction_on with
  | empty => intro s small; simp [variation]
  | @insert a b ha ih =>
    let X := ∏ i ∈ b, (A i + D i)
    let Y := ∏ i ∈ b, A i
    have extend : rises (X - Y) := by
      intro t nz
      by_contra! low
      have exact := ih t (by omega)
      have z : variation A D t b = 0 := Finset.sum_eq_zero fun i _ => by rw [below (high i) t low,zero_mul]
      exact nz (by rw [part_sub]; exact exact.trans z)
    have zero : X.part J.quiet = Y.part J.quiet := by
      apply sub_eq_zero.mp
      rw [← part_sub]
      exact below extend _ (by simp [Census.quiet])
    have scalar (r : Finset I) : (∏ i ∈ r, A i).part J.quiet = ∏ i ∈ r, (A i).part J.quiet := by
      induction r using Finset.induction_on with
      | empty => simp
      | insert z r zr hr => simp [zr,Poly.quiet_mul,hr]
    intro s small
    rw [Finset.prod_insert ha,Finset.prod_insert ha,← part_sub]
    change ((A a + D a) * X - A a * Y).part s = _
    rw [show (A a + D a) * X - A a * Y = X * D a + A a * (X - Y) from by ring]
    rw [Poly.part_plus,one_factor X (D a) (high a) s small,one_factor (A a) (X - Y) extend s small,
      zero,part_sub,ih s small,variation_insert A D s b a ha]
    simp only [Y,scalar,mul_comm]

/-- The exterior competitors in every original pattern remain inside the finite sum. -/
theorem field {n : Lattice.Side} (A D : Box n → Poly J) (high : ∀ i, rises (D i))
    (flags : Lattice.Support n) (s : J.Mode) (small : s.val.card ≤ 2) :
    (Accent.field (fun i => A i + D i) flags).part s - (Accent.field A flags).part s =
      ∑ b : Finset (Box n), if Pattern flags b then variation A D s b else 0 := by
  simp only [Accent.field,Poly.part_sum,← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases actual : Pattern flags b
  · simp only [grid,if_pos actual]
    exact cover A D high b s small
  · simp [grid,actual]

end YM.Integration.WilsonMatrixTicketLanesNormalizedFleetVariation
