import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds

/-! The absolute Fourier sum in D dimensions spends D+1 derivatives, uniformly in the truncation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierLattice
open Function Finset
open scoped BigOperators Classical Topology

private def bar (z:ℤ):ℝ:=max 1 |(z:ℝ)|

private theorem unitBar (z:ℤ):0<bar z:=lt_of_lt_of_le zero_lt_one (le_max_left ..)

private theorem axis {p:ℝ}(hp:1<p):Summable (fun z:ℤ=>bar z ^ (-p)):=by
  let d:ℤ→ℝ:=Pi.single 0 1
  have atom:Summable d:=summable_of_hasFiniteSupport ((Set.finite_singleton 0).subset (by
    intro i hi; by_contra he; exact hi (show d i=0 from by simp_all [d])))
  refine Summable.of_nonneg_of_le (fun z=>Real.rpow_nonneg (unitBar z).le _) (fun z=>?_) ((Real.summable_abs_int_rpow hp).add atom)
  by_cases hz:z=0
  · subst z
    simp [bar,d,Real.zero_rpow (neg_ne_zero.mpr (zero_lt_one.trans hp).ne')]
  · simp only [d,Pi.single_eq_of_ne hz,add_zero]
    exact Real.rpow_le_rpow_of_nonpos (abs_pos.mpr (by exact_mod_cast hz)) (le_max_right ..) (neg_nonpos.mpr (zero_le_one.trans hp.le))

private theorem finiteAxes {p:ℝ}(hp:1<p)(n:ℕ):Summable (fun z:Fin n→ℤ=>∏i,bar (z i)^(-p)):=by
  induction n with
  | zero=>exact summable_of_hasFiniteSupport (Set.toFinite _)
  | succ n ih=>
    let e:=Fin.consEquiv (fun _:Fin (n+1)=>ℤ)
    refine e.summable_iff.mp (((axis hp).mul_of_nonneg ih (fun i=>Real.rpow_nonneg (unitBar i).le _)
      (fun i=>Finset.prod_nonneg fun _ _=>Real.rpow_nonneg (unitBar _).le _)).congr (fun ⟨a,b⟩=>?_))
    simp [Function.comp,e,Fin.prod_univ_succ,Fin.consEquiv]

private theorem tensor {p:ℝ}(hp:1<p)(J:Type*)[Fintype J]:Summable (fun z:J→ℤ=>∏i,bar (z i)^(-p)):=by
  let e:=Fintype.equivFin J
  let u:(Fin (Fintype.card J)→ℤ)≃(J→ℤ):=Equiv.arrowCongr e.symm (Equiv.refl _)
  refine u.summable_iff.mp ((finiteAxes hp _).congr ?_)
  intro z
  exact (Equiv.prod_comp e (fun i=>bar (z i)^(-p))).symm

def height {J:Type*}[Fintype J](z:J→ℤ):ℝ:=1+∑i, |(z i:ℝ)|

theorem active {J:Type*}[Fintype J](z:J→ℤ):1≤height z:=le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=>abs_nonneg _)

private theorem seen {J:Type*}[Fintype J](z:J→ℤ)(i:J):bar (z i)≤height z:=by
  exact max_le (active z) ((Finset.single_le_sum (f:=fun k=>|(z k:ℝ)|) (fun _ _=>abs_nonneg _) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one))

theorem reserve (J:Type*)[Fintype J]:Summable (fun z:J→ℤ=>(height z ^ (Fintype.card J+1))⁻¹):=by
  by_cases he:Fintype.card J=0
  · letI:IsEmpty J:=Fintype.card_eq_zero_iff.mp he
    exact summable_of_hasFiniteSupport (Set.toFinite _)
  have dim:0<(Fintype.card J:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero he
  let p:ℝ:=(Fintype.card J:ℝ)⁻¹+1
  have inc:1<p:=lt_add_of_pos_left _ (inv_pos.mpr dim)
  have expo:(-p)*(Fintype.card J:ℝ)=-(↑(Fintype.card J+1):ℝ):=by
    dsimp [p]; push_cast; field_simp; ring
  refine Summable.of_nonneg_of_le (fun z=>inv_nonneg.mpr (pow_nonneg (zero_le_one.trans (active z)) _)) (fun z=>?_) (tensor inc J)
  have hz:=zero_le_one.trans (active z)
  calc
    (height z^(Fintype.card J+1))⁻¹ = height z ^ (-p*(Fintype.card J:ℝ)):=by rw [expo,Real.rpow_neg hz,Real.rpow_natCast]
    _ = ∏_:J, height z ^ (-p):=by rw [Real.rpow_mul hz,Real.rpow_natCast]; simp
    _ ≤ ∏i:J,bar (z i)^(-p):=Finset.prod_le_prod (fun _ _=>Real.rpow_nonneg hz _) (fun i _=>Real.rpow_le_rpow_of_nonpos (unitBar _) (seen z i) (neg_nonpos.mpr (zero_le_one.trans inc.le)))

end YM.Integration.WilsonSeparatedOriginalSlabFourierLattice
