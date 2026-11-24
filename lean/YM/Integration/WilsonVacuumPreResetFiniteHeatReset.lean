import YM.Integration.WilsonVacuumPreResetFiniteHeatSlope
import YM.Integration.WilsonFiniteCommonKineticReset
import YM.Integration.RootedVacuumWinding

/-! The common kinetic reset of the measured finite material and the
periodic image of the independent pre-reset shelf. The signed incoming
error and the original fresh vacuum winding bill enter separately. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatReset
open Bloch Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding PowerSeries
open scoped Classical BigOperators
variable {G:Gauge}{m N:ℕ}

theorem entry {α:Type}[Fintype α][DecidableEq α]{n:Side}{r:ℕ}{s:ℝ}(hs:0 ≤ s)
    (P:Ten ℝ (Co n α) (r+1))(y):
    |P y| ≤ RootedVacuumWinding.held 0 (y 0) s P:=by
  let t:=Real.exp (s*soar (tor n) y)
  have one:1 ≤ t:=Real.one_le_exp (mul_nonneg hs (Nat.cast_nonneg _))
  calc
    _ ≤ t*|P y|:=le_mul_of_one_le_left (abs_nonneg _) one
    _ ≤ _:=by
      unfold RootedVacuumWinding.held
      have h:=Finset.single_le_sum (s:=univ)
        (f:=fun (z : Fin (r+1) → (Site n × α)) =>if z 0=y 0 then Real.exp (s*soar (tor n) z)*‖P z‖ else 0)
        (fun z _=>by split <;> positivity) (mem_univ y)
      simpa [Real.norm_eq_abs,t] using h

/-- Reversion of a finite whole row commutes with the genuine period fold
at positive angular rank. The cover inputs have their native summability. -/
theorem original (L:Levels G)(O:ChartRatio G)(live:m<N)(n:Side)(i r:ℕ){s A B:ℝ}
    (positive:0<s)(shelf:∀a ≤ i,∃v,Amber terrain s v (freshet L O N m a (r+1)))
    (upper:∀a ≤ i,∀x,|unripe L O N m (story L O N (m+1)).1 n a (r+1) x-coil0 L O m N n a (r+1) x| ≤ A)
    (fresh:∀a ≤ i,∀x,|RootedVacuumWinding.ground L O N m n a r x| ≤ B)(x):
    |(story L O N m).1 n i (r+1) x-emera (actionW L O N m) n i (r+1) x| ≤
      rimJ (ratioHigh L O N m) i (r+1)*(A+B):=by
  classical
  let b:=ratioHigh L O N m
  let c(a:ℕ):ℝ:=coeff (i-a) (b^a*(b⁻¹)^(r+1))
  let F(a:ℕ):=freshet L O N m a (r+1)
  let Z(a:ℕ):=unripe L O N m (story L O N (m+1)).1 n a (r+1)
  have covered:emera (actionW L O N m) n i (r+1)=∑a∈range (i+1),c a • lagoon (F a) n:=by
    change lagoon (actionW L O N m i (r+1)) n=_
    rw [conduct L O live]
    change lagoon (∑a∈range (i+1),c a • F a) n = _
    rw [lagoon_join _ (fun a ha=>?_ ) positive]
    · simp only [lagoon_scalar]
    · obtain ⟨v,p⟩:=shelf a (Nat.lt_succ_iff.mp (mem_range.mp ha))
      exact ⟨_,p.smul (c a)⟩
  have finite:(story L O N m).1 n i (r+1)=∑a∈range (i+1),c a • Z a:=by
    rw [story_stride L O live]
    rfl
  have priced(a:ℕ)(v:a ≤ i):|Z a x-lagoon (F a) n x| ≤ A+B:=by
    have h:=fresh a v x
    change |lagoon (F a) n x-coil0 L O m N n a (r+1) x| ≤ B at h
    rw [abs_sub_comm] at h
    exact (abs_sub_le ..).trans (add_le_add (upper a v x) h)
  rw [finite,covered]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,←Finset.sum_sub_distrib,←mul_sub]
  change |∑a∈range (i+1),c a*(Z a x-lagoon (F a) n x)| ≤ (∑a∈range (i+1),‖c a‖)*(A+B)
  rw [Finset.sum_mul]
  apply (abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum
  intro a ha
  rw [abs_mul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (priced a (Nat.lt_succ_iff.mp (mem_range.mp ha))) (abs_nonneg _)

end YM.Integration.WilsonVacuumPreResetFiniteHeatReset
end
