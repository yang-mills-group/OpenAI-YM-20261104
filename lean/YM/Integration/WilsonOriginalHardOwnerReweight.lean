import YM.QuadraticLocal.Travel
import YM.RemainderComparison.Lyric.Finale

/-! Reserve support decay for a distinguished occupied owner when pricing its
actual first successor. The inserted leaves, their gas predicates, and their
original root inventory do not depend on the numerical weights. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalHardOwnerReweight
open Function Filter Finset Lattice Wilson RG Ac Marker Push Push.AbsoluteSums Pressure
open Push.SectorMeasure ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Lotus Merge
open RemainderComparison RemainderComparison.Lyric
open scoped Topology BigOperators Classical
variable {ι E : Type} [Fintype ι] [Fintype E] {G : Gauge} {c f : Side}
    {S : StepData c f} {R : Rep G f} {M : ι → Lotus.Leaf R} {o : E → Site f} {A : ι → Finset E}
    {a b θ : ℝ} {N d : ℕ}

def raise (use : ι → Prop) (θ : ℝ) (d : ℕ) (i : ι) : ℝ :=
  if use i then Real.exp (θ*d) else 1

omit [Fintype ι] in
theorem scale (h : Scale o A M (fun _ => 1) N a b S) (θ0 : 0≤θ)
    (use : ι → Prop) (wide : ∀ i,use i → d≤coverNumber R.p.B (M i).crest) :
    Scale o A M (raise use θ d) N (a-θ) b S := by
  have positive i : 0 < raise use θ d i := by unfold raise; split <;> positivity
  refine ⟨fun i=>(positive i).le,?_,?_,h.tolerance,h.sizes⟩
  · intro i hit
    apply h.pin i
    simpa only [Palette.wages,one_mul] using (pos_of_mul_pos_right hit (positive i).le)
  · intro x
    refine Extra.Multi.Budget.mono (h.crown x) ?_ ?_ le_rfl
    · intro i
      split
      · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (positive i).le (M i).profit)
      · exact le_rfl
    · intro i
      split_ifs
      · let q : ℝ := coverNumber R.p.B (M i).crest
        change Real.exp ((a-θ)*q)*(raise use θ d i*(M i).weight) ≤ Real.exp (a*q)*(1*(M i).weight)
        rw [one_mul,←mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (M i).profit
        by_cases selected : use i
        · rw [raise,if_pos selected,←Real.exp_add]
          apply Real.exp_le_exp.mpr
          have paid := mul_le_mul_of_nonneg_left (show (d:ℝ)≤q from by dsimp only [q]; exact_mod_cast wide i selected) θ0
          linarith
        · rw [raise,if_neg selected,mul_one]
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_right (sub_le_self _ θ0) (Nat.cast_nonneg _)
      · exact le_rfl

/-- The native coarsening inequality still holds after reserving an eighth
of the authentic incoming support exponent. -/
theorem funded {P : Teller G} (Q : Target G P) {L : Side} (foam : Daisy.foam Q L)
    (large : 4 ≤ Q.relative) (budget : 4*Q.ε ≤ a) : radiusCost Q L (a-a/8) := by
  let k := 10*Footprint.preCost (Q.halo+5)/(L.val:ℝ)
  have nonneg : 0≤k := by dsimp [k,Footprint.preCost]; positivity
  have fee : Q.relative*k ≤ Q.ε := foam
  have spare : 4*k ≤ Q.ε := (mul_le_mul_of_nonneg_right large nonneg).trans fee
  change (Q.relative+1)*k+2*Q.ε ≤ a-a/8
  nlinarith only [fee,spare,budget,nonneg]

end YM.Integration.WilsonOriginalHardOwnerReweight
end
