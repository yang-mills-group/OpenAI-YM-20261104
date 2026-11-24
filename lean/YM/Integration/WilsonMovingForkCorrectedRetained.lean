import YM.Integration.WilsonIndependentMatchedPhysicalPeer

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonMovingForkCorrectedRetained
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped BigOperators Classical
variable {G:Gauge}{h D k u e:ℕ}
local notation "CC" => Credit.leanC

open Finset

def cost (Q:SealR G)(keep:Finset (Alma Q.F))(φ:PowerSeries ℝ→ₗ[ℝ]ℝ)(x:Q.Rider):ℝ:=
  ∑i∈keep,‖φ (x i)‖

def crossing (Q:SealR G){H:Hol G}{v:Rails Q.h k u e}{E W V U:Credit}
    (X:CutsP H Q.ans Q.path v E W V U)(keep:Finset (Alma Q.F))(φ:PowerSeries ℝ→ₗ[ℝ]ℝ)(i:Alma Q.F):ℝ:=
  ∑j∈Finset.univ \ keep,(Wray X.ax X.tx Q.ans Q.path X.N X.m)⁻¹ i j*φ (home Q X j)

/-- A retained numerical charge on the fixed returned pupil. The earlier
coordinate change acts on the entire old row before its error is charged. -/
theorem original (Q:SealR G){H:Hol G}{v:Rails Q.h k u e}{E W V U:Credit}
    (X:CutsP H Q.ans Q.path v E W V U)(keep:Finset (Alma Q.F))(φ:PowerSeries ℝ→ₗ[ℝ]ℝ)(D:ℝ)
    (paid:∀i∈keep,∀j∈keep,‖(Wray X.ax X.tx Q.ans Q.path X.N X.m)⁻¹ i j‖ ≤ D):
    cost Q keep φ (dose X 1) ≤ (keep.card:ℝ)*D*cost Q keep φ (home Q X)+∑i∈keep,‖crossing Q X keep φ i‖:=by
  classical
  let A:=(Wray X.ax X.tx Q.ans Q.path X.N X.m)⁻¹
  have same:PermuteLens X.ax X.tx Q X.N X.m (home Q X)=dose X 1:=by
    simpa only [WilsonPositionProgramTrialHomeDose.scaled,one_smul] using (WilsonPositionProgramTrialHomeDose.original Q X 1).1
  have one i (hi:i∈keep):‖φ (dose X 1 i)‖ ≤ D*cost Q keep φ (home Q X)+‖crossing Q X keep φ i‖:=by
    rw [←same]
    unfold PermuteLens
    simp only [map_sum,map_smul,smul_eq_mul]
    change ‖∑j,A i j*φ (home Q X j)‖ ≤ _
    rw [←sum_sdiff (s₁:=keep) (s₂:=univ) (subset_univ keep),add_comm]
    apply (norm_add_le ..).trans
    apply add_le_add ?_ (le_refl _)
    unfold cost
    rw [mul_sum]
    apply (norm_sum_le ..).trans
    apply sum_le_sum
    intro j hj
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (paid i hi j hj) (norm_nonneg _)
  calc
    _ ≤ ∑i∈keep,(D*cost Q keep φ (home Q X)+‖crossing Q X keep φ i‖):=sum_le_sum one
    _ = _:=by rw [sum_add_distrib];simp [mul_assoc]

theorem descended (Q:SealR G){H:Hol G}{v:Rails Q.h k u e}{E W V U:Credit}
    (X:CutsP H Q.ans Q.path v E W V U)(keep:Finset (Alma Q.F))(φ:PowerSeries ℝ→ₗ[ℝ]ℝ)(D:ℝ)
    (paid:∀i∈keep,∀j∈keep,‖(Wray X.ax X.tx Q.ans Q.path X.N X.m)⁻¹ i j‖ ≤ D)
    (preserves:∀i∈keep,∀j∉keep,(Wray X.ax X.tx Q.ans Q.path X.N X.m)⁻¹ i j=0):
    cost Q keep φ (dose X 1) ≤ (keep.card:ℝ)*D*cost Q keep φ (home Q X):=by
  classical
  have clear (i) (hi:i∈keep):crossing Q X keep φ i=0:=sum_eq_zero fun j hj=>by
    rw [preserves i hi j (mem_sdiff.mp hj).2,zero_mul]
  simpa only [sum_congr rfl (fun i hi=>congrArg norm (clear i hi)),norm_zero,sum_const_zero,add_zero]
    using original Q X keep φ D paid
end YM.Integration.WilsonMovingForkCorrectedRetained
end
