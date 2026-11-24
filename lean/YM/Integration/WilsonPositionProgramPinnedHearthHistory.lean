import YM.Integration.WilsonMarkedIndependentNormalizedElection
import YM.WilsonCoeffUV.Product.Report.Center

/-! Carry one capture pin through every finer date of the inherited finite
and cover programs, moving the entire occupied source with its old deposits. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionProgramPinnedHearthHistory
open Filter Function Finset Lattice Wilson RG Exterior Precision Tree Planned.PrimaryIntegral295
open WilsonCoeffUV WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Soil
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open scoped Classical BigOperators
variable {G:Gauge}
def count (S:Schedule)(b i:ℕ):ℕ:=∏ j ∈ Ico b i,(S.block j).val
def pin (S:Schedule)(b i:ℕ)(v:Cover):Cover := count S b i • v

theorem moves (S:Schedule){b i:ℕ}(old:b ≤ i)(v:Cover):
    pin S b (i+1) v=(S.block i).val • pin S b i v := by
  unfold pin count
  rw [prod_Ico_succ_top old,Nat.mul_comm, mul_smul]

variable {V:Type} [NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
variable (L:Levels G) {O:ChartRatio G} (simple:G.Simple) (law:LocalRatio O)
    {k N:ℕ}(U:Era G V)(ready:Auth k U){b c:ℕ}

include simple law ready in
theorem at_date (v:Cover)(cap:c ≤ N){i:ℕ}(before:i ≤ c)(after:b ≤ i):
    cruises L O N k c i (shifted U (pin L.S b c v)) =
      shifted (cruises L O N k c i U) (pin L.S b i v) := by
  induction before using Nat.decreasingInduction with
  | self=>rw [cruises_top,cruises_top]
  | of_succ i younger ih=>
    rw [cruises_sub _ _ _ _ _ younger,cruises_sub _ _ _ _ U younger,ih (by omega),moves L.S after]
    exact outing L (younger.trans_le cap) simple law (cruising L simple law younger cap ready) _

include simple law ready in
theorem capture (v:Cover)(cap:c ≤ N)(order:b ≤ c):
    cruises L O N k c b (shifted U (pin L.S b c v)) =
      shifted (cruises L O N k c b U) v := by
  rw [at_date L simple law U ready v cap order le_rfl]
  simp [pin,count]

end YM.Integration.WilsonPositionProgramPinnedHearthHistory
end
