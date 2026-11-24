import YM.Integration.WilsonVacuumPreResetJointPublished
import YM.Integration.WilsonVacuumPreResetJointFace

/-! The three genuine reference rows and the elementary Wilson face in the
unmasked pre-reset action. The quadratic equality compares the complete
double sum of ordered physical paths on its original torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetJointBanks
open WilsonCoeffUV
open Filter Function Finset Lattice Wilson RG Laurent Exterior Precision Stationary
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonLimitConstruction OriginalMarkedRunAction
open private pairIndices from YM.Integration.WilsonPhysicalHistoryRetainedSpringGram
open scoped Topology BigOperators Classical
variable {G : Gauge} {f : Side} {K : PathData G} {B : Clip} {σ C Λ : ℝ}

def kinetic (K : PathData G) : PrismA G := ⟨0,0,le_rfl,tides K⟩
abbrev cubic (K : PathData G) : PrismA G := WilsonCubicPrintedTensor.source K.cubic
def quartic (K : PathData G) : PrismA G := ⟨2,2,le_rfl,K.quartic⟩

theorem commission (paid : K.Bounds B σ C Λ) :
    Commission (kinetic K).cells σ (gramCost G C) (kinetic K).grade ∧
    Commission (cubic K).cells σ C (cubic K).grade ∧
    Commission (quartic K).cells σ C (quartic K).grade := by
  exact ⟨⟨tones K,tides_pay paid,fun h => False.elim (Nat.not_lt_zero _ h)⟩,
    ⟨fun i => (paid.invariant i).2.1,paid.three,fun _ => trivial⟩,
    ⟨fun i => (paid.invariant i).2.2,paid.four,fun _ => trivial⟩⟩

theorem filed (K : PathData G) :
    kinetic K ∈ pool K ∧ cubic K ∈ pool K ∧ quartic K ∈ pool K := by
  simp [pool, kinetic, cubic, quartic, WilsonCubicPrintedTensor.source]

theorem rawKinetic (paid : K.Bounds B σ C Λ) (U : Config G f) :
    secondTerm B K U = B.direct * (∑ x : Site f, facePriceAt x U) +
      FundedPeriodAction.action f (kinetic K) U := by
  have same (x : Site f) : sitePacket (gramEntries K) x U = sitePacket (tides K) x U := by
    unfold sitePacket
    congr 1
    funext s
    calc
      _ = ∑' t : PairsIndex, (gramPath K t).unmasked (pull s 0 U) x :=
        pairIndices.tsum_eq _
      _ = _ := ((towers G K).tsum_eq (fun t => (gramPath K t).unmasked (pull s 0 U) x)).symm
  rw [(bare_sites B K U).1, Finset.mul_sum]
  change (∑ x : Site f, secondAt B K x U) = _ + Patch.average (fun s : Signed => uncut (tides K) (pull s 0 U))
  rw [packet_sites, ← Finset.sum_add_distrib]
  exact sum_congr rfl fun x _ => (gram_at K paid x U).trans (by rw [same])

theorem rawInteraction (B : Clip) (U : Config G f) :
    interaction K U = FundedPeriodAction.action f (cubic K) U + FundedPeriodAction.action f (quartic K) U := by
  change interaction K U = Patch.average (fun s : Signed => uncut K.cubic (pull s 0 U)) +
    Patch.average (fun s : Signed => uncut K.quartic (pull s 0 U))
  rw [packet_sites, packet_sites, ← Finset.sum_add_distrib]
  exact (bare_sites B K U).2.1

end YM.Integration.WilsonVacuumPreResetJointBanks
