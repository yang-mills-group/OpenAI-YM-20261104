import YM.Integration.WilsonPosteriorProjectionRootedCharge
import YM.Integration.WilsonPosteriorProjectionCommonGrade
import YM.Integration.WilsonPosteriorProjectionCommonRooted

/-! One original scene grade for all ranks of the independently normalized
fresh Wilson bank. The only numerical input is the presold original spatial
menu of the finite census, already available on the common trajectory. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionCommonCensus

open Filter Finset Lattice Wilson RG Source Labels Next.Foundations
open PhysicalNext.Repeat.Legato MSbar MSbar.Heath MSbar.Mosaic
open FVA1Physical.Round2.Curvature FVA1Physical.Marked FVA1Physical.Wilson
open WilsonPosteriorProjectionPinned WilsonPosteriorProjectionCommonGrade
open WilsonPosteriorProjectionCommonWords WilsonPosteriorProjectionCommonRooted
open RGComparison.Core16.Spool
open scoped Classical BigOperators Topology
variable {G : Gauge} {I : Type} [Fintype I] {d : ℕ}

def degreePrice (P q : ℕ) := chartInversePower (q+1)+(P+1)
def audit (p K : ℕ) :=
  if K=0 then fieldAuditOrder p 0 else common (p+(p+8)) (degreePrice (p+(p+8))) K

theorem each (a : I → CoverLabel G d) (R : Run G) (u : G.ColorIndex) (hG : G.Simple)
    (V : Voice G) (cle : Clear G V) (inputs : PinnedReadings (freshLamps a) R u)
    (rows : PinnedEmissions (freshLamps a) R u) (cash : Late R (rootedFieldMenu a))
    (p K q s L radius : ℕ) (hq : 0<q) (qK : q≤K) (hs : 6 ≤ s) {D η : ℝ} (hD : 0≤D) (hη : 0<η) :
    AtGrade a R u p q s L radius D η (audit p K) := by
  let P := p+(p+8)
  have K0 : K ≠ 0 := (hq.trans_le qK).ne'
  obtain ⟨adequate,same⟩ := pays P (degreePrice P) K q hq qK
  have real := word (freshLamps a) hG R u inputs rows P q s L hs D 1 hD zero_lt_one
    (stencil (degreePrice P) K q) adequate
  have words : AtOrder (freshLamps a) R u P q L D 1 (audit p K) := by
    rw [audit,if_neg K0,same]; exact real
  have hp : P≤audit p K := by rw [audit,if_neg K0]; unfold common; dsimp only [P]; omega
  obtain ⟨m,hm⟩ := margin_eventually (derivative_clock p 0 0 le_rfl hη).1
  exact atGrade a R u hG V cle rows p q s L radius (audit p K) hp hq hs hD hη words
    (margin_pos m) hm (WilsonPosteriorProjectionRootedSchedule.charge a R cash q (s+s) radius m)

end YM.Integration.WilsonPosteriorProjectionCommonCensus
end

