import YM.Integration.WilsonCapturedPrimaryGuardedWeakTrial
import YM.Integration.WilsonReceivedQUnitPosterior
import YM.Integration.WilsonPositionProgramBlockedTrialNodes

/-! Normalize a canonical blocked trial with the original end vacua.
The engineering factor is the product of the actual steps in this interval. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWeakTrialEngineering
open Function Finset Filter MeasureTheory Lattice Wilson RG Labels Source Extra.Histories
open RG17 Next.Rank.Spindle Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato WilsonOriginalNullCorridor WilsonOriginalNullPlacedGermMap
open WilsonPositionProgramOriginalBlockedTrial WilsonCapturedPrimaryWeakTileColumn
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (d N per i : ℕ)
local notation "W" n:max => R.family.path.rep N per n

def gain (n : ℕ) : ℂ := ((R.family.S.a i / R.family.S.a (i+n) : ℝ) : ℂ)^d

theorem flow_price (n : ℕ) (f : Config G (R.family.side (i+n) per) → ℂ)
    (hf : Integrable f (prior G _)) :
    flow R.family d N per i n f = gain R d i n • flow R.family 0 N per i n f := by
  induction n with
  | zero => simp [flow,gain,(R.family.S.a_pos i).ne']
  | succ n prev =>
    let L : ℂ := (factor R.family (i+n) : ℂ)^d
    let next := transition (C:=R.family) 0 N per (i+n) f
    have step : transition (C:=R.family) d N per (i+n) f = L • next := by
      simp [next,L,transition,blast,factor]
    have ready : Integrable next (prior G _) := WilsonOriginalNullCorridor.integrable R.family 0 N per hf
    have scales : L * gain R d i n = gain R d i (n+1) := by
      have rates : R.family.S.a i / R.family.S.a (i+(n+1)) = (factor R.family (i+n)) * (R.family.S.a i / R.family.S.a (i+n)) := by
        rw [←Nat.add_assoc, R.family.S.a_step, div_div_eq_mul_div]
        ring
      unfold gain
      rw [rates,Complex.ofReal_mul,mul_pow]
    change flow R.family d N per i n (transition (C:=R.family) d N per (i+n) f) = _ • flow R.family 0 N per i n next
    rw [step,WilsonOriginalNullPlacedFlowPanel.scalar R.family d N per i n L next ready,prev next ready,smul_smul,scales]

theorem normalized {n : ℕ} (live : i+n ≤ N) (o : Site (R.family.side (i+n) per)) (v : R.family.label d)
    (U : Config G (R.family.side i per)) :
    (((W i).eval U : ℝ) : ℂ)⁻¹ * carried R d (p:=per) live o v U =
      gain R d i n * actualTransport R.family (N:=N)
        (fun V => part (R.family.localSection d) o (W (i+n)) V v) (Nat.le_add_right i n) U := by
  let f := numerator R d N per (i+n) o v
  have top : (fun V => (W (i+n)).eval V • part (R.family.localSection d) o (W (i+n)) V v) = f := by
    funext V
    exact (original_field R d N per (i+n) o v V).symm
  have written : (fun V => (((W (i+n)).eval V : ℝ) : ℂ) * part (R.family.localSection d) o (W (i+n)) V v) = f := by
    simpa only [Complex.real_smul,smul_eq_mul] using top
  change _ * flow R.family d N per i n f U = _
  rw [flow_price R d N per i n f (tested R d live o v),WilsonReceivedQUnitPosterior.raw R i n f]
  simp only [actualTransport,Pi.smul_apply,smul_eq_mul,Complex.real_smul,Complex.ofReal_inv,written]
  ring

end YM.Integration.WilsonCapturedPrimaryWeakTrialEngineering
