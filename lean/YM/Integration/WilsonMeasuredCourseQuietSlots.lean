import YM.QuadraticLocal.Advent
import YM.RG01.Slack
import YM.Integration.QLocalQuietDifferenceInvoice

/-! The forced inventory on the measured perturbative course has the same
literal supports and required flags as the original Wilson vacuum. Individual
quiet kernel differences are flat in the original rooted norm at every date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredCourseQuietSlots
open Function Filter Lattice Wilson RG RG.Shoot Marker Overlay Extra.Histories
open PhysicalNext Repeat Legato Graces Roost
open Pressure Testing Input Precision Org Supply Push SectorMeasure PriceCompiler
open ConnectedActivityE6 Progress.DirectedRecipe
open AllOrder AllOrder.Transit WheelP AllOrder.Floe
open QuadraticLocal.Advent
open scoped Topology Classical
variable {G:Gauge} (R:Run G)

theorem selected {i m N per k:ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (Ψ:∀ j,RG.Rep G (R.family.side j per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (started : m ≤ i) (live : i ≤ N) :
    let P := R.family.path.rep N per i
    let κ := R.family.path.levels.clock.forcedAllowance i
    P.p=(Ψ i).p ∧ P.activities.forced=(Ψ i).activities.forced ∧
      QLocalQuietDifferenceInvoice.Receipt P (Ψ i) (κ+κ) := by
  intro P κ
  let π₀ := ((R.T.sticks N per).prices i (Nat.zero_le _) live).1
  let π₁ := (later R π Γ Ψ course started live).truep
  have common : P.p=(Ψ i).p := π₀.point.trans π₁.point.symm
  have original : HasSlots (R.alloy.B.a.budget i) P.activities := by
    have funded := π₀.loads
    rw [R.kit.machine.ready] at funded
    exact (PeriodFuture.pockets funded).2.2.2.2
  have other := spare R π Γ Ψ course started live
  have sq : P.activities.forced=(Ψ i).activities.forced := by
    rw [π₁.point] at other
    exact original.forced.trans other.forced.symm
  exact ⟨common,sq,QLocalQuietDifferenceInvoice.paid P (Ψ i) common sq π₀.valid.labels.boundK π₁.valid.labels.boundK⟩

theorem original (simple:G.Simple) (q:ℕ) : ∀ᶠ i:ℕ in atTop, ∀ {m N per k:ℕ}
    (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀ j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → m ≤ i → i ≤ N →
    let P:=R.family.path.rep N per i
    P.activities.forced=(Ψ i).activities.forced ∧
      QLocalQuietDifferenceInvoice.Receipt P (Ψ i) (2*((R.family.path.levels.clock.hatBeta i)^q)⁻¹) := by
  let A := R.family.path.levels
  filter_upwards [(RG01.Physical.shrink simple A q).eventually_le_const zero_lt_one] with i paid m N per k π Γ Ψ course started live
  obtain ⟨_,slots,b⟩ := selected R π Γ Ψ course started live
  have positive : 0<(A.clock.hatBeta i)^q := pow_pos (zero_lt_one.trans (A.fits.delayed i)) q
  have cost : A.clock.forcedAllowance i ≤ ((A.clock.hatBeta i)^q)⁻¹ := by
    have bound : A.clock.forcedAllowance i * (A.clock.hatBeta i)^q ≤ 1 := by simpa only [mul_comm] using paid
    exact ((le_div_iff₀ positive).2 bound).trans_eq (one_div _)
  exact ⟨slots,QLocalQuietDifferenceInvoice.Receipt.mono _ _ b (by change A.clock.forcedAllowance i+A.clock.forcedAllowance i ≤ 2*((A.clock.hatBeta i)^q)⁻¹; linarith)⟩

end YM.Integration.WilsonMeasuredCourseQuietSlots
end
