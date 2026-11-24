import YM.Integration.WilsonReceivedChronologicalFixedRoseCashPower
import YM.Integration.WilsonOriginalTwoFlatIRSocketRose
import YM.Integration.WilsonOriginalOneArmClearCash

/-! Pay the two ears, the intervening chronological sum, and the captured two-ear switch
on their real dates with one public salary purchased before both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseDatedSalary
open Function Filter Finset Lattice Wilson RG Pert.Asymptotics PhysicalNext.Repeat.Legato
open WilsonReceivedCanonicalVersePortfolio (wallet)
open WilsonReceivedChronologicalLastFlat (wage)
open WilsonReceivedChronologicalFixedRoseCashPower (dated)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple){n:ℕ}

include simple in
theorem original (d power:Fin n→ℕ)(s:(Stock.census (Fin n)).Mode)(A pole P p interior target E:ℕ)
    (B C α η θ:ℝ)(bp:0≤B)
    (edge:target+1+2*pole*n≤P)(switch:target+1+2*pole*n≤p)(middle:target+1+2*pole*n≤ interior):
    ∀ᶠ v:ℕ in atTop,∀{c K N per:ℕ},0<v → v≤c → c≤N → K≤N →
    R.family.S.scale K-R.family.S.scale (v-1)≤(A:ℝ)*(1+Real.log (R.family.path.levels.clock.hatBeta v)) →
    let due:=wallet R d (fun _=>B*(R.family.path.levels.clock.hatBeta K)^pole) s.val
    let g:=regulatorRun R.family N per v
    due*(WilsonOriginalOneArmClearCash.wage s P θ*g^P)≤g^target ∧
    due*(wage s P 1 θ*g^P)≤g^target ∧
    due*((4*((2*A:ℕ):ℝ)/Real.log 3)*wage s P 1 η*g^interior)≤g^target ∧
    due*(WilsonOriginalTwoFlatIRSocketRose.charge R d power P C α E s*(regulatorRun R.family N per c)^p)≤g^target:=by
  filter_upwards [dated R simple d s.val A pole P target edge B (WilsonOriginalOneArmClearCash.wage s P θ) bp,
    dated R simple d s.val A pole P target edge B (wage s P 1 θ) bp,
    dated R simple d s.val A pole interior target middle B ((4*((2*A:ℕ):ℝ)/Real.log 3)*wage s P 1 η) bp,
    dated R simple d s.val A pole p target switch B (WilsonOriginalTwoFlatIRSocketRose.charge R d power P C α E s) bp]
    with v low high mid paid c K N per vp vc cn kn span
  exact ⟨low vp le_rfl (vc.trans cn) kn span,high vp le_rfl (vc.trans cn) kn span,
    mid vp le_rfl (vc.trans cn) kn span,paid vp vc cn kn span⟩

end YM.Integration.WilsonReceivedChronologicalFixedRoseDatedSalary
