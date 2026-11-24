import YM.Integration.WilsonReceivedCompactQRadiused
import YM.Integration.WilsonCloseCaptureDate

/-! A programmed close sale can use the actual geometric date of each sufficiently small real radius. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedCompactRadiusCalendar
open Filter XSpace PhysicalNext.Repeat.Legato
open scoped Topology

theorem original {G:Gauge} (R:Run G) (simple:G.Simple) (test:Test 3) {A:ℕ→Prop} (bought:∀ᶠ m:ℕ in atTop,A m) :
    ∃t:ℝ,0<t ∧ ∀r:ℝ,0<r → r ≤ t →
    let m:=WilsonCloseCaptureDate.level R.family.S r
    WilsonReceivedCompactQRadiused.floor R simple test ≤ m ∧ |r| ≤ R.family.S.a m ∧ A m := by
  obtain ⟨m₀,live⟩:=eventually_atTop.mp bought
  let n:=max m₀ (WilsonReceivedCompactQRadiused.floor R simple test)
  refine ⟨R.family.S.a n,R.family.S.a_pos n,?_⟩
  intro r rp small
  let m:=WilsonCloseCaptureDate.level R.family.S r
  have bracket:=WilsonCloseCaptureDate.bracket R.family.S rp
    (small.trans (R.family.S.strictAnti.antitone (Nat.zero_le n)))
  have nm:n ≤ m:=by
    by_contra! early
    have spent:=R.family.S.strictAnti.antitone (Nat.succ_le_of_lt early)
    exact (not_lt_of_ge spent) (bracket.1.trans_le small)
  exact ⟨(le_max_right ..).trans nm,(abs_of_pos rp).le.trans bracket.2,live m ((le_max_left ..).trans nm)⟩

end YM.Integration.WilsonReceivedCompactRadiusCalendar
