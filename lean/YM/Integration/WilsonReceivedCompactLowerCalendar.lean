import YM.Integration.WilsonReceivedCompactRadiusCalendar

/-! At geometric capture the same real course can also file the immediately earlier Wilson return. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedCompactLowerCalendar
open Filter XSpace PhysicalNext.Repeat.Legato
open scoped Topology

theorem original {G:Gauge} (R:Run G) (simple:G.Simple) (test:Test 3) {A:ℕ→Prop} (bought:∀ᶠ m:ℕ in atTop,A m) :
    ∃t:ℝ,0<t ∧ ∀r:ℝ,0<r → r ≤ t →
    let b:=WilsonCloseCaptureDate.level R.family.S r
    ∃m:ℕ,m+1=b ∧ WilsonReceivedCompactQRadiused.floor R simple test ≤ b ∧ |r| ≤ R.family.S.a b ∧ A m := by
  obtain ⟨m₀,live⟩:=eventually_atTop.mp bought
  obtain ⟨t,positive,paid⟩:=WilsonReceivedCompactRadiusCalendar.original R simple test (eventually_ge_atTop (m₀+1))
  refine ⟨t,positive,?_⟩
  intro r rp small
  obtain ⟨funded,space,headroom⟩:=paid r rp small
  let b:=WilsonCloseCaptureDate.level R.family.S r
  have enough:m₀+1 ≤ b:=headroom
  exact ⟨b-1,by omega,funded,space,live _ (by omega)⟩

end YM.Integration.WilsonReceivedCompactLowerCalendar
