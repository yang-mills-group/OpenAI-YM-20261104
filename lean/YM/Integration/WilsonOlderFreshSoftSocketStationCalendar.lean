import YM.Integration.WilsonOlderFreshSoftSocketStationDate

/-! One cofinal intermediate stop for all future plants, positions and original regulators. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshSoftSocketStationCalendar
open Filter Function RG Wilson Real Pert.Asymptotics PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "a_" => R.family.S.a
local notation "σ" => R.family.S.scale
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "g" => regulatorRun R.family

def Offered (width:ℕ)(loss:ℝ)(c w:ℕ):Prop:=
  ∀K N per,c≤K→K≤N→a_ c/a_ K≤(H c)^width→
    let logg:=log (g N per K)⁻¹
    a_ c/a_ w≤exp (-loss*logg) ∧ loss*logg≤σ c-σ w ∧
      σ c-σ w≤8*((2*⌈loss⌉₊:ℕ)+1:ℝ)*logg

def date (width:ℕ)(loss:ℝ)(c:ℕ):ℕ:=
  Nat.findGreatest (Offered R width loss c) c

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(width:ℕ)(loss:ℝ)(positive:0≤loss):
    Tendsto (date R width loss) atTop atTop ∧
    ∀ᶠ c:ℕ in atTop,date R width loss c≤c ∧ Offered R width loss c (date R width loss c):=by
  constructor
  · apply tendsto_atTop.2
    intro gate
    filter_upwards [WilsonOlderFreshSoftSocketStationDate.original R simple slow gate width loss positive] with c quote
    obtain ⟨w,late,below,filed⟩:=quote
    exact late.trans (Nat.le_findGreatest (P:=Offered R width loss c) below filed)
  · filter_upwards [WilsonOlderFreshSoftSocketStationDate.original R simple slow 0 width loss positive] with c quote
    obtain ⟨w,_,below,filed⟩:=quote
    exact ⟨Nat.findGreatest_le _,Nat.findGreatest_spec (P:=Offered R width loss c) below filed⟩

theorem settled (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(width:ℕ)(loss:ℝ)(positive:0≤loss):
    ∀ᶠ c:ℕ in atTop,∀v K N per,v≤date R width loss c→c≤K→K≤N→a_ v/a_ K≤(H v)^width→
      let w:=date R width loss c
      let logg:=log (g N per K)⁻¹
      w≤c ∧ a_ c/a_ w≤exp (-loss*logg) ∧ loss*logg≤σ c-σ w ∧
        σ c-σ w≤8*((2*⌈loss⌉₊:ℕ)+1:ℝ)*logg:=by
  filter_upwards [(original R simple slow width loss positive).2] with c h v K N per vw ck live room
  exact ⟨h.1,h.2 K N per ck live (WilsonOlderFreshSoftSocketStationDate.width R simple (vw.trans h.1) room)⟩

end YM.Integration.WilsonOlderFreshSoftSocketStationCalendar
end
