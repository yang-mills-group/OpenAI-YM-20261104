import YM.Integration.WilsonReceivedChronologicalFixedRoseEnrolledCash
import YM.Integration.WilsonOriginalTwoFlatIRCapturedCross
import YM.Integration.WilsonMovingForkCofinalStops
import YM.Integration.WilsonOriginalCensusPublicationClock
import YM.Integration.WilsonOriginalTwoFlatIRRows

/-! The two appointments on one arbitrary finite enrolled faculty, with one Laurent
power for each genuine numerical source and the original two-stop thermal income. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterTariff
open Function Filter Finset Lattice Wilson RG Pert.Asymptotics
open PhysicalNext PhysicalNext.Repeat Legato
open WilsonPositionProgramReporterBand (Band)
open WilsonIndependentCapturedPages (Stop)
open WilsonOriginalTwoFlatIRCapturedCross (Quote)
open WilsonOriginalCensusPublicationClock (Load Open)
open WilsonReceivedChronologicalFixedRoseEnrolledCash (roof)
open scoped Classical BigOperators Topology

variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "C" => R.family
local notation "g" N:max per:max i:max => regulatorRun R.family N per i
local notation "H" i:max => R.family.path.levels.clock.hatBeta i

theorem original {n k q order shelf p:ℕ}(grades:Fin n → ℕ)(pieces stages:ℕ)
    (load:Load k q order shelf p grades pieces stages)(B:ℝ)(paid:1≤B)(caps:Fin n → ℝ)(A:ℕ)
    (slow:WilsonWindowReportingPace.Slow R.kit)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)(D:XSpace.Run){stage u depth:ℕ}
    (band:Band R D stage)(v:Stop R D band u depth)(deep:0<depth)(ref:R.family.ref 0≤u)(target:ℕ):
    1≤roof B caps ∧ ∀ᶠ t:ℕ in atTop,let c:=band.reporter+t;let b:=v.date t
      ∃uv:u≤b,∃vc:b<c,Open R simple grades pieces stages load c ∧
      2≤H c ∧ (eventually_atTop.mp (WilsonOriginalTwoFlatIRRows.nextClock R simple)).choose≤c ∧
      ∀{K N per:ℕ},c<K → K≤N → R.family.S.a b/R.family.S.a K≤(H b)^A →
        let rate:=(Real.sqrt (R.family.path.β N per b))^(1:ℝ)*B^n
        Quote R N per u b c target depth (uv.trans vc.le) vc.le ∧
        0≤rate ∧ 0<g N per b ∧ g N per b≤1 ∧ g N per K≤1 ∧
        rate≤roof B caps*(3*(g N per c)⁻¹)^1 ∧ (∀i,caps i≤roof B caps*(3*(g N per c)⁻¹)^1) ∧
        rate≤roof B caps*(3*(g N per b)⁻¹)^1 ∧ ∀i,caps i≤roof B caps*(3*(g N per b)⁻¹)^1 :=by
  obtain ⟨cp,fees⟩:=WilsonReceivedChronologicalFixedRoseEnrolledCash.original R simple B paid caps A
  refine ⟨cp,?_⟩
  have ct:Tendsto (fun t:ℕ=>band.reporter+t) atTop atTop:=
    tendsto_atTop_mono (fun t=>Nat.le_add_left t band.reporter) tendsto_id
  filter_upwards [v.heard,ct.eventually (WilsonOriginalOpticalCouplingBand.cold R simple 2),
    ct.eventually (WilsonOriginalCensusPublicationClock.original R simple grades pieces stages load),
    ct.eventually ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop 2),
    ct.eventually_ge_atTop (eventually_atTop.mp (WilsonOriginalTwoFlatIRRows.nextClock R simple)).choose,
    (WilsonMovingForkCofinalStops.original R v).eventually fees,
    WilsonOriginalTwoFlatIRCapturedCross.original R simple slow.2 ready D band v ref target] with
    t hearing thermal opening tall clocked wallet quote
  let c:=band.reporter+t
  have pos:0<g c 0 c:=ActualRunKernelPackets.regulator_pos R c 0 c le_rfl
  have cheap:(2:ℝ)≤(g c 0 c)⁻¹:=thermal c 0 le_rfl
  have cold:g c 0 c<1:=by
    rw [le_inv_comm₀ (by norm_num) pos] at cheap
    linarith
  have small: v.date t<c:=by
    apply lt_of_le_of_ne (v.upper t)
    intro same
    have bound:=(hearing.2 c 0 le_rfl).2.2.1
    change R.family.S.a c/R.family.S.a (v.date t)≤((g c 0 c)^depth)^2 at bound
    rw [same,div_self (R.family.S.a_pos c).ne'] at bound
    exact not_lt_of_ge bound (pow_lt_one₀ (pow_nonneg pos.le _) (pow_lt_one₀ pos.le cold deep.ne') (by decide))
  refine ⟨hearing.1,small,opening,tall,clocked,?_⟩
  intro K N per after live mesh
  exact ⟨quote N per (after.trans_le live) (hearing.1.trans small.le),wallet small.le after.le live mesh⟩

end YM.Integration.WilsonReceivedChronologicalRosterTariff
end
