import YM.Integration.WilsonIndependentCollarAppointmentCharge
import YM.Integration.WilsonIndependentCollarActualSeatWidth
import YM.Integration.WilsonOriginalCensusPathGaussian

/-! Issue the authentic physical path-census Paid predicate on the same
optical Realm, at the actual teacher and without changing the stored input. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarCensusAppointment
open Function Finset Filter Lattice Wilson RG Precision PhysicalNext.Repeat.Legato Exterior Work.F08 MeasureTheory
open RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Next.Scheduling Extra.Iteration Song ThroughLaunch Roof Push.PriceCompiler
open Further.StrongStartup SectorNext WilsonStartup Progress.DirectedRecipe Next.Foundations
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Iron
open QuadraticLocal QuadraticLocal.Mentor WilsonCoeffUV WilsonOriginalCollarTeacher
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express
open WilsonIndependentCollarPrintIncome WilsonIndependentCollarRootedWidth
open FundedMarkedPathSelection WilsonOlderFreshConnectedRobe
open scoped Classical BigOperators Topology
variable {G:Gauge} {n e:ℕ}

theorem original (R:Run G)(simple:G.Simple)(D k:Fin n→ℕ)(V:Realm G (e+1) Credit.leanC)
    (clock:V.y=zz R.family.path.levels)(school:Cloze D k V Credit.leanC){δ:ℝ}(power:0<δ):
    ∀ᶠm:ℕ in atTop,∀(hm:V.anchor ≤ m)(w:Widths G)(request:Request G)(ψ:ℕ→ℕ)(K x:ℕ),
      1≤K → n≤K →
      let U:=V.mint m hm
      let D₀:=WilsonOlderFreshGraphSchool.roots (menu request) simple R.metals.p R.metals.K
      U.gear.s=2*U.σ → U.σ≤1 → (∀J:Finset (Fin n),
        let out:=issue w (e+1) (mass k J) U.gear
        out.fee≤V.y m ∧ out.strip⁻¹≤V.y m ∧ teacherWidth request R.metals.p.kernel x≤out.strip) →
        WilsonOlderFreshConnectedAppointment.Paid R V hm D k δ (Poetry.Agenda.seed D₀ ψ K x):=by
  have rate:∀z:Finset (Fin n) × Fin n,∀ᶠm:ℕ in atTop,
        (WilsonIndependentCollarAppointmentCharge.coin (G:=G) D k e z.1 z.2).buy (zz R.family.path.levels m) ≤
        R.family.path.levels.clock.hatBeta m^δ:=fun z=>WilsonOlderFreshConnectedCurrency.tariff R simple _ power
  filter_upwards [eventually_all.mpr rate] with m bills
  intro hm w request ψ K x working seats U D₀ twice cap policy N S J c A X sub front pos live
  let out:=issue w (e+1) (mass k J) U.gear
  obtain ⟨fee,strip,tag⟩:=policy J
  have relative:out.strip≤U.σ:=by
    apply out.narrow.trans
    apply (min_le_right ..).trans
    apply (min_le_left ..).trans
    rw [twice];linarith [U.width]
  have wide:32*Poetry.Agenda.seed D₀ ψ K x≤WilsonIndependentCollarRootedWidth.rooted J.card out.strip:=
    WilsonIndependentCollarActualSeatWidth.original request R simple ψ K x J.card working
      (Finset.card_le_univ J |>.trans (by simpa using seats)) out.strip tag
  have coach:=WilsonIndependentCollarConnectedFilm.original V hm X w c front sub pos live school twice cap
  refine ⟨coach.1,?_⟩
  intro o j hj r
  have amount:=WilsonIndependentCollarAppointmentCharge.original (D:=D) (k:=k) V hm J c front w A pos cap
    (((inv_le_inv₀ U.width out.openStrip).2 relative).trans strip) fee
  have billed:(WilsonIndependentCollarAppointmentCharge.coin (G:=G) D k e J c).buy (V.y m) ≤
      R.family.path.levels.clock.hatBeta m^δ:=by rw [clock];exact bills (J,c)
  apply WilsonOlderFreshConnectedCurrency.posted V hm X (WilsonOlderFreshConnectedEarning.payroll V hm X (coach.2 o j hj r) wide)
  exact amount.trans (mul_le_mul_of_nonneg_right billed (pow_nonneg pos _))

end YM.Integration.WilsonIndependentCollarCensusAppointment
end
