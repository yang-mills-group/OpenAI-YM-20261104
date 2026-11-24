import YM.Integration.WilsonMatrixTicketLanesReportedAdmission
import YM.RGComparison.Core16.Astage.Layouts

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedCrew
open Function Filter Set Metric Real OPE Labels RG12 RG17 Extraction Spec Wilson Table
open RGComparison.Core16.Astage SharpGram.Lenses PhysicalNext.Repeat.Legato
open Pier.Lair OPE.Orbits Climb Ward PhysMS Trace.Pilot SharpGram
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : RG17.Layout F)
local notation "β" => R.family.path.levels.clock.hatBeta

theorem temperature {ι : Type} {l : Filter ι} (simple : G.Simple) {m : ι → ℕ} (hm : Tendsto m l atTop) :
    RateIs l (ruler R.family m) (fun i => β (m i)) 0 := by
  have raw : RateIs atTop R.family.S.scale β 0 :=
    ⟨Eventually.of_forall (fun i => zero_lt_one.trans (R.family.path.levels.fits.delayed i)),
      (MergeProof.Ribbons.hut R.family simple).pitch⟩
  exact raw.comp hm

theorem radius {ι : Type} {l : Filter ι} (simple : G.Simple) {m : ι → ℕ} (hm : Tendsto m l atTop)
    (r : ι → ℝ) (near : ∀ᶠ i in l, R.family.S.a (m i) ≤ r i ∧
      r i ≤ R.family.S.a (m i) * β (m i)^2) : RateIs l (ruler R.family m) r (-1) := by
  have mesh := (Axle.ruler_height (C:=R.family) hm).mesh
  have heat := temperature R simple hm
  have high : RateIs l (ruler R.family m) (fun i => R.family.S.a (m i) * β (m i)^2) (-1) :=
    (mesh.mul (heat.power 2)).swap (by norm_num)
  exact RateIs.of_sandwich mesh (high.pays (large_s R.family hm))
    (near.mono fun _ h => h.1) (near.mono fun _ h => h.2) (large_s R.family hm)

variable (J : ℝ → PhysMS.tower S) (lead : PhysMS.Leading F J)
  {K : (Bel R.family.book).Hierarchy}
  (aligned : ∀ d : ℕ, ∀ᶠ r in trail, AlignO F.sector F.room.kernel.spin K d (J r d))
  {u : Filter (ℕ×ℕ)} (B : Mantle F u) (E : Services R.family f S)
  (pegs : Pegs B L) (near : ∀ᶠ r in trail, R.family.S.a (L.level r) ≤ r ∧
    r ≤ R.family.S.a (L.level r) * R.family.path.levels.clock.hatBeta (L.level r)^2)
include lead aligned E pegs near in
/-- The original physical address receipt for any moving measured field with subpower free coordinates.
Its paid representative is the full regulated atRef operator under the original filter. -/
theorem original {U : Filter (ℕ×ℕ)} [U.NeBot] (cut : U ≤ L.lens)
    (d : ℕ) (v : ℝ → RG17.Free R.family d) (bounded : RateLE trail (ruler R.family L.level) v 0) :
    Axle.Crew U (κ:=trail) (m:=L.level) (fun r => J r d (v r)) := by
  let m := L.level
  have grows := pegs.level.growing
  have late := large_s R.family grows
  obtain ⟨e,earn⟩ := WilsonReportingMeasuredTender.entry B E
    (WilsonReportingMeasuredAdmission.present F J lead aligned) pegs near d
  let fee (r : ℝ) := R.family.S.a (m r)^d * (β (m r)^e * ‖v r‖)
  have heat := ((temperature R E.simpleGate grows).power e).pays late
  have mesh := ((Axle.ruler_height (C:=R.family) grows).mesh.power d).pays late
  have buy : RateLE trail (ruler R.family m) fee (-(d : ℝ)) :=
    (mesh.mul (heat.mul bounded.norm)).mono (by simp)
  refine ⟨⟨fee,buy,?_⟩⟩
  filter_upwards [earn,grows.eventually_ge_atTop (R.family.ref d)] with r paid hm
  obtain ⟨w,price,name⟩ := paid (v r)
  refine ⟨RG17.locatedRef L d r w, fun z => RG17.atRef L d r z w,
    RG17.tendsRef L cut tendsto_const_nhds hm, (RG17.payRef (D:=d) (r:=r) L w).trans name, ?_⟩
  filter_upwards [((Cards.largeMesh f).eventually_ge_atTop (m r)).filter_mono (cut.trans L.certified)]
    with i hi
  exact (WilsonMatrixTicketLanesReportedAdmission.quota R F L d r w hm i.1 i.2 hi).trans_le
    (mul_le_mul_of_nonneg_left price (pow_nonneg (R.family.S.a_pos _).le d))

end YM.Integration.WilsonMatrixTicketLanesReportedCrew
