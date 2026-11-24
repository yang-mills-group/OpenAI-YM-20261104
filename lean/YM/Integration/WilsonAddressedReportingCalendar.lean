import YM.Integration.WilsonAddressedReportingMesh

/-! Fix the three physical raw stations and their coarsest common grid
before choosing any submitted vectors, derivative order, or accuracy. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonAddressedReportingCalendar
open Function Filter Finset Set RG Wilson Extraction Table Spec Trace.Pilot GapsContact.Seams
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingFourPool WilsonAddressedReportingScale
open scoped Classical Topology
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) {l : Ultrafilter (ℕ×ℕ)} {H : (Climb.Bel R.family.book).Hierarchy}
  {Z : Trace.Terrace.Arch R.family}
local notation "C₀" => R.family

structure Dates (d T : Fin 3 → ℕ) (g : ℝ → ℝ) (U : ℝ) where
  j : ℝ → Fin 3 → ℕ
  m : ℝ → Fin 3 → ℕ
  first : ℝ → Fin 3
  least : ∀ r a, j r (first r) ≤ j r a
  enters : ∀ a, Tendsto (fun r => j r a) trail atTop
  receipt : ∀ᶠ r in trail, ∀ a,
    Receipt F l (radius (univ.sup T) r) (j r a) (m r a) (d a) (dock (radius (univ.sup T) r)^(T a))
  mesh : ∀ᶠ r in trail, ∀ a,
    (C₀).S.a (j r a)/r ≤ (g r)^2 ∧ (r/(C₀).S.a (j r a))*(g r)^(2*(2*univ.sup T+2)) ≤ U

theorem original (simple : G.Simple) (bliss : Bliss F l Z H) (g : ℝ → ℝ) (hg : Coupling G g)
    (d : Fin 3 → ℕ) :
    ∃ T : Fin 3 → ℕ, ∃ U : ℝ, 0<U ∧ Nonempty (Dates (l:=l) F d T g U) := by
  classical
  choose T offers using fun a : Fin 3 => WilsonThermometerUnitFilingFourPool.original F simple bliss (d a)
  let D := univ.sup T
  let ρ := radius D
  let trueAt (r : ℝ) (P : Fin 3 → ℕ×ℕ) :=
    ∀ a, Receipt F l (ρ r) (P a).1 (P a).2 (d a) (dock (ρ r)^(T a))
  have paid : ∀ᶠ r in trail, ∀ a : Fin 3, ∃ j m, Receipt F l (ρ r) j m (d a) (dock (ρ r)^(T a)) :=
    Filter.eventually_all.mpr fun a => (near D).eventually (offers a)
  have can : ∀ᶠ r in trail, ∃ P, trueAt r P := by
    filter_upwards [paid] with r h
    choose j m seated using h
    exact ⟨fun a => (j a,m a),seated⟩
  let P (r : ℝ) := Classical.epsilon (trueAt r)
  have seated : ∀ᶠ r in trail, trueAt r (P r) := can.mono fun _ h => Classical.epsilon_spec h
  let j (r : ℝ) (a : Fin 3) := (P r a).1
  let m (r : ℝ) (a : Fin 3) := (P r a).2
  obtain ⟨U,positive,paid⟩ := WilsonAddressedReportingMesh.priced F l simple g hg D
  have mesh : ∀ᶠ r in trail, ∀ a : Fin 3,
      (C₀).S.a (j r a)/r ≤ (g r)^2 ∧ (r/(C₀).S.a (j r a))*(g r)^(2*(2*D+2)) ≤ U := by
    filter_upwards [paid,seated] with r price h a
    exact price (T a) (Finset.le_sup (f:=T) (mem_univ a)) _ _ _ (h a)
  choose e _ least using fun r : ℝ => Finset.exists_min_image univ (j r) univ_nonempty
  refine ⟨T,U,positive,⟨j,m,e,fun r a => least r a (mem_univ _),?_,seated,mesh⟩⟩
  intro a
  refine tendsto_atTop.mpr fun k => ?_
  filter_upwards [self_mem_nhdsWithin,mesh,hg.positive,(hg.conforms simple).eventually (gt_mem_nhds zero_lt_one),
    (gt_mem_nhds ((C₀).S.a_pos k)).filter_mono nhdsWithin_le_nhds] with r rp nodes gp unit small
  have less : (C₀).S.a (j r a) ≤ r := (div_le_one rp).mp ((nodes a).1.trans
    (by simpa only [one_pow] using pow_le_pow_left₀ gp.le unit.le 2))
  exact le_of_not_gt fun lt => (not_le_of_gt (less.trans_lt small)) ((C₀).S.strictAnti.antitone lt.le)

end YM.Integration.WilsonAddressedReportingCalendar
end
