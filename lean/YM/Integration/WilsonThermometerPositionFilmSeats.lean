import YM.Integration.WilsonThermometerPositionFirstDeposit
import YM.Integration.WilsonThermometerPositionFilmBank

/-! The latent unit at an unused physical socket is its literal original finite source. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmSeats
open Function Finset Lattice RG Wilson Precision Marker Multi Comparison.RG02 Source Labels
open PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Kick
open PertExtension.Orb.SlotEvaluation RegulatorIR Lodge WilsonThermometerProgramSubmittedWords
open scoped Classical BigOperators
variable {G:Gauge} (C:Run G) {V:Type} [LinearOrder V] [Fintype V] (d:V→ℕ)
  {b f:Side} (o:V→Site b) (h:b.val∣f.val) (s:Finset V) (q:Choice C d b f s)
local notation "live₀" => live C d s q
local notation "grade₀" => (fun j:↥s=>d j.val)
local notation "axis₀" => axis C d s q
local notation "pos₀" => coords C d o h s q
local notation "B" => Lodge.basisR C

omit [Fintype V] [LinearOrder V] in
private theorem unitAt (j:↥s) (missing:j∉live₀) : axis₀ j=0 := by
  cases l:(q j).2 with
  | none=>simp [axis,l]
  | some a=>exact False.elim (missing (by simp [live,l]))

include q in
omit [Fintype V] [LinearOrder V] in
theorem toll : depthF live₀ grade₀ axis₀=depthF univ grade₀ axis₀ := by
  apply sum_subset (subset_univ _)
  intro j _ miss
  rw [unitAt C d s q j miss,(C.family.labels.level _).zero_degree]

include q in
omit [Fintype V] [LinearOrder V] in
theorem raw (n:Side) : Kick.topMark B live₀ grade₀ axis₀ n pos₀=
    Kick.topMark B univ grade₀ axis₀ n pos₀ := by
  unfold Kick.topMark
  apply prod_subset (subset_univ _)
  intro j _ miss
  rw [unitAt C d s q j miss]
  exact unit_zero ((B).owns _)

include q in
omit [Fintype V] in
theorem submitted {M:Type} [Fintype M] [DecidableEq M] (J:Census M) (u:M) (N per:ℕ) :
    Boot.ink J u C.family.path N per (Boot.scout C live₀ grade₀ axis₀ pos₀)=
      Boot.ink J u C.family.path N per (Boot.scout C univ grade₀ axis₀ pos₀) := by
  unfold Boot.ink
  simp only [Boot.scout]
  rw [toll C d s q,raw C d o h s q]

end YM.Integration.WilsonThermometerPositionFilmSeats
