import YM.Integration.WilsonMaxwellThermometerKineticAppointment

/-! The signed Rose and the true original running law on an enrolled fine date.
The independent run retains its own mesh and physical input table throughout. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerKineticFineRose
open Filter Set Function Maxwell XSpace XSpace.Cirrus XSpace.Normalize FVA2 FVA2.Register
open Lattice Wilson RG Source Extraction Table Spec Climb PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS
open Pert.Asymptotics WilsonMaxwellThermometerKineticPanel WilsonPositionThermometerCapStation WilsonPositionCapTransport
open scoped Topology Classical
variable {G : Gauge} (Z : WilsonPrescription G) {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (A : ℝ → Group R.family 6)
    {Y : Ultrafilter (ℕ×ℕ)} {H : (Bel R.family.book).Hierarchy} {arch : Trace.Terrace.Arch R.family}
    (simple : G.Simple) {B : ℕ} (hB : 0<B) (fine index : ℝ→ℕ)
local notation "visits" => trail.curry (Y : Filter (ℕ×ℕ))
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "m" => WilsonMeasuredWindow.stop R.family.path.levels simple B
local notation "ref" => (fun r : ℝ => (Real.sqrt (R.family.path.levels.clock.hatBeta (m r)))⁻¹)
local notation "out" => WilsonPositionGradedThermometerHearing.offer F J Z.store Z.criterion A
local notation "thermal" => WilsonPositionRawCutoff.thermometer Z F J A
def axis (w : ℝ×(ℕ×ℕ)) : ℝ := regulatorRun R.family w.2.1 w.2.2 (fine w.1)
def regulator (w : ℝ×(ℕ×ℕ)) : Mesh := Z.run.step (index w.1)
local notation "u" => axis (R:=R) fine
local notation "mesh" => regulator Z index
local notation "enrolled" => WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index

private theorem currency (j N per : ℕ) (live : j≤N) :
    (Real.sqrt (R.family.path.levels.clock.hatBeta j))⁻¹ ≤ 2*regulatorRun R.family N per j := by
  let x:=Real.sqrt (R.family.path.levels.clock.hatBeta j)
  let y:=Real.sqrt (R.family.path.β N per j)
  have xp : 0<x := Real.sqrt_pos.mpr (zero_lt_one.trans (R.family.path.levels.fits.delayed j))
  have yp : 0<y := Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live)
  have band := (R.makes.wilson.represents N per j live).band.2
  have h : y≤2*x := by
    have xx : x^2=R.family.path.levels.clock.hatBeta j := Real.sq_sqrt (by linarith [R.family.path.levels.fits.delayed j])
    have yy : y^2=R.family.path.β N per j := Real.sq_sqrt (Overlay.beta_positive R.makes.wilson live).le
    change R.family.path.β N per j ≤ 2*R.family.path.levels.clock.hatBeta j at band
    nlinarith [xx,yy,sq_nonneg (y-2*x)]
  change x⁻¹ ≤ 2*y⁻¹
  field_simp [xp,yp]
  simpa only [mul_comm] using h

include hB in
theorem appointed (schedule : enrolled) (prior : (Y:Filter _)≤f.fuse) :
    Tendsto mesh visits Front ∧ ∀ᶠ w in visits, 0<u w ∧ ref w.1≤4*u w := by
  have high := (WilsonAdmissionScale.logarithm_tendsto R.family.path.levels simple).comp
    (WilsonMeasuredWindow.stop_tendsto R.family.path.levels simple B hB)
  have long := tendsto_atTop_add_const_left _ (2:ℝ) high
  have lower := (tendsto_rpow_atTop (show 0<(3:ℝ)/2 by norm_num)).comp long
  have times : Tendsto index trail atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [schedule,lower.eventually_ge_atTop ((k:ℝ)*Real.log Z.run.ratio)] with r seated far
    have lr := Real.log_pos (show 1<(Z.run.ratio:ℝ) by exact_mod_cast (show 1<Z.run.ratio by have h:=Z.run.large; omega))
    exact_mod_cast (mul_le_mul_iff_of_pos_right lr).mp (far.trans seated.2.1)
  have radius : Tendsto (Prod.fst : ℝ×(ℕ×ℕ)→ℝ) visits trail := tendsto_fst.mono_left Filter.curry_le_prod
  refine ⟨(goesFront (Expense.Stretched.runs Z.run)).comp (times.comp radius),?_⟩
  have near := (WilsonMaxwellThermometerKineticAppointment.original R simple hB Z schedule f Y prior).eventually_const_lt
    (show (1/2:ℝ)<1 by norm_num)
  apply eventually_curry_iff.mpr
  filter_upwards [schedule,eventually_curry_iff.mp near] with r seated close
  filter_upwards [(Next.UVStress.large_mesh f (fine r)).filter_mono prior,close] with z live stayed
  have mpre := seated.1.trans live
  have pos : 0<regulatorRun R.family z.1 z.2 (m r) := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson mpre))
  have lower_bound := (lt_div_iff₀ pos).mp stayed
  have amount := currency (R:=R) (m r) z.1 z.2 mpre
  exact ⟨inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live)),by unfold axis; linarith only [amount,lower_bound]⟩

def panel (E : ℝ×(ℕ×ℕ) → Board) : Prop := ∀ ε>0, ∀ᶠ w in visits,
  |(out w.1 w.2).re - sampled Z (E w) 1 (u w)| +
    |sampled Z (E w) 1 (u w)-WilsonPositionFineDetectorSource.faces Z (mesh w) 1 (u w)| ≤ ε*ref w.1

include hB in
theorem original (pace : WilsonWindowReportingPace.Slow R.kit) (bliss : Bliss F Y arch H)
    (book : Book (f:=f) (l:=Y) (H:=H) A J) (lead : Leading F J)
    (schedule : enrolled) (E : ℝ×(ℕ×ℕ)→Board)
    (test : panel (Y:=Y) Z F J A simple (B:=B) fine index E) :
    Tendsto (fun w : ℝ×(ℕ×ℕ) => thermal w.1 w.2 / u w) visits (𝓝 1) ∧
    Tendsto (fun r=>θ r/(Real.sqrt (arch.β (m r)))⁻¹) trail (𝓝 1) ∧ Coupling G θ := by
  obtain ⟨cofinal,live⟩:=appointed (R:=R) (f:=f) Z simple hB fine index schedule bliss.lies
  let physical (w:ℝ×(ℕ×ℕ)) := (out w.1 w.2).re - sampled Z (E w) 1 (u w)
  let changed (w:ℝ×(ℕ×ℕ)) := sampled Z (E w) 1 (u w) - WilsonPositionFineDetectorSource.faces Z (mesh w) 1 (u w)
  have pay (a:ℝ×(ℕ×ℕ)→ℝ) (fee:∀ w,|a w|≤|physical w|+|changed w|) :
      Tendsto (fun w=>a w/u w) visits (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε he
    filter_upwards [live,test (ε/8) (by positivity)] with w hw observed
    rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hw.1,div_lt_iff₀ hw.1]
    have bound:=mul_le_mul_of_nonneg_left hw.2 (show 0≤ε/8 by positivity)
    have small:= (fee w).trans (observed.trans bound)
    exact small.trans_lt (by nlinarith [mul_pos he hw.1])
  have slope := WilsonMaxwellThermometerKineticPanel.hearing (Y:=Y) Z F J A simple mesh u E cofinal
    (live.mono fun _ h=>h.1)
    (pay physical (fun w=>le_add_of_nonneg_right (abs_nonneg (changed w))))
    (pay changed (fun w=>le_add_of_nonneg_left (abs_nonneg (physical w))))
  exact ⟨slope,WilsonMaxwellThermometerKineticRunning.original Z F J A simple pace hB bliss book lead u
    (live.mono fun _ h=>h.1) slope (WilsonMaxwellThermometerKineticAppointment.original R simple hB Z schedule f Y bliss.lies)⟩

end YM.Integration.WilsonMaxwellThermometerKineticFineRose
