import YM.Integration.WilsonMaxwellThermometerKineticFineRose

/-! One finite position request containing the target and all seven Rose faces.
The numerical tolerance is in the reference Wilson currency, before discovering the physical parameter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerKineticRequest
open Finset Filter Set Function Maxwell XSpace XSpace.Structure1 XSpace.Cirrus XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open Lattice Wilson RG Source Extraction Table Spec Climb PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS
open OPE OPE.Orbits MS MS.Fleet MS.Land
open Pert.Asymptotics WilsonMaxwellThermometerKineticPanel WilsonPositionThermometerCapStation WilsonPositionCapTransport
open WilsonPositionSeparatedProfileMatching
open scoped BigOperators Topology Classical
variable {G : Gauge} (Z : WilsonPrescription G) {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (A : ℝ → Group R.family 6)
    {Y : Ultrafilter (ℕ×ℕ)} {H : (Bel R.family.book).Hierarchy} {arch : Trace.Terrace.Arch R.family}
    (simple : G.Simple) {B : ℕ} (hB : 0<B) (fine index : ℝ→ℕ)
    (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n)
local notation "visits" => trail.curry (Y : Filter (ℕ×ℕ))
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "m" => WilsonMeasuredWindow.stop R.family.path.levels simple B
local notation "ref" => (fun r : ℝ => (Real.sqrt (R.family.path.levels.clock.hatBeta (m r)))⁻¹)
local notation "out" => WilsonPositionGradedThermometerHearing.offer F J Z.store Z.criterion A
local notation "u" => WilsonMaxwellThermometerKineticFineRose.axis (R:=R) fine
local notation "reg" => WilsonMaxwellThermometerKineticFineRose.regulator Z index
local notation "enrolled" => WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index

def earned (q : ℕ) : Prop :=
  ∃ (E : ℝ×(ℕ×ℕ)→Board) (w : ℝ → (ℕ × ℕ) → Fin n → R.family.label d) (c : ℝ → Fin n → R.family.label d),
  (∀ᶠ r in trail, ∀ i, Tendsto (fun z=>w r z i) (Y:Filter _) (𝓝 (c r i)) ∧
    S.project d (c r i)=WilsonPositionHomogeneousPanel.field F J Z d v r i) ∧
  ∀ δ>0, ∀ᶠ r in trail, ∃ D : Handoff.Directory Z (index r) (Handoff.Directory.budget G n d+q),
    ∀ᶠ z in (Y:Filter (ℕ × ℕ)),
      ‖(∑ site : WilsonPositionPhysicalCellTest.Sites R z n, WilsonPositionPhysicalCellTest.mass φ r z site *
        R.family.ensemble (N:=z.1) (p:=z.2) (fun _=>d) site (w r z)) -
        WilsonPositionOriginalCellAverage.average (Z.run.step (index r)) φ
          (WilsonPositionEpochCellTariff.data D d q v (u (r,z):ℂ))‖ ≤ δ*(ref r)^q ∧
      |(out r z).re - sampled Z (E (r,z)) q (u (r,z))| +
        |sampled Z (E (r,z)) q (u (r,z)) - WilsonPositionFineDetectorSource.faces Z (reg (r,z)) q (u (r,z))|
        ≤ δ*(ref r)^q

local notation "request" => earned (Y:=Y) Z F J A simple (B:=B) fine index d φ v

theorem first (test : request 1) :
    ∃ E, WilsonMaxwellThermometerKineticFineRose.panel (Y:=Y) Z F J A simple (B:=B) fine index E := by
  obtain ⟨E,_,_,_,income⟩:=test
  refine ⟨E,fun δ hd=>eventually_curry_iff.mpr ?_⟩
  filter_upwards [income δ hd] with r row
  obtain ⟨_,sale⟩:=row
  exact sale.mono fun z hz=>by simpa only [pow_one] using hz.2

include hB in
theorem restored (pace : WilsonWindowReportingPace.Slow R.kit) (schedule : enrolled)
    (prior : (Y:Filter _) ≤ f.fuse) (rate : Coupling G θ) (q : ℕ) (test : request q) :
    WilsonOriginalPositionFineScheme.paired (l:=Y) F J Z A fine index d φ v q := by
  obtain ⟨E,w,c,labels,income⟩:=test
  refine ⟨w,c,labels,?_⟩
  have paid := WilsonPositionFineCouplingBill.finer R simple hB pace θ rate
  have taken:=WilsonMaxwellThermometerKineticFineRose.appointed (R:=R) (f:=f) Z simple hB fine index schedule prior
  have change : ∀ᶠ r in trail, ref r≤8*|θ r| := by
    filter_upwards [paid,schedule,eventually_curry_iff.mp taken.2] with r receive selected ready
    obtain ⟨z,cut,credit⟩ := (((Next.UVStress.large_mesh f (fine r)).filter_mono prior).and ready).exists
    have back := (receive (fine r) z.1 z.2 selected.1 cut).2
    have cash : ref r≤4*regulatorRun R.family z.1 z.2 (fine r) := credit.2
    nlinarith only [cash,back,le_abs_self (θ r)]
  let coin:=min 1 |Rose.c_T Z.criterion|
  have cp:0<coin:=lt_min zero_lt_one (abs_pos.mpr Z.criterion.fresh.ne)
  intro δ hd
  let cost:=δ*coin/(8:ℝ)^q
  have positive : 0<cost:=div_pos (mul_pos hd cp) (by positivity)
  have docket:=WilsonPositionFineDetectorSource.scheduled Z F J A simple hB fine index schedule
  filter_upwards [income cost positive,change,docket] with r row back used
  obtain ⟨D,sale⟩:=row
  refine ⟨D,?_⟩
  have rp:0≤ref r:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have refund : cost*(ref r)^q ≤ (δ*|θ r|^q)*coin := by
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ rp back q) positive.le).trans_eq
    dsimp [cost]
    rw [mul_pow]
    field_simp
  have common := mul_nonneg hd.le (pow_nonneg (abs_nonneg (θ r)) q)
  filter_upwards [sale] with z hz
  refine ⟨hz.1.trans (refund.trans ?_),?_⟩
  · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) common).trans_eq (mul_one _)
  · apply (used q (u (r,z)) z (δ*|θ r|^q)).mpr
    apply (abs_sub_le _ (sampled Z (E (r,z)) q (u (r,z))) _).trans
    exact hz.2.trans (refund.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) common))

end YM.Integration.WilsonMaxwellThermometerKineticRequest
