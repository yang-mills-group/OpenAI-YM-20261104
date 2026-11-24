import YM.Integration.WilsonMaxwellThermometerNominatedGroundPanel
import YM.Integration.WilsonMaxwellThermometerNominatedOrdinary
import YM.Integration.WilsonMaxwellThermometerNominatedFilingRate

/-! The six lower signed readings and the single compensated full reading on
the named original (6,4,4) cells suffice for the integrated first-order log. -/
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedGroundProgram
open Finset Filter Function Set Lattice Wilson Labels RG Source PhysicalNext.Repeat.Legato RG17
open OPE OPE.Orbits Next.UVStress Climb Table Spec Extraction Trace Trace.Pilot PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose
open MeasureTheory WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Mark
open WilsonReflectedPhysicalRate WilsonMaxwellThermometerNominatedGroundPanel
open Marker QuadraticLocal Extra.Trajectories Primitives.GCC.Anchor WilsonThermometerCenteredAlgebra
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedSource
open WilsonMaxwellThermometerNominatedProperFaces WilsonMaxwellThermometerNominatedDelta
open WilsonMaxwellThermometerNominatedGroundPurse
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Final R.family f S) (J:ℝ→tower S) (V:Store G) (A:ℝ→Group R.family 6)
  {Y:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy}
  (simple:G.Simple) (hl:(Y:Filter _)≤f.fuse) (book:Book (f:=f) (l:=Y) (H:=H) A J)
local notation "J₀" => Stock.census (Fin 3)

abbrev Visit:=ℝ×(ℕ×ℕ)
variable (v:ℕ)
local notation "k₀" => WilsonReflectedPhysicalRate.launch R simple v
local notation "g₀" => WilsonPositionThermometerSevenFaceRate.temperature (R:=R) simple (B:=v)
local notation "pub" => WilsonMaxwellThermometerNominatedGroundPanel.actual R F J V A
local notation "basis" => WilsonOriginalThermometerPalette.levels
variable (caps:Fin 3→ℕ) (room:∀i,basis i<caps i)
    (test:Visit→Points 3→WilsonCoeffUV.Wheel.Case caps) (q a:ℕ)

def filed (w:Visit) (x:Points 3):Marker.Poly J₀:=
  let o:=WilsonSeparatedOriginalThermometerCells.positions (R:=R) w.1 w.2 x
  WilsonMaxwellThermometerNominatedOrdinary.table R
    (WilsonPositionCorrectedCap.adjusted F J V A w.1) w.2.1 w.2.2 (k₀ w.1) caps room
    (WilsonThermometerAlignedCells.atOrigin (WilsonThermometerAlignedCells.offsets o))
    (test w x) (fun _=>0) (g₀ w.1 w.2) q a (fun _=>1)
local notation "reported" => WilsonMaxwellThermometerNominatedGroundProgram.filed R F J V A simple v caps room test q a
local notation "W" => WilsonMaxwellThermometerNominatedGroundPurse.policy R
local notation "curr" => (trail.curry (Y:Filter _))

include hl in
theorem clock (slow:WilsonWindowReportingPace.Slow R.kit) (wide:0<v)
    :
    (∀ᶠw:Visit in curr,0<g₀ w.1 w.2) ∧ Tendsto (fun w:Visit=>g₀ w.1 w.2) curr (𝓝 0):=by
  let k:=k₀
  let A₀:=R.family.path.levels
  have rise:Tendsto A₀.clock.hatBeta atTop atTop:=
    tendsto_atTop_add_const_left _ _ (A₀.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have dates:=(WilsonReflectedPhysicalRate.dates R simple slow v wide).2.grows
  have cool:Tendsto (fun r:ℝ=>(Real.sqrt (A₀.clock.hatBeta (k r)))⁻¹) trail (𝓝 0):=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp (rise.comp dates))
  refine ⟨eventually_curry_iff.mpr (.of_forall fun r=>?_),?_⟩
  · filter_upwards [(large_mesh f (k r)).filter_mono hl] with z late
    exact inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson late))
  · apply Metric.tendsto_nhds.mpr
    intro δ pos
    apply eventually_curry_iff.mpr
    filter_upwards [cool.eventually_lt_const (show 0<δ/2 by linarith)] with r low
    filter_upwards [(large_mesh f (k r)).filter_mono hl] with z late
    have band:=(WilsonMaxwellThermometerPublicFiling.band R simple v r z.1 z.2 late).1
    change |g₀ r z| ≤ 2*(Real.sqrt (A₀.clock.hatBeta (k r)))⁻¹ at band
    rw [Real.dist_eq,sub_zero];linarith

include book hl in
theorem compact (lead:Leading F J) (slow:WilsonWindowReportingPace.Slow R.kit) (wide:0<v)
    {E:Set (Points 3)} (comp:IsCompact E) (sep:E⊆conf 3)
    (C:ℝ) (cp:0≤C)
    (six:∀ᶠw:Visit in curr,∀x∈E,∀s:(J₀).Mode,s≠(J₀).quiet→s≠WilsonThermometerCenteredAlgebra.full→
       ‖(pub w x).part s-(reported w x).part s‖≤C*(g₀ w.1 w.2))
    (δ:ℝ) (small:0<δ):
    ∀ᶠw:Visit in curr,∀x∈E,‖WilsonMaxwellThermometerNominatedDelta.discrepancy (pub w x) (reported w x) (W x)‖≤δ*g₀ w.1 w.2:=by
  obtain ⟨gp,tiny⟩:=clock R simple hl v slow wide
  by_cases inhabited:E.Nonempty
  · let chooser (w:Visit):=if h:∃x∈E,δ*g₀ w.1 w.2<‖WilsonMaxwellThermometerNominatedDelta.discrepancy (pub w x) (reported w x) (W x)‖ then h.choose else inhabited.choose
    have inside (w:Visit):chooser w∈E:=by
      dsimp only [chooser]
      split
      next h=>exact h.choose_spec.1
      next _=>exact inhabited.choose_spec
    have quiet (w:Visit):(reported w (chooser w)).part (J₀).quiet=1:=
      WilsonMaxwellThermometerNominatedOrdinary.quiet _ _ _ _ _ _ _ _ _ _ _ _ _ _
    have T:=WilsonMaxwellThermometerNominatedGroundPanel.compared R F J V A simple hl book lead comp sep
      chooser (.of_forall inside) (fun w=>reported w (chooser w)) _ C cp gp tiny (.of_forall quiet)
      (six.mono fun w h=>h _ (inside w))
    filter_upwards [gp,T.eventually_lt_const small] with w positive sharp x hx
    by_contra! fails
    have bad:∃x∈E,δ*g₀ w.1 w.2<‖WilsonMaxwellThermometerNominatedDelta.discrepancy (pub w x) (reported w x) (W x)‖:=⟨x,hx,fails⟩
    have excess:δ*g₀ w.1 w.2<‖WilsonMaxwellThermometerNominatedDelta.discrepancy (pub w (chooser w)) (reported w (chooser w)) (W (chooser w))‖:=by
      simpa only [chooser,dif_pos bad] using bad.choose_spec.2
    exact (not_lt_of_ge (le_of_lt ((div_lt_iff₀ positive).mp sharp))) excess
  · exact .of_forall fun _ _ hx=>(inhabited ⟨_,hx⟩).elim

include book hl in
theorem integrated (lead:Leading F J) (slow:WilsonWindowReportingPace.Slow R.kit) (wide:0<v)
    (φ:Test 3) (C:ℝ) (cp:0≤C)
    (six:∀ᶠw:Visit in curr,∀x∈tsupport (fun y=>φ y),∀s:(J₀).Mode,
       s≠(J₀).quiet→s≠WilsonThermometerCenteredAlgebra.full→
       ‖(pub w x).part s-(reported w x).part s‖≤C*(g₀ w.1 w.2)) (δ:ℝ) (small:0<δ):
    ∀ᶠw:Visit in curr,‖φ.applyTo (fun x=>WilsonMaxwellThermometerNominatedDelta.discrepancy (pub w x) (reported w x) (W x))‖
      ≤(∫x,‖φ x‖)*δ*g₀ w.1 w.2:=by
  have buy:=compact R F J V A simple hl book v caps room test q a lead slow wide φ.hasCompactSupport φ.tsupport_subset C cp six δ small
  filter_upwards [buy] with w bound
  let fee:=δ*g₀ w.1 w.2
  have base:Integrable (fun x=>‖φ x‖*fee):=(φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm.mul_const _
  have price:‖φ.applyTo (fun x=>WilsonMaxwellThermometerNominatedDelta.discrepancy (pub w x) (reported w x) (W x))‖≤∫x,‖φ x‖*fee:=by
    apply norm_integral_le_of_norm_le base (.of_forall fun x=>?_)
    rw [norm_mul]
    by_cases hz:φ x=0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left (bound _ (subset_tsupport _ hz)) (norm_nonneg _)
  rw [integral_mul_const] at price
  exact price.trans_eq (mul_assoc _ _ _).symm

end YM.Integration.WilsonMaxwellThermometerNominatedGroundProgram
