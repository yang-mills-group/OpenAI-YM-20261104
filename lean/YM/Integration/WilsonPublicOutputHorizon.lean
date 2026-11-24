import YM.Integration.WilsonPublicOutputRows
import YM.XSpace.Symphony

/-! Coordinates of the independently prescribed complete output and a nonzero
weight-six physical direction on the same determining measurement. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicOutputHorizon
open Filter Set Table Spec OPE PhysMS Trace.Pilot Climb Maxwell Maxwell.Free
open FVA2 FVA2.Register FVA2.ColorCode FVA2.Scale Pert Pert.Position MS MS.Local.Physical
open MS.Menus MS.Land MS.Theater RegulatorIR.FVAAlt2.Lodge Extra.FD OPE.Levy
open XSpace XSpace.Photo XSpace.Normalize XSpace.Rose XSpace.Graph3 XSpace.Cirrus XSpace.AxesTangent
open PhysicalNext.Repeat.Legato WilsonMatrixTicketLanesSmearedPivot
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (Z : WilsonPrescription G)
local notation "Print" => Press.portDeck G

def dual {h : ℕ} (b : Glyph Print h) : (Bel R.family.book).Field h →L[ℂ] ℂ :=
  (((Daylight Print h).coord b).comp (exactField R.family.labels h).toLinearMap).toContinuousLinearMap

theorem coordinate {h n : ℕ} (M : MS_Data G (Position.OpenAxis.Plot Print))
    (d : Fin n → ℕ) (v : (i : Fin n) → (Bel R.family.book).Field (d i)) (μ : ℝ)
    (x : Points n) (u : ℝ) (q : ℕ) (b : Glyph Print h) (y : (Bel R.family.book).Field h)
    {T : ℝ} (paid : ‖y-WilsonMacroscopicRichMSCoefficient.field R M h d v μ x u q‖ ≤ T) :
    ‖dual (R:=R) b y-WilsonMacroscopicRichMSCoefficient.coefficient R M d v μ x u q b‖ ≤
      ‖dual (R:=R) b‖*T := by
  rw [←WilsonMacroscopicRichMSCoefficient.filed R M h d v μ x u q b]
  change ‖dual (R:=R) b y - dual (R:=R) b _‖ ≤ _
  rw [←map_sub]
  exact ((dual (R:=R) b).le_opNorm _).trans (mul_le_mul_of_nonneg_left paid (norm_nonneg _))

/-- The zero-field test of the independent multilinear first variation would make the
strictly negative, publicly stipulated Rose integral vanish. -/
theorem cubic_ne_zero (W : Initialize G) (V : Normalize.Store G) (simple : G.Simple) :
    Rose.toll G ≠ 0 := by
  intro hz
  obtain ⟨Y⟩ := Rose.nominate W simple V
  have zero (x : Points 3) : checked1 W V 6 x (Rose.tag G) = 0 :=
    (checked1 W V 6 x).map_coord_zero (i:=(0:Fin 3)) (by exact hz)
  have integrand (x : Points 3) :
      Y.image x * Rose.numeric G Y.cut (x 0) (x 1) (x 2) = 0 := by
    rw [Rose.numeric_pays simple V W Y.grants Y.manages Y.image
      (fun y hy => (Y.segment hy).1) x,zero]
    simp
  have no : Rose.cT Y.cut G Y.image = 0 := by
    unfold Rose.cT
    simp_rw [integrand]
    simp
  exact Y.fresh.ne no

def cubic : (Bel R.family.book).Field 6 := (Maxwell.Free.fields R.family.labels 6).symm (Rose.toll G)

/-- Every sufficiently small real radius has a nonzero actual two-site reading on
this physical cubic. The outer date and the test are those of the same true Wilson tower. -/
theorem six {Y : (Bel R.family.book).Hierarchy}
    (lead : Leading F J) (owed : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d)
    (W : Initialize G) (simple : G.Simple) :
    ∃ B : Profiles R 6, (∀ j : B.probes.index, ∃ w : (standard R.family.book.grid).Ref 6,
      B.probes.shell j = WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid 6 w) ∧
      ∀ (g : ℝ → ℝ), Coupling G g → ∀ A : ℕ, ∀ᶠ r in trail,
        ∃ j : B.probes.index, row F J Z B (r/(g r)^A) (J r 6 (cubic (R:=R))) j ≠ 0 := by
  obtain ⟨B,two,paid⟩ := WilsonMacroscopicRichTwoDatePivot.original F J Z lead owed simple 6
  obtain ⟨K,_,buy⟩ := paid 1 zero_lt_one
  have source := cubic_ne_zero W Z.store simple
  have nz : cubic (R:=R) ≠ 0 := by
    intro e
    apply source
    simpa only [cubic,LinearEquiv.apply_symm_apply,map_zero] using
      congrArg (Maxwell.Free.fields R.family.labels 6) e
  refine ⟨B,two,?_⟩
  intro g hg A
  have date := WilsonThermometerWeakPairClock.small simple g hg A
  filter_upwards [date.eventually buy,hg.positive,length_rate.pos,
    (hg.conforms simple).eventually (ge_mem_nhds zero_lt_one)] with r reading gp rp cap
  by_contra! all
  let t := r/(g r)^A
  have no : row F J Z B t (J r 6 (cubic (R:=R))) = 0 := funext all
  have eq : (g r)^A * WilsonThermometerWeakPairClock.scale g A r = r := by
    unfold WilsonThermometerWeakPairClock.scale
    field_simp [gp.ne']
  have low := reading ((g r)^A) ⟨pow_pos gp A,pow_le_one₀ gp.le cap⟩ (J r 6 (cubic (R:=R)))
  rw [eq,LinearEquiv.symm_apply_apply,show WilsonThermometerWeakPairClock.scale g A r = t from rfl,
    no,norm_zero,mul_zero] at low
  exact (norm_pos_iff.mpr nz).not_ge low
end YM.Integration.WilsonPublicOutputHorizon
