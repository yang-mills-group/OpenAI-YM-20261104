import YM.Integration.WilsonPositionThermometerReading
import YM.Integration.WilsonSeparatedOriginalSlabWatchScalarMesh

/-! The actual thermometer on the fine periodic lattice. Its exact signed cell masses
hold all three independently rounded addresses and the genuine smooth Rose test;
all seven products keep every registered slot of the corresponding thermometer badge. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalThermometerCells
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open OPE OPE.Orbits Climb Trace.Pilot Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox
open WilsonPositionThermometerReading WilsonLimitConstruction
open scoped Topology Classical BigOperators

section Cells
variable {S:Type}[Fintype S][MeasurableSpace S][MeasurableSingletonClass S]
    (φ:Test 3)(χ:Points 3→S)

def weight (o:S):ℂ:=∫x:Points 3,(χ ⁻¹' {o}).indicator (fun y=>φ y) x

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
private theorem unique (x:Points 3)(Y:S→ℂ):
    φ x*Y (χ x)=∑o:S,(χ ⁻¹' {o}).indicator (fun y=>φ y) x*Y o:=by
  classical
  rw [Finset.sum_eq_single (χ x)]
  · rw [Set.indicator_of_mem (show x∈χ ⁻¹' {χ x} from rfl)]
  · intro b _ hn
    rw [Set.indicator_of_notMem (show x∉χ ⁻¹' {b} from fun h=>hn (Eq.symm h)),zero_mul]
  · intro missing;exact (missing (Finset.mem_univ _)).elim

theorem tested (hc:Measurable χ)(Y:S→ℂ):
    φ.applyTo (fun x=>Y (χ x))=∑o,weight φ χ o*Y o:=by
  let f:=fun x:Points 3=>φ x
  have base:Integrable f:=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have ok (o:S):Integrable ((χ ⁻¹' {o}).indicator f):=base.indicator ((measurableSet_singleton o).preimage hc)
  change (∫x,φ x*Y (χ x))=_
  simp_rw [unique φ χ _ Y]
  rw [integral_finsetSum _ (fun o _=>(ok o).mul_const (Y o))]
  exact Finset.sum_congr rfl fun o _=>integral_mul_const _ _

theorem variation (hc:Measurable χ):
    ∑o,‖weight φ χ o‖≤∫x:Points 3,‖φ x‖:=by
  let f:=fun x:Points 3=>φ x
  have base:Integrable f:=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have ok (o:S):Integrable ((χ ⁻¹' {o}).indicator f):=base.indicator ((measurableSet_singleton o).preimage hc)
  calc
    _≤∑o:S,∫x:Points 3,‖(χ ⁻¹' {o}).indicator f x‖:=sum_le_sum fun o _=>norm_integral_le_integral_norm _
    _=_:=by
      rw [←integral_finsetSum _ (fun o _=>(ok o).norm)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x=>by
        change (∑i:S,‖(χ ⁻¹' {i}).indicator f x‖)=‖φ x‖
        rw [sum_eq_single (χ x)]
        · rw [Set.indicator_of_mem (show x∈χ ⁻¹' {χ x} from rfl)]
        · intro b _ hn
          rw [Set.indicator_of_notMem (show x∉χ ⁻¹' {b} from fun h=>hn (Eq.symm h)),norm_zero]
        · intro missing;exact (missing (Finset.mem_univ _)).elim
end Cells

variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (r:ℝ)(L:Layout F)(E:RG17.Free R.family 6→L[ℂ] R.family.label 6)(z:UVIndex)
local notation "Sites"=>Fin 3→Site (R.family.side z.1 z.2)

def positions (x:Points 3):Sites:=wrap _ ∘ address (R.family.S.a z.1) (r • x)
private theorem addressable (N n:ℕ):Measurable (address (R.family.S.a N):Points n→(Fin n → Cover)):=by
  apply measurable_to_countable;intro z;exact measurable_segment (R.family.S.a_pos N) (address (R.family.S.a N) z)

theorem placed:Measurable (positions (R:=R) r z):=
  (measurable_of_countable (fun a:Fin 3 → Cover=>wrap (R.family.side z.1 z.2) ∘ a)).comp
    ((addressable (R:=R) z.1 3).comp (continuous_const_smul r).measurable)

def observed (o : Sites)(s:Finset (Fin 3)):ℂ:=
  R.family.omega z.1 z.2 (fun U=>∏i:Fin 3,
    R.family.O z.1 z.2 (RG17.atRef L 6 r z (E (leg R.family s i))) (o i) U)

def field (x:Points 3):ℂ:=WilsonPositionThermometerConnected.value (observed F r L E z (positions (R:=R) r z x))

theorem physical (φ:Test 3):
    φ.applyTo (field F r L E z)=
      ∑o,weight φ (positions (R:=R) r z) o*WilsonPositionThermometerConnected.value (observed F r L E z o):=by
  exact tested φ _ (placed (R:=R) r z) (fun o=>WilsonPositionThermometerConnected.value (observed F r L E z o))

end YM.Integration.WilsonSeparatedOriginalThermometerCells
end
