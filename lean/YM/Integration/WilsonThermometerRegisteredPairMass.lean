import YM.Integration.WilsonThermometerRegisteredFacePair

/-! The original signed grade-six field and its grade-four spectator, at independently
sampled fine sites, against a physical two-field test. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredPairMass

open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits OPE.Therm Climb Trace.Pilot RG12 RG17 PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose Cells Push.GridApprox FVA1
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading
open WilsonThermometerRegisteredCells
open private addressable from YM.Integration.WilsonSeparatedOriginalThermometerCells
open scoped Topology Classical BigOperators

section Purchases
variable {S:Type}[Fintype S][MeasurableSpace S][MeasurableSingletonClass S]
    (φ:Test 2)(χ:Points 2→S)

def weight (o:S):ℂ:=∫x:Points 2,(χ ⁻¹' {o}).indicator (fun y=>φ y) x

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
private theorem unique (x:Points 2)(Y:S→ℂ):
    φ x*Y (χ x)=∑o:S,(χ ⁻¹' {o}).indicator (fun y=>φ y) x*Y o:=by
  classical
  rw [Finset.sum_eq_single (χ x)]
  · rw [Set.indicator_of_mem (show x∈χ ⁻¹' {χ x} from rfl)]
  · intro b _ hn
    rw [Set.indicator_of_notMem (show x∉χ ⁻¹' {b} from fun h=>hn (Eq.symm h)),zero_mul]
  · intro missing;exact (missing (Finset.mem_univ _)).elim

theorem tested (hc:Measurable χ)(Y:S→ℂ):
    φ.applyTo (fun x=>Y (χ x))=∑o,weight φ χ o*Y o:=by
  let f:=fun x:Points 2=>φ x
  have base:Integrable f:=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have ok (o:S):Integrable ((χ ⁻¹' {o}).indicator f):=base.indicator ((measurableSet_singleton o).preimage hc)
  change (∫x,φ x*Y (χ x))=_
  simp_rw [unique φ χ _ Y]
  rw [integral_finsetSum _ (fun o _=>(ok o).mul_const (Y o))]
  exact Finset.sum_congr rfl fun o _=>integral_mul_const _ _

theorem variation (hc:Measurable χ):
    ∑o,‖weight φ χ o‖≤∫x:Points 2,‖φ x‖:=by
  let f:=fun x:Points 2=>φ x
  have base:Integrable f:=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have ok (o:S):Integrable ((χ ⁻¹' {o}).indicator f):=base.indicator ((measurableSet_singleton o).preimage hc)
  calc
    _≤∑o:S,∫x:Points 2,‖(χ ⁻¹' {o}).indicator f x‖:=sum_le_sum fun o _=>norm_integral_le_integral_norm _
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
end Purchases

variable {G:Gauge} (R:Run G) (A:Group R.family 6) {i per:ℕ}
local notation "z₀" => ((i+2,per):UVIndex)
local notation "T" => Site (R.family.side (i+2) per)
local notation "names" => Stock.census (Fin 3)
local notation "surplus" => (names).fire 2
local notation "cut" => (Nat.le_succ_of_le (Nat.le_succ i))

def positions (r:ℝ) (x:Points 2):Fin 2→T:=wrap (R.family.side (i+2) per) ∘
  address (R.family.S.a (i+2)) (r • x)

def offset (r:ℝ) (x:Points 2):T:=positions R r x 1-positions R r x 0

theorem visible (r:ℝ):Measurable (offset R (i:=i) (per:=per) r):=
  (measurable_of_countable (fun a:Fin 2 → Cover=>wrap (R.family.side (i+2) per) (a 1)-wrap _ (a 0))).comp
    ((addressable (R:=R) (i+2) 2).comp (continuous_const_smul r).measurable)

def mass (φ:Test 2) (r:ℝ) (y:T):ℂ:=weight φ (offset R r) y

theorem total (φ:Test 2) (r:ℝ): ∑ y:T,‖mass R φ r y‖ ≤ ∫ x:Points 2,‖φ x‖:=
  variation φ (offset R r) (visible R r)

def leg (x:Fin 2 → T) : Config G (R.family.side (i+2) per) → ℂ :=
  raw A (z₀) 0 1 (![x 0,x 1,0])

def sensor (r:ℝ) (φ:Test 2) : ℂ :=
  φ.applyTo fun x=>R.family.omega (i+2) per (leg R A (positions R r x))

private theorem invariant (ready:∀v:Fin 3,R.family.ref (grade v).val ≤ i+2) (y c:T) :
    R.family.omega (i+2) per (leg R A ((![c,y+c]:Fin 2→T)))=
      R.family.omega (i+2) per (leg R A ![0,y]) := by
  let use:Fin 2→Fin 3:=![0,1]
  let field (j:Fin 2):R.family.book.Token:=
    ⟨(grade (use j)).val,A.station.wheel.atCut (z₀) (index A (grade (use j))) (vector A univ (use j))⟩
  have same (x:Fin 2→T):R.family.numeric (i+2) per field x=R.family.omega (i+2) per (leg R A x):=by
    apply congrArg (R.family.omega (i+2) per)
    funext U
    simp [field,use,Fin.prod_univ_two,leg,WilsonThermometerRegisteredCells.raw]
    rfl
  rw [←same,←same]
  have sites:(![c,y+c]:Fin 2→T)=fun j=>(![0,y]:Fin 2→T) j+c:=by
    funext j;fin_cases j <;> simp
  rw [sites]
  exact R.family.anchored R.makes field (fun j=>ready (use j)) c ![0,y]

theorem aligned (other:T→T) (y:T) :
    WilsonThermometerRegisteredFacePair.physical R A (placement (R:=R) (z₀) (y,other y)) surplus =
      actualTransport R.family (N:=i+2) (leg R A ![0,y]) (cut) :=by
  apply congrArg (fun X=>actualTransport R.family (N:=i+2) X (cut))
  funext U
  have kept:(WilsonThermometerCenteredAlgebra.complement (surplus)).val=({0,1}:Finset (Fin 3)):=by decide
  rw [kept]
  simp [leg,WilsonThermometerRegisteredCells.raw,placement,WilsonThermometerAlignedCells.atOrigin]

/-- Translations act on both literal stencils before either regulator. The third
site on the same appointment can be specified independently for each placement. -/
theorem original (ready:∀v:Fin 3,R.family.ref (grade v).val ≤ i+2)
    (other:T→T) (r:ℝ) (φ:Test 2) :
    sensor R A (i:=i) (per:=per) r φ =
      ∫ U,∑ y:T,mass R φ r y *
        WilsonThermometerRegisteredFacePair.physical R A (placement (R:=R) (z₀) (y,other y)) surplus U
      ∂scene R.family.path (i+2) per i :=by
  let obs(x:Fin 2→T):=R.family.omega (i+2) per (leg R A x)
  have entries:sensor R A (i:=i) (per:=per) r φ=∑ y:T,mass R φ r y*obs ![0,y]:=by
    unfold sensor
    change φ.applyTo (fun x=>obs (positions R r x))=_
    have eq (x:Points 2):obs (positions R r x)=obs ![0,offset R r x]:=by
      let v:=positions R (i:=i) (per:=per) r x
      have same:v=(![v 0,(v 1-v 0)+v 0]:Fin 2→T):=by funext j;fin_cases j <;> simp
      exact (congrArg obs same).trans (invariant R A ready (v 1-v 0) (v 0))
    simp_rw [eq]
    exact tested φ (offset R r) (visible R r) (fun y=>obs ![0,y])
  rw [entries]
  have weighted (y:T):Integrable (fun U=>(R.family.path.rep (i+2) per (i+2)).eval U • leg R A ![0,y] U) (prior G _):=by
    have continuous:Continuous (leg R A ![0,y]):=(R.family.continuousO ..).mul (R.family.continuousO ..)
    simpa only [Complex.real_smul] using
      (RG05Readout.Harvest.dye_grow («C»:=R.family) (N:=i+2) (p:=per) R.makes continuous)
  have lawEq:scene R.family.path (i+2) per (i+2)=law G (R.family.side (i+2) per) (R.family.beta (i+2) per):=by
    have actual:R.family.Makes:=R.makes
    unfold scene law dose Wilson.weight
    rw [(actual.wilson.starts (i+2) per).2]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro y _
    rw [aligned R A other y,integral_const_mul,actualScene_transport R.family R.makes (le_refl (i+2)) (weighted y) (cut),lawEq]
    rfl
  · intro y _
    rw [aligned R A other y]
    exact (actualScene_integrable_of_weighted R.family R.makes (cut)
      (actualTransport_weighted_integrable_of_integrable R.family R.makes (le_refl (i+2)) (weighted y) (cut))).const_mul _

end YM.Integration.WilsonThermometerRegisteredPairMass
