import YM.Integration.WilsonReportingForestAngularReflection
import YM.Integration.WilsonReportingForestAngularCurrency
import YM.Integration.WilsonPositionSeparatedProfileReportingPrimary
import YM.Integration.WilsonReportingForestCompactAngles

/-! The angular rejection on every plaquette incident on the *submitted*
physical activity support. Its cost is linear in the genuine rooted length,
including supports and radii chosen after the date and period. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingMolecularMaskRegion
open Filter Set Finset MeasureTheory Lattice Wilson RG RG16 OPE.Therm Pressure
open PhysicalNext.Repeat.Legato WilsonReportingForestPivots WilsonPositionSeparatedProfileReportingPrimary
open WilsonReportingForestAngularFare WilsonReportingForestAngularReflection
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)
local notation "A"=>R.family.path.levels

/-- Use the minimizing connected cover to count the sites and the two extra
plaquette layers. One native plaquette is counted with its orientation. -/
theorem faces {n:Side} (b:ℝ) (one:1≤b) (X:Support n) :
    ((cover X).card:ℝ)≤(coverNumber (radiusB b) X:ℝ)*((5:ℝ)^8*Fintype.card PlaqAxes)*b^8 := by
  let B:=radiusB b
  obtain ⟨Y,covers,card⟩:=coverNumber_realized B X
  have sites:X.card≤Y.card*(B+B+1)^4:=(Finset.card_le_card covers.1).trans (Lattice.Corona.halo_size Y B)
  rw [card] at sites
  have count:(cover X).card ≤ (coverNumber B X*(B+B+1)^4)*5^4*Fintype.card PlaqAxes:=by
    rw [cover,card_product,card_univ]
    exact Nat.mul_le_mul_right _ ((Lattice.Corona.halo_size X 2).trans (Nat.mul_le_mul_right _ sites))
  have bp:0≤b:=zero_le_one.trans one
  have lg:0≤Real.log b:=Real.log_nonneg one
  have major:(B:ℝ)≤b^2+1:=
    (Nat.ceil_lt_add_one (sq_nonneg (Real.log b))).le.trans (add_le_add (pow_le_pow_left₀ lg (Real.log_le_self bp) 2) le_rfl)
  have size:((B+B+1:ℕ):ℝ)≤5*b^2:=by push_cast; nlinarith only [major,one,show 1≤b^2 from one_le_pow₀ one]
  have bound:((B+B+1:ℕ):ℝ)^4≤(5*b^2)^4:=pow_le_pow_left₀ (by positivity) size _
  calc
    _≤(coverNumber B X:ℝ)*((B+B+1:ℕ):ℝ)^4*5^4*Fintype.card PlaqAxes:=by exact_mod_cast count
    _≤(coverNumber B X:ℝ)*(5*b^2)^4*5^4*Fintype.card PlaqAxes:=by gcongr
    _=_:=by unfold B;ring

theorem purchased (simple:G.Simple) (gate:posted R) (q:ℕ) {ε:ℝ} (ep:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀N,m<N→∀per (X:Support (R.family.side (m+1) per)),
    let b:=(A).clock.hatBeta (m+1)
    let D:=House.chilly (G:=G) (cover X) (angularCut b)
    let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
    (scene R.family.path N per (m+1)).real Dᶜ≤(coverNumber (radiusB b) X:ℝ)*(ε*g^q) ∧
    ∀Y⊆X,∀U∈D,Healthy (Pressure.temp b) Y U := by
  let C:ℝ:=5^8*Fintype.card PlaqAxes
  have cp:0<C:=by dsimp [C];positivity
  have eps:0<ε/C:=div_pos ep cp
  filter_upwards [WilsonReportingForestAngularReflection.original R simple gate (8+q+1),
    WilsonReportingForestAngularCurrency.currency R simple 8 q eps,smaller R simple,
    (tendsto_add_atTop_nat 1).eventually (narrow (H:=R.family.path) simple)]
    with m law spend wide cold N live per X b D g
  have one:1≤b:=((A).fits.delayed _).le
  have low:angularCut b≤Pressure.temp b:=by
    apply wide.trans;change cool (A) (m+1)≤(A).clock.threshold (m+1);linarith only [cold.1,cold.2]
  have exp0:0≤(b⁻¹)^(8+q+1):=pow_nonneg (inv_nonneg.mpr (zero_le_one.trans one)) _
  letI:IsProbabilityMeasure (scene R.family.path N per (m+1)):=probability R.makes.wilson live
  constructor
  · calc
      _≤((cover X).card:ℝ)*(b⁻¹)^(8+q+1):=House.cool_miss _ (law N per live) _
      _≤((coverNumber (radiusB b) X:ℝ)*C*b^8)*(b⁻¹)^(8+q+1):=mul_le_mul_of_nonneg_right (faces b one X) exp0
      _=(coverNumber (radiusB b) X:ℝ)*C*(b^8*(b⁻¹)^(8+q+1)):=by ring
      _≤(coverNumber (radiusB b) X:ℝ)*C*((ε/C)*g^q):=mul_le_mul_of_nonneg_left (spend N live per) (by positivity)
      _=_:=by field_simp
  · intro Y sub U accepted
    apply healthy Y _ low accepted
    intro z hz
    obtain ⟨i,hi,d⟩:=halo_spec.mp (mem_product.mp hz).1
    exact mem_product.mpr ⟨halo_spec.mpr ⟨i,sub hi,d⟩,mem_univ _⟩

end YM.Integration.WilsonReportingMolecularMaskRegion
