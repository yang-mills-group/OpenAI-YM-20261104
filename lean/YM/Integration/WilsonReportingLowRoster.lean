import YM.Integration.WilsonReportingPrescribedUnit

/-! All original finite-chart fields below engineering grade four have
one coefficient. Their actual returned palettes share a single power
before cutoff and period for each finite heterogeneous roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingLowRoster
open Function Filter Lattice Wilson RG Source Labels RG12 RG05Readout Address
open WilsonReportingPrescribedUnit WilsonReportingUnitOrbit
open scoped Classical Topology BigOperators
variable {G:Gauge} {C:Family G}

theorem whole (simple:G.Simple) {d:ℕ} (low:d<4) (x:C.label d) : scalar C d x=x := by
  obtain ⟨z,rfl⟩:=RG12.unit_spans simple C d 0 low x
  unfold scalar unitVec
  simp only [smul_smul,Pi.smul_apply,smul_eq_mul,Frame.e0,Pi.single_eq_same,mul_one]

theorem roster (h:C.Makes) (simple:G.Simple) {ι:Type} [Fintype ι] (d e:ι→ℕ) (low:∀i,d i<4) :
    ∃ H:ℕ, ∀ᶠ m:ℕ in atTop, ∀i:ι, ∀ {N p b:ℕ} {D:Rail C} {B:ℕ→ℕ→ℝ}
    {V:Sight C (d i) p} {U:Emblems C (d i)}, Spine D B h b p (d i) N V U →
    b ≤ m → m ≤ N → ∀ x:C.label (d i), mass C (d i) x ≤ (C.path.levels.clock.hatBeta m)^(e i) →
    let y:=WilsonReportingUpperChartPrice.returned h (primary (d i)) x U m N p
    size y ≤ (C.path.levels.clock.hatBeta m)^H ∧
      Many.point U y m N=chunk (primary (d i)) ((C.factory (d i) N p).terminal.symm
        (atK C h (d i) m (N,p) x)) := by
  let H:=Finset.univ.sup e+1
  refine ⟨H,?_⟩
  filter_upwards [Filter.eventually_all.mpr (fun i:ι=>affordable h simple (d i) (e i))] with m tickets
  intro i N p b D B V U spine start live x price y
  have original:=tickets i spine start live x price
  rw [whole simple (low i) x] at original
  have exponents:e i+1 ≤ H:=Nat.add_le_add_right (Finset.le_sup (f:=e) (Finset.mem_univ i)) 1
  refine ⟨original.trans (pow_le_pow_right₀ (C.path.levels.fits.delayed m).le exponents),?_⟩
  dsimp only [y]
  rw [Many.weave_fine live,WilsonReportingUpperChartPrice.returned,Many.point,
    dif_neg (Nat.not_lt.mpr live),LinearEquiv.apply_symm_apply]
  rfl

end YM.Integration.WilsonReportingLowRoster
