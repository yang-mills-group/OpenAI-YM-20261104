import YM.Integration.WilsonPositionOriginalPathMarginals
import YM.Integration.PhysicalWilsonHotIntegral

/-! A true local threshold failure on either end of a physical two-date
read is paid on the common chronological Wilson path. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQFailedPath
open Lattice Wilson RG Function Set MeasureTheory Filter OPE.Therm
open Push.AbsoluteSums.Animals PhysicalNext.Repeat.Legato Pert.Asymptotics QLocalPhysicalPathKernel
open scoped Classical Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)(Y:Poetry R.family.path.levels)
local notation "κ" k:max=>R.family.path.levels.clock.forcedAllowance k
abbrev ConfigurationPath (per:ℕ) := (k:ℕ) → Config G (R.family.side k per)
local notation "ledger" N:max p:max=>path R.family R.makes N p

include simple Y

/-- The original flag allowance at the measured regulator pays any fixed
division and remaining coupling order against a correlated path observable. -/
theorem original (q P:ℕ) :
    ∀ᶠ m:ℕ in atTop,∀N per,m≤N→∀X:Support (R.family.side m per),
      let failed:=SelectedCofactorAnchoredRegister.hot (G:=G) (R.family.path.rep N per m).p.threshold X
      ∀(H:ConfigurationPath R per→ℂ)(b:ℝ),0≤b→(∀ω,‖H ω‖≤b)→
      ‖∫ ω in (fun t:ConfigurationPath R per=>t m) ⁻¹' failed,H ω ∂(ledger N per)‖ ≤
        b*(X.card * ballCost 2 * Fintype.card PlaqAxes:ℕ)*(κ m)^q*regulatorRun R.family N per m^P:=by
  filter_upwards [PhysicalWilsonHotIntegral.sites R simple Y (ρ:=1) zero_lt_one (q+1),
    OriginalForcedFlat.allowance R simple P zero_lt_one] with m fee flat N per top X
  intro E H b hb envelope
  have law:=WilsonPositionOriginalPathMarginals.observed R.family R.makes (p:=per) top
  have he:MeasurableSet E:=SelectedCofactorAnchoredRegister.measurable _ _
  have same:(ledger N per).real ((fun t:ConfigurationPath R per=>t m) ⁻¹' E)=(scene R.family.path N per m).real E:=
    congrArg ENNReal.toReal (law.measure_preimage he.nullMeasurableSet)
  have elected: (scene R.family.path N per m).real E≤(X.card*ballCost 2*Fintype.card PlaqAxes:ℕ)*(κ m)^(q+1):=by
    simpa [E] using fee N top per X
  have money:κ m≤regulatorRun R.family N per m^P:=by simpa using flat N per top
  have positive:0≤κ m:=Real.exp_nonneg _
  calc
    _ ≤ b*(ledger N per).real ((fun t:ConfigurationPath R per=>t m) ⁻¹' E):=by
      simpa [Measure.real,Measure.restrict_apply MeasurableSet.univ] using
        (norm_integral_le_of_norm_le_const (μ:=(ledger N per).restrict ((fun t:ConfigurationPath R per=>t m) ⁻¹' E))
          (Eventually.of_forall envelope))
    _ ≤ b*((X.card*ballCost 2*Fintype.card PlaqAxes:ℕ)*(κ m)^(q+1)):=by
      rw [same];exact mul_le_mul_of_nonneg_left elected hb
    _ = (b*(X.card*ballCost 2*Fintype.card PlaqAxes:ℕ)*(κ m)^q)*(κ m):=by rw [pow_succ];ring
    _ ≤ _:=mul_le_mul_of_nonneg_left money (by positivity)

/-- Both measured field differences, their proper terms and all intervening
hard partners are evaluated on one sample of the actual Wilson path. -/
theorem square (q P:ℕ) :
    ∀ᶠ m:ℕ in atTop,∀N per,m≤N→∀X:Support (R.family.side m per),
      let failed:=SelectedCofactorAnchoredRegister.hot (G:=G) (R.family.path.rep N per m).p.threshold X
      ∀i j (Q₁ Q₂:Config G (R.family.side i per)→ℂ)(L₁ L₂:Config G (R.family.side j per)→ℂ)
        (a b c d:ℝ),0≤a→0≤b→0≤c→0≤d→
        (∀U,‖Q₁ U‖≤a)→(∀U,‖Q₂ U‖≤b)→(∀V,‖L₁ V‖≤c)→(∀V,‖L₂ V‖≤d)→
      ‖∫ ω in (fun t:ConfigurationPath R per=>t m) ⁻¹' failed,(Q₁ (ω i)-L₁ (ω j))*(Q₂ (ω i)-L₂ (ω j))
          ∂(ledger N per)‖ ≤ (a+c)*(b+d)*(X.card*ballCost 2*Fintype.card PlaqAxes:ℕ)*(κ m)^q*
            regulatorRun R.family N per m^P:=by
  filter_upwards [original R simple Y q P] with m paid N per top X
  intro E i j Q₁ Q₂ L₁ L₂ a b c d ha hb hc hd p₁ p₂ h₁ h₂
  apply paid N per top X _ ((a+c)*(b+d)) (by positivity)
  intro ω
  rw [norm_mul]
  exact mul_le_mul ((norm_sub_le ..).trans (add_le_add (p₁ _) (h₁ _)))
    ((norm_sub_le ..).trans (add_le_add (p₂ _) (h₂ _))) (norm_nonneg _) (add_nonneg ha hc)

end YM.Integration.WilsonPositionOriginalDressedQFailedPath
