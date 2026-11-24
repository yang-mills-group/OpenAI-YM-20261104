import YM.RGComparison.Core16.Astage.Axle
import YM.Integration.WilsonMatrixTicketLanesNativePrices
import YM.Integration.WilsonCoherentTerminalFrame

/-! The actual near-mesh inverse column and its normalized reported group observable. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedPivot
open Filter FVA2 MS.Local.Physical Wilson Lattice Pert.Asymptotics
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Astage
open PhysicalNext.Repeat.Legato WilsonMatrixTicketLanesNativePrices
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {d : ℕ}

/-- Re-register the literal central field of this cutoff label at the chosen reporting date. -/
def center (m N p : ℕ) (x : R.family.label d) : R.family.label d :=
  (R.family.factory d m p).terminal
    (((R.family.factory d N p).entries m ((R.family.factory d N p).terminal.symm x)).x)

private theorem normalize (m N p : ℕ) (x v : R.family.label d)
    (h : (R.family.labels.level d).scaled (R.family.path.levels.clock.threshold m)⁻¹
        (((R.family.factory d N p).entries m ((R.family.factory d N p).terminal.symm x)).x) =
      ((R.family.S.a m ^ d : ℝ) : ℂ) • (R.family.labels.level d).scaled (regulatorRun R.family N p m)⁻¹ v) :
    WilsonCoherentTerminalFrame.coordinates R m p (center R m N p x) =
      (R.family.labels.level d).scaled (regulatorRun R.family N p m)⁻¹ v := by
  have ha : ((R.family.S.a m : ℂ)^d) ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos m).ne')
  unfold WilsonCoherentTerminalFrame.coordinates center
  rw [LinearEquiv.symm_apply_apply, map_smul, h, Complex.ofReal_pow, smul_smul,
    inv_mul_cancel₀ ha, one_smul]

/-- The individual angular coefficients have the running coupling from this very upper cutoff. -/
theorem coordinates {m N : ℕ} (p : ℕ) (hm : R.family.ref d ≤ m) (hN : m ≤ N) (v : R.family.label d) :
    WilsonCoherentTerminalFrame.coordinates R m p (center R m N p (Axle.root R.makes d m N p v)) =
      (R.family.labels.level d).scaled (regulatorRun R.family N p m)⁻¹ v :=
  normalize R m N p _ v (Axle.atCoupling R.makes d hm hN v)

/-- Each upper configuration and its inverse-transported center give this actual nonlinear field at m. -/
theorem measured {m N : ℕ} (p : ℕ) (hm : R.family.ref d ≤ m) (hN : m ≤ N) (v : R.family.label d)
    (o : Site (R.family.side m p)) (U : Config G (R.family.side m p)) :
    R.family.O m p (center R m N p (Axle.root R.makes d m N p v)) o U =
      ∑ j, ((regulatorRun R.family N p m)⁻¹ ^ ((R.family.labels.level d).grades j).2 : ℝ) *
        v j * Light (WilsonCoherentTerminalFrame.lamp R d j) (R.family.side m p) o U := by
  rw [WilsonCoherentTerminalFrame.row, coordinates R p hm hN]
  simp only [Labels.Frame.scaled_apply]

/-- Real or complex signed combinations of prescribed graded columns retain all original section prices. -/
theorem portfolio {m N : ℕ} (p : ℕ) (hm : R.family.ref d ≤ m) (hN : m ≤ N)
    (B : Deck G) {I : Type} [Fintype I] (grade : I → ℕ)
    (pick : ∀ i, B.BIndex (d:ℤ) (grade i)) (c : I → ℂ)
    (o : Site (R.family.side m p)) (U : Config G (R.family.side m p)) :
    let v := ∑ i, c i • (warehouse R).qfits B d (grade i) (pick i)
    R.family.O m p (center R m N p (Axle.root R.makes d m N p v)) o U =
      ∑ j, ((regulatorRun R.family N p m)⁻¹ ^ ((R.family.labels.level d).grades j).2 : ℝ) *
        (∑ i, c i * FVAAlt2.Shop.valueP B (R.family.localSection d) (R.makes.sections d)
          (CoefficientBridge.run_valuation R d) (pick i) j) *
        Light (WilsonCoherentTerminalFrame.lamp R d j) (R.family.side m p) o U := by
  intro v
  rw [measured R p hm hN]
  apply Finset.sum_congr rfl
  intro j _
  have eq (i : I) := ((warehouse R).price_cast B (pick i) j).symm.trans
    (WilsonMatrixTicketLanesNativePrices.original R B d (grade i) (pick i) j)
  simp only [v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eq]

/-- A single true operator limit is chosen for every source, before any grade or period. -/
theorem filed {f : Extraction.Order} (U : Ultrafilter (ℕ × ℕ)) (hu : (U : Filter (ℕ × ℕ)) ≤ f.fuse) :
    ∃ A : Axle.TransferLimit R.family R.makes U, ∀ d m, R.family.ref d ≤ m →
      ∀ v : R.family.label d,
        Tendsto (fun z : ℕ × ℕ => Axle.root R.makes d m z.1 z.2 v) U (𝓝 (A.fieldMap d m v)) ∧
        ∀ N p, m ≤ N → Next.UVStress.quota R.family d m N p (Axle.root R.makes d m N p v) ≤
          R.family.S.a m ^ d * (Axle.cost R.family d m * ‖v‖) := by
  obtain ⟨A⟩ := Axle.option R.makes U hu
  refine ⟨A, fun d m hm v => ⟨?_, fun N p hN => Axle.charge R.makes d hm hN v⟩⟩
  exact (ContinuousLinearMap.apply ℂ (R.family.label d) v).continuous.continuousAt.tendsto.comp
    (A.lim d m hm)

end YM.Integration.WilsonMatrixTicketLanesReportedPivot
