import YM.Integration.WilsonMatrixTicketLanesNativePrices
import YM.Integration.WilsonMatrixTicketLanesDescentWords
import YM.FVA2.CommonSources

/-! Identity of the finite MS article's upper registered sources and the actual Wilson insertions. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesArticleSource
open Function Lattice Gauge RG Tree Wilson Precision PhysicalNext.Repeat.Legato
open FVA2 FVA2.CityHistory FVA2.Both FVA2.Both.Passage RGComparison.Core16 RGComparison.Core16.Spool
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.InversionTop
open WilsonMatrixTicketLanesNativePrices WilsonMatrixTicketLanesDescentWords
open scoped BigOperators Classical
variable {G : Gauge} (R : Run G) {n : Side}

/-- A filed article atom carries the complete nonlinear compact Wilson field before Taylor expansion. -/
theorem atom (d : ℕ) (i : (R.family.labels.level d).Index) (x : Site n) (U : Config G n) :
    ((Track.loadStamp (warehouse R) x i).stencil U : ℂ) =
      Light (investment (R.makes.sections d) (CoefficientBridge.run_valuation R d) i) n x U := by
  classical
  let c : R.family.label d := Pi.single i 1
  have fixed : star c = c := by
    funext l
    by_cases h : l=i
    · subst l; simp [c]
    · simp [c,Pi.single_eq_of_ne h]
  let V := expandAt x U
  change (((R.family.localSection d).evaluate c V).re : ℂ) = (R.family.localSection d).evaluate c V
  apply Complex.conj_eq_iff_re.mp
  calc
    _ = (R.family.localSection d).evaluate (star c) V := ((R.makes.sections d).ordinary_real c V).symm
    _ = _ := congrArg (fun z : R.family.label d=>(R.family.localSection d).evaluate z V) fixed

variable {I : Type} [DecidableEq I] (s : Finset I) (d : I→ℕ)
    (i : ∀a,(R.family.labels.level (d a)).Index) (x : I→Site n)

omit [DecidableEq I] in
/-- The equality holds for every occupied subset, including repeated field labels and sites. -/
theorem shafts : Stamp.shafts (Track.Seals (warehouse R) x d i) s =
    look false ∘ tally (lamps R (fun a : s=>d a.1) (fun a=>i a.1)) (fun a=>x a.1) := by
  funext U
  have fields : (((∏a∈s,(Track.loadStamp (warehouse R) (x a) (i a)).stencil U):ℝ):ℂ) =
      tally (lamps R (fun a:s=>d a.1) (fun a=>i a.1)) (fun a=>x a.1) U := by
    rw [Complex.ofReal_prod,← Finset.prod_attach,show s.attach=Finset.univ from rfl]
    exact Finset.prod_congr rfl fun a _=>atom R (d a) (i a) (x a) U
  simp only [Stamp.shafts,Finset.prod_apply]
  exact (Complex.ofReal_re _).symm.trans (congrArg Complex.re fields)

/-- The upper ticket actually purchased by `CapReady.Article` has this precise original germ. -/
theorem original : PowerSeries.X ^ power (lamps R (fun a:s=>d a.1) (fun a=>i a.1)) *
    Passage.seats (warehouse R) d i s x =
      exPay (look false ∘ tally (lamps R (fun a : s=>d a.1) (fun a=>i a.1)) (fun a=>x a.1)) := by
  have graded : Stamp.degrees (Track.Seals (warehouse R) x d i) s =
      power (lamps R (fun a:s=>d a.1) (fun a=>i a.1)) := by
    unfold Stamp.degrees power
    rw [←Finset.sum_attach,show s.attach=Finset.univ from rfl]
    rfl
  rw [←graded,Passage.scripture,shafts R s d i x]

end YM.Integration.WilsonMatrixTicketLanesArticleSource
