import YM.Integration.WilsonMatrixTicketLanesVacuumSale
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskEarned

/-! Test the signed physical mask change of the actual previously filed action
against both enrolled operators. Each marked position keeps its own original
upper coordinate and its own chosen earlier vacuum origin. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesVacuumSpring
open Filter Function Set MeasureTheory Lattice Wilson RG OPE.Therm
open IterationFour IterationFour.Vacuum WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Pert.Asymptotics
open WilsonInvariantActionPriorHearing WilsonMatrixTicketLanesVacuumPanel OriginalMarkedRunAction
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {k N per:ℕ}
local notation "upper" => Config G (R.family.side (k+1) per)
local notation "lower" => Config G (R.family.side k per)
local notation "Sites" => Fin 2→Site (R.family.side N per)

/-- Change from the unmasked signed vacuum score to its physical masked score. -/
def difference (Z:SeriesA G) (σ C:ℝ) (s:ℕ) (x:Site (R.family.side (k+1) per)) (U:upper):ℝ:=
  let g:=regulatorRun R.family N per (k+1)
  springAt R N per (k+1) s Z g x U-maskedSpringAt R N per (k+1) s Z σ C g x U

def Paid (live:k+1≤N) (birth:R.family.ref 4≤k+1) (marks:Fin 2→R.family.label 4)
    (φ:Test 2) (χ:ℂ→L[ℝ]ℝ) (Z:SeriesA G) (σ C:ℝ) (s:ℕ) (goal:ℝ):Prop:=
  ∀o:Sites→Site (R.family.side (k+1) per),∃w:Sites→ readings (lower×upper),
    (∀x V U,(w x).val (V,U)=difference R (N:=N) Z σ C s (o x) U) ∧
    ∀kind:Kind,|signed R kind live birth marks φ χ w|≤goal

theorem at_date (live:k+1≤N) (birth:R.family.ref 4≤k+1) (marks:Fin 2→R.family.label 4)
    (φ:Test 2) (χ:ℂ→L[ℝ]ℝ) (Z:SeriesA G) (σ C:ℝ) (s q:ℕ) (δ goal:ℝ)
    (return_:SpringMaskEstimate R k N Z σ C s q δ)
    (bounded:∀x,Envelope (difference R (N:=N) (per:=per) (k:=k) Z σ C s x))
    (sale:∀w:Sites→ readings (lower×upper),
      (∀x,joint R live (WilsonMatrixTicketLanesVacuumIncome.absolute (w x))≤δ*(regulatorRun R.family N per (k+1))^q)→
      ∀kind:Kind,|signed R kind live birth marks φ χ w|≤goal):
    Paid R (per:=per) live birth marks φ χ Z σ C s goal:=by
  intro o
  let w (x:Sites):readings (lower×upper):=⟨fun a=>difference R (N:=N) Z σ C s (o x) a.2,
    (bounded (o x)).meas.comp measurable_snd,(bounded (o x)).cost.choose,
    fun a=>(bounded (o x)).cost.choose_spec a.2⟩
  refine ⟨w,fun _ _ _=>rfl,sale w fun x=>?_⟩
  rw [WilsonMatrixTicketLanesVacuumIncome.fineMass R live (w x) (difference R (N:=N) Z σ C s (o x)) (fun _ _=>rfl)]
  have h:=(return_ per (o x) (k+1) (le_refl _)).2.2.1
  rw [actualTransport_base R.family R.makes live] at h
  simpa only [difference,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm] using h

end YM.Integration.WilsonMatrixTicketLanesVacuumSpring
