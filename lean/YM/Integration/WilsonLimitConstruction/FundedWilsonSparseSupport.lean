import YM.Integration.WilsonLimitConstruction.FundedWilsonCauchy

/-! Exact vacuum normalization and incidence counts for a sparse physical
field direction. All plaquettes retain their original four oriented links. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonSparseSupport

open Function Finset Set Lattice Exterior MS.Native
open FundedWilsonAtlas
open scoped Classical BigOperators
variable {G : Gauge} {n : Side}

def links (B : fieldDir G n 1) := Finset.univ.filter fun e => collect G B e ≠ 0

def faces (B : fieldDir G n 1) := Finset.univ.filter fun i => directions B i ≠ 0

def recover (e : Edge (Site n)) (q : PlaqAxes) (a : Axis) : Chart.Rout (Site n) :=
  (![(e.1 : Site n),e.1-Chart.drive n q.1.1,e.1-Chart.drive n q.1.2,e.1] a,q)

theorem ancestor (i : Chart.Rout (Site n)) (a : Axis) :
    recover (Chart.loadC (Chart.drive n) i a) i.2 a = i := by
  obtain ⟨x,q⟩ := i
  fin_cases a <;> simp [recover,Chart.loadC]

def turn (q : PlaqAxes) : Axis → Axis := ![q.1.1,q.1.2,q.1.1,q.1.2]

theorem edge_direction (i : Chart.Rout (Site n)) (a : Axis) :
    (Chart.loadC (Chart.drive n) i a).2 = turn i.2 a := by
  fin_cases a <;> rfl

abbrev Corners (a : Axis) := {u : PlaqAxes × Axis // turn u.1 u.2 = a}

theorem six (a : Axis) : Fintype.card (Corners a) = 6 := by
  fin_cases a <;> decide

theorem incidence (B : fieldDir G n 1) : (faces B).card ≤ 6*(links B).card := by
  have live (i : faces B) : ∃ a : Axis, collect G B (Chart.loadC (Chart.drive n) i.1 a) ≠ 0 := by
    by_contra! h
    have hz : directions B i.1 = 0 := funext h
    exact (Finset.mem_filter.mp i.2).2 hz
  choose a ha using live
  let f (i : faces B) : Σ e : links B, Corners e.1.2 :=
    ⟨⟨Chart.loadC (Chart.drive n) i.1 (a i),Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha i⟩⟩,
      ⟨(i.1.2,a i),(edge_direction i.1 (a i)).symm⟩⟩
  have hf : Injective f := by
    intro i j hij
    apply Subtype.ext
    have h := congrArg (fun w : Σ e : links B, Corners e.1.2 => recover w.1.1 w.2.1.1 w.2.1.2) hij
    simpa only [f,ancestor] using h
  have h := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_sigma,six,Nat.mul_comm] using h

def origin (G : Gauge) : ℝ := PertExtension.Chart.fee (XSpace.Bare.chart G) 0

theorem positive (G : Gauge) : 0 < origin G := by
  have R := XSpace.Bare.chart_ratio G
  exact (mul_pos R.scale (R.pos _ (Metric.mem_ball_self R.patch))).trans_le (le_max_left _ _)

theorem energy (B : fieldDir G n 1) (t : ℝ) :
    FundedWilsonGerm.action B t = FundedWilsonSupportGerm.physical B (faces B) t := by
  rw [FundedWilsonAtlas.physical]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hz : directions B i = 0 := by simpa [faces] using hi
  simp [hz,FundedWilsonPlaquette.price,Chart.gone,Chart.atCart]

theorem prior (B : fieldDir G n 1) (t : ℝ) :
    FundedWilsonMeasure.priorWeight B t / FundedWilsonMeasure.priorWeight B 0 =
      FundedWilsonCauchy.chartPrior B (links B) t / (origin G)^(links B).card := by
  let f (e : Edge (Site n)) := PertExtension.Chart.fee (XSpace.Bare.chart G) (t • collect G B e)
  have ho := (positive G).ne'
  have he : ∏ e, (f e / origin G) = ∏ e ∈ links B, (f e / origin G) := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro e _ he
    have hz : collect G B e = 0 := by simpa [links] using he
    have hzero : f e = origin G := by simp [f,hz,origin]
    rw [hzero,div_self ho]
  rw [Finset.prod_div_distrib,Finset.prod_div_distrib] at he
  simpa [FundedWilsonMeasure.priorWeight,PertExtension.Chart.jacobian,f,
    FundedWilsonCauchy.chartPrior,origin] using he

end YM.Integration.WilsonLimitConstruction.FundedWilsonSparseSupport
end
