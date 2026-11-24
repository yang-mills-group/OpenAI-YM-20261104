import YM.Integration.ActualWilsonJoinedCofactor
import YM.Integration.WilsonPhysicalMarkedDefectRegularProjection
import YM.Integration.ActualWilsonExteriorPrice
import YM.Integration.SelectedCofactorExteriorGas

/-! The remaining actual compulsory marked gas grouped by its charged row.
The reserve of the row pays the flags in its own support, and the signed
deleted gas supplies the flags outside that support. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportRootedPartners
open Function Filter Finset Lattice Wilson RG Source Labels Extraction Spec
open Extra.Histories Extra.Multi MergeProof OPE PhysicalNext.Repeat.Legato
open Next.Rank Next.Rank.Spindle Planned.Forced SectorNext.Vacuum
open ActualWilsonPacketSplit ActualWilsonJoinedCofactor
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G}

private theorem remaining (C : Family G) (N p b : ℕ) (i : ℕ) (U : Config G (C.side b p)) :
    let A := C.path.rep N p b
    let Y := (A.activities.forced i).support
    let I := (A.activities.forced i).inventory
    dressed A i U=if Y∩flags A.p.threshold U=I then (outsideGas A.activities A.p Y U:ℂ) else 0 := by
  dsimp only
  rw [dressed_eq]
  exact SelectedCofactorExteriorGas.gas _ _ _ (C.path.rep N p b |>.activities.forced i |>.inventory_sup) U

/-- A single charged rooted address sees the signed exterior only at the
exact actual flag inventory in its punched support. -/
theorem identity {d b N p : ℕ} (cut : b≤N)
    (Z : Coefficient (R.family.labels.level d) (R.family.side b p)) {w : ℝ}
    (form : Z.Format 0 R.family.params (R.family.path.rep N p b))
    (bill : Z.remBound 0 (R.family.path.rep N p b) (Real.sqrt (R.family.path.levels.clock.forcedAllowance b)) w)
    (U : Config G (R.family.side b p)) :
    let A := R.family.path.rep N p b
    (∑' J,Z.marked A J U) =
     ∑' i, Z.forced i U*(if (A.activities.forced i).support∩flags A.p.threshold U=(A.activities.forced i).inventory
       then (outsideGas A.activities A.p (A.activities.forced i).support U:ℂ) else 0) ∧
     ∀i,Z.forced i U≠0 → 0∈(A.activities.forced i).support ∧ (A.activities.forced i).eligible A.p.threshold U := by
  dsimp only
  constructor
  · exact (dress_eq (R.makes.wilson.represents N p b cut).good (rem_dominated bill) U).trans
      (tsum_congr fun i=>congrArg (fun z : ℂ=>Z.forced i U*z) (remaining R.family N p b i U))
  intro i nz
  exact ⟨form.carried i (fun hz=>nz (congrFun hz U)),form.forcing i U nz⟩

private theorem allocation {n : Side} (p : BudgetPoint) (F Y : Support n) :
    Real.exp (-flagRate p*((F\Y).card:ℝ))≤Real.exp (-flagRate p*(F.card:ℝ))*Real.exp (p.supportExponent*coverNumber p.B Y) := by
  have inc : F ⊆ (F\Y)∪Y := by
    intro v hv
    by_cases hy : v∈Y
    · exact mem_union_right _ hy
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hv,hy⟩)
  have count : (F.card:ℝ)≤((F\Y).card:ℝ)+(Y.card:ℝ) := by exact_mod_cast (card_le_card inc).trans (card_union_le ..)
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left count (flagRate_pos p).le,inventory_pay p (Subset.refl Y)]

/-- The complete initially marked numerator (including every other allowed
signed activity) has a geometric bill in the total actual flag count.
There is no inverse density, extensive factor or uncharged sum of labels
in this numerator estimate. -/
theorem physical {d b N p : ℕ} (cut : b≤N)
    (Z : Coefficient (R.family.labels.level d) (R.family.side b p)) {w : ℝ}
    (form : Z.Format 0 R.family.params (R.family.path.rep N p b))
    (bill : Z.remBound 0 (R.family.path.rep N p b) (Real.sqrt (R.family.path.levels.clock.forcedAllowance b)) w)
    (U : Config G (R.family.side b p)) :
    let A := R.family.path.rep N p b
    let κ := Real.sqrt (R.family.path.levels.clock.forcedAllowance b)
    ‖∑' J,Z.marked A J U‖ ≤ (if flags A.p.threshold U=∅ then 0 else
        Real.exp (-flagRate A.p*(flags A.p.threshold U).card)*κ*w) := by
  let C := R.family
  let A := C.path.rep N p b
  let F := flags A.p.threshold U
  let β := C.path.levels.clock.forcedAllowance b
  let κ := Real.sqrt β
  let B := Real.exp (-flagRate A.p*(F.card:ℝ))
  let Y := fun i=>(A.activities.forced i).support
  let r := fun i=>dressed A i U
  have pos : 0≤B := (Real.exp_pos _).le
  have low : β≤1 := Real.sqrt_le_one.mp (divisor_le C b)
  have lawful := (R.makes.wilson.represents N p b cut).good
  have sum : (∑' J,Z.marked A J U)=∑' i,Z.forced i U*r i := dress_eq lawful (rem_dominated bill) U
  change ‖∑' J,Z.marked A J U‖ ≤ if F=∅ then 0 else B*κ*w
  by_cases empty : F=∅
  · rw [if_pos empty]
    have zero := WilsonPhysicalMarkedDefect.RegularProjection.clear Z 0 A R.family.params form U empty
    simp_rw [zero]
    simp only [tsum_zero,norm_zero,le_refl]
  rw [if_neg empty,sum]
  obtain ⟨a,t,ha,_,debit,hκ,_,e,he,size⟩ := bill
  have charged i : ‖Z.forced i U *r i‖≤ B*A.p.mass (Y i) (e i) := by
    have nonneg := (size i).1
    have raw : ‖r i‖≤Real.exp (-flagRate A.p*((F\Y i).card:ℝ)) := by
      rw [show r i = _ from remaining C N p b i U]
      split_ifs
      · rw [Complex.norm_real]
        have hb := (ActualWilsonExteriorPrice.covered A.activities lawful.labels.boundK low (Y i) U).2
        exact hb.trans (mul_le_of_le_one_left (Real.exp_pos _).le (by split <;> first | exact le_rfl | exact low))
      · rw [norm_zero];exact (Real.exp_pos _).le
    rw [norm_mul]
    calc
      _ ≤ e i*(B*Real.exp (A.p.supportExponent*coverNumber A.p.B (Y i))) :=
        mul_le_mul ((size i).2 U) (raw.trans (allocation A.p F (Y i))) (norm_nonneg _) nonneg
      _ = _ := by unfold BudgetPoint.mass;ring
  have base := he.2.1.mul_left B
  have finite := base.of_nonneg_of_le (fun i=>norm_nonneg (Z.forced i U*r i)) charged
  calc
    _ ≤ ∑' i,‖Z.forced i U*r i‖ := norm_tsum_le_tsum_norm finite
    _ ≤ ∑' i,B*A.p.mass (Y i) (e i) := finite.tsum_le_tsum charged base
    _ = B*∑' i,A.p.mass (Y i) (e i) := tsum_mul_left
    _ ≤ B*(κ*t) := mul_le_mul_of_nonneg_left he.2.2 pos
    _ ≤ B*κ*w := by
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left ha).trans debit) (mul_nonneg pos hκ.le)
end YM.Integration.WilsonReportRootedPartners
end
