import YM.Integration.WilsonPositionProgramTrialFittedIntake
import YM.Integration.WilsonPositionProgramTrialFittedTable

/-! The finite source conversion is evaluated before the moving measured vector. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialFittedBudget
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Power
open WilsonPositionProgramTrialFittedTable (head change)
open WilsonPositionProgramTrialFittedLens (ticket)
open WilsonPositionProgramTrialFittedIntake (convert)
open WilsonPositionProgramSubmittedCoordinates (submitted)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonPositionProgramNormalizedMaster (fee)
open scoped BigOperators Classical
variable {G:Gauge}{h e a:ℕ}{F:Frame G h}

def scalar (x:F.Coeff)(φ:ℂ →L[ℝ] ℝ)(j:Alma F):ℝ:=if rankS j.val.2=0 then φ (x j.val.1) else 0

theorem one (x:F.Coeff)(φ:ℂ →L[ℝ] ℝ)(j:Alma F):‖scalar x φ j‖≤‖φ‖*F.coeffSize x:=by
  have each:‖x j.val.1‖≤F.coeffSize x:=Finset.single_le_sum (f:=fun i=>‖x i‖) (fun _ _=>norm_nonneg _) (mem_univ j.val.1)
  unfold scalar;split
  · exact (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left each (norm_nonneg _))
  · rw [norm_zero];exact mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans each)

def capital (A:Levels G)(O:ChartRatio G)(Q:SealR G)(N m K e:ℕ):ℝ:=
  ∑j:Alma Q.F,∑t:Fin (e+1),∑b:Alma Q.F,‖change A O Q N m K t j b‖

theorem source (R:Run G)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
    (x:(i:Fin (a+1))→R.family.label (l i))(φ:Fin (a+1)→ℂ →L[ℝ] ℝ)(i:Fin (a+1)):
    submitted R l d fit x φ i=head (scalar (x i) (φ i)):=by
  funext j
  have together (P:Prop)[Decidable P](b:ℝ):(if P then C b else 0)=C (if P then b else 0):=by by_cases hp:P <;> simp [hp]
  exact together (rankS j.val.2=0) ((φ i) (x i j.val.1))

theorem original (R:Run G)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)(m K e:ℕ)(i:Fin (a+1)):
    let B:=capital R.family.path.levels R.metals.O (deck (G:=G) l d fit i) K m K e
    0≤B ∧ ∀(x:(i:Fin (a+1))→R.family.label (l i))(φ:Fin (a+1)→ℂ →L[ℝ] ℝ),
      fee (convert R l d fit K m K x φ) e i≤B*(‖φ i‖*(R.family.labels.level (l i)).coeffSize (x i)):=by
  intro B
  constructor
  · exact sum_nonneg (fun _ _=>sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _)
  intro x φ
  let Q:=deck (G:=G) l d fit i
  let A:=R.family.path.levels
  let O:=R.metals.O
  have field:=source R l d fit x φ i
  change (∑j:Alma Q.F,∑t:Fin (e+1),‖coeff t.val (ticket A O Q K m K (submitted R l d fit x φ i) j)‖)≤_
  rw [field]
  dsimp only [B,capital]
  rw [Finset.sum_mul]
  apply sum_le_sum;intro j _
  rw [Finset.sum_mul];apply sum_le_sum;intro t _
  rw [Finset.sum_mul]
  have formula:=congrFun (WilsonPositionProgramTrialFittedTable.native A O Q K m K t (scalar (x i) (φ i))) j
  change coeff t.val (ticket A O Q K m K (head (scalar (x i) (φ i))) j)=(WilsonPositionProgramTrialFittedTable.change A O Q K m K t *ᵥ scalar (x i) (φ i)) j at formula
  refine (le_of_eq (congrArg norm formula)).trans ?_
  change ‖∑b,change A O Q K m K t j b*scalar (x i) (φ i) b‖≤_
  apply (norm_sum_le _ _).trans
  apply sum_le_sum;intro b _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (one (x i) (φ i) b) (norm_nonneg _)

end YM.Integration.WilsonPositionProgramTrialFittedBudget
