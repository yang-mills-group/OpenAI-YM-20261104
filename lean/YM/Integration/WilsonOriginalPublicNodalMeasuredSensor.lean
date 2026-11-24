import YM.Integration.WilsonOriginalPublicNodalPlainSensor
import YM.Integration.WilsonPositionProgramTrialFittedInversion

/-! All calibrated physical coefficients share the original scalar test at their distinct visits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalMeasuredSensor
open Finset Function Lattice RG Wilson Precision Source Labels PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonPositionProgramSubmittedCoordinates (plain submitted)
open WilsonPositionProgramTrialFittedBudget (scalar)
open WilsonPositionProgramInversionMaterial (Axes axis dose)
open WilsonOriginalPublicNodalPlainSensor (sensor)
open scoped Classical BigOperators
variable {G:Gauge}{a:ℕ}(R:Run G)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)

theorem wheel (d:ℕ)(ρ y:ℝ)(z:Cover)(F:Phrase d)(c:CellR):
    sensor d (wheelC ρ y z F c)=F.val (address ρ y c z zeroC):=by
  change claim d ⟨⟨0,Nat.zero_lt_succ _⟩,Fin.elim0⟩ zeroC (page _ (sonal ρ y c z F))=_
  rw [nib _ (Nat.zero_le _) Fin.elim0]
  simp [crease,iteratedFDeriv_zero_apply,sonal]

abbrev Picks:Type:=(i:Fin (a+1))→(R.family.labels.level (l i)).Index

def embed (b:Picks R l):Axes R l:=fun i=>plain (R.family.labels.level (l i)) (b i)

theorem keep {M:Type*}[AddCommMonoid M](f:Axes R l→M)
    (zero:∀v:Axes R l,(∃i,rankS (v i).val.2≠0)→f v=0):
    ∑v,f v=∑b:Picks R l,f (embed R l b):=by
  let live:=univ.filter (fun v:Axes R l=>∀i,rankS (v i).val.2=0)
  calc
    ∑v,f v=∑v∈live,f v:=by
      apply (sum_subset (filter_subset ..) ?_).symm
      intro v _ hv
      apply zero
      simpa [live] using hv
    _=∑b:Picks R l,f (embed R l b):=by
      apply sum_bij' (fun v _=>axis R l v) (fun b _=>embed R l b)
      · simp
      · intro b _
        simp [live,embed,WilsonPositionProgramSubmittedCoordinates.plain,rankS]
      · intro v hv
        funext i
        exact (WilsonOriginalPublicNodalPlainSensor.only _ (v i) ((mem_filter.mp hv).2 i)).symm
      · intro b _
        rfl
      · intro v hv
        apply congrArg f
        funext i
        exact WilsonOriginalPublicNodalPlainSensor.only _ (v i) ((mem_filter.mp hv).2 i)

def weights (B:(i:Fin (a+1))→Volume (d i)):ℂ:=((∏i,sensor (d i) (B i):ℝ):ℂ)
def coefficients (x:(i:Fin (a+1))→R.family.label (l i))(φ:Fin (a+1)→ℂ →L[ℝ] ℝ)(b:Picks R l):ℂ:=
  ∏i,((φ i) (x i (b i)):ℂ)

theorem original (x:(i:Fin (a+1))→R.family.label (l i))(φ:Fin (a+1)→ℂ →L[ℝ] ℝ)
    (B:(i:Fin (a+1))→Volume (d i))(X:Picks R l→PowerSeries ℂ):
    ∑v:Axes R l,dose R l (submitted R l d fit x φ) d fit B v*X (axis R l v)=
      PowerSeries.C (weights d B)*(∑b:Picks R l,PowerSeries.C (coefficients R l x φ b)*X b):=by
  refine (keep R l _ ?_).trans ?_
  · intro v hv
    obtain ⟨i,dead⟩:=hv
    have gone:WilsonPositionProgramTrialVisitDose.amount R l d fit x φ B v=0:=by
      unfold WilsonPositionProgramTrialVisitDose.amount
      apply prod_eq_zero (mem_univ i)
      simp [scalar,dead]
    rw [WilsonPositionProgramTrialVisitDose.original,gone,map_zero,zero_mul]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro b _
  rw [WilsonPositionProgramTrialVisitDose.original,←mul_assoc,←map_mul]
  apply congrArg (·*X b)
  apply congrArg PowerSeries.C
  unfold WilsonPositionProgramTrialVisitDose.amount weights coefficients
  push_cast
  rw [←Finset.prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  change ((scalar (x i) (φ i) (plain _ (b i)):ℝ):ℂ) *
    ((jewelBloom (fit i) (plain _ (b i)) (B i):ℝ):ℂ)=_
  rw [WilsonOriginalPublicNodalPlainSensor.chosen]
  simp [scalar,WilsonPositionProgramSubmittedCoordinates.plain,rankS,mul_comm]

end YM.Integration.WilsonOriginalPublicNodalMeasuredSensor
end
