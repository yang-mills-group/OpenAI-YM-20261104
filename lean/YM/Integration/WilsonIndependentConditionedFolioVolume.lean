import YM.Integration.WilsonIndependentConditionedFolioPupil
import YM.Integration.WilsonIndependentConditionedFolioReader
import YM.Integration.WilsonIndependentConditionedPlacementArm
import YM.Integration.WilsonIndependentMatchedCoverProfile

/-! The full affine Mer pupil on its actual named mesh and common translation. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioVolume
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels
open Laurent Bloch Metric FreeResolvent Work.F08 Precision Exterior Gauge XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open WilsonCoeffUV.Wheel.Flooring PertExtension RegulatorIR RegulatorIR.Budget
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedSectionIncome (leaf)
open WilsonIndependentMatchedOrdinarySeat (here received)
open WilsonIndependentSpoutOrdinaryPlate (sample)
open scoped Classical BigOperators
open WilsonIndependentMatchedTopReceipt (realDose)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningRoster (seat)
open WilsonIndependentMatchedOpeningPayment (affiled)

open WilsonIndependentNotebookConstantSeat (issue part)
open private seated_sum from YM.Integration.WilsonIndependentNotebookConstantSeat
open WilsonIndependentMatchedOpeningRoster (seat)
open WilsonIndependentMatchedOpeningFiled (planted)
open WilsonIndependentMatchedOpeningColumn (column)


open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentConditionedFolioReader (site)
open WilsonIndependentConditionedPlacementArm (stencil head)
open WilsonIndependentConditionedFolioPupil (atSite)
open WilsonIndependentConditionedBankRankedPorts (offered)
variable {G:Gauge}(R:Run G)(W:Initialize G){d D:ℕ}(fit:d<D)
local notation "F" => R.family.labels.level d
local notation "a" => R.family.S.a

private theorem part_smul (im:Bool)(c:ℝ)(z:ℂ):part im (c • z)=c*part im z:=by
  cases im <;> simp [part,Complex.real_smul]

private theorem issued (im:Bool)(c:ℝ)(z:(R.family.labels.level d).Coeff):c • issue F im z=issue F im (c • z):=by
  funext i
  simp only [Pi.smul_apply,issue]
  split_ifs
  · ext k
    simp only [part_smul,map_smul,PowerSeries.coeff_C]
    split_ifs <;> simp
  · exact smul_zero ..


theorem prefactors (f K m:ℕ)(im:Bool)(z:(R.family.labels.level d).Coeff):
    ((a f/a m)^d) • offered F false im (((a K/a f)^d) • z)=issue F im (((a K/a m)^d) • z):=by
  rw [offered,if_neg (by decide : ¬(false=true)),issued,smul_smul,←mul_pow]
  have eq:(a f/a m)*(a K/a f)=a K/a m:=by field_simp [(R.family.S.a_pos f).ne',(R.family.S.a_pos m).ne']
  rw [eq]

theorem site_at (j m f K N per:ℕ)(axes:R.family.label d≃ₗ[ℂ]R.family.label d)(source:R.family.label d)
    (turn:Signed)(hand:Bool)(phase:ℂ)(im:Bool)(φ:Rarity D)(y:ℝ)(o:CellR)(n:Cover):
    let x:=a K/a m
    site (stencil R axes source turn hand phase j m f K N per W false false im fit) φ x y o d n=
      x^4 • ∑i:(R.family.labels.level d).Index,(part im (head R d j K N per axes source turn hand phase i)*
        φ.ψ.val (Mer.position x y o n)) • column R W false fit (seat F i) n:=by
  classical
  intro x
  unfold stencil
  rw [prefactors]
  change drumB d x • planted R W false fit (wheelC x y n φ.ψ o)
    (issue F im (x^d • head R d j K N per axes source turn hand phase)) n=_
  rw [WilsonIndependentConditionedFolioIssue.original,Finset.smul_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply,part_smul,atSite,smul_smul]
  congr 1
  have hx:x≠0:=(div_pos (R.family.S.a_pos K) (R.family.S.a_pos m)).ne'
  dsimp [drumB]
  field_simp [hx]

end YM.Integration.WilsonIndependentConditionedFolioVolume
end
