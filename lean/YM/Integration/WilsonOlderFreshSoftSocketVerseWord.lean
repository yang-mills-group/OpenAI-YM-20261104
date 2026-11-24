import YM.Integration.WilsonOlderFreshSoftSocketVerseProduct
import YM.Integration.WilsonIndependentMatchedOpeningProfile

/-! Uniform income of a complete measured section and its compensated change at the published sites. -/
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketVerseWord
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels
open Laurent Bloch Metric FreeResolvent Work.F08 Precision Exterior Gauge XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Wheel.Flooring
open PertExtension RegulatorIR RegulatorIR.Budget
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedOpeningFiled (planted)
open WilsonOlderFreshSoftSocketVerseProduct (Paid)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G)
variable {D d:ℕ}
local notation "F" => R.family.labels.level d

def filed (s:Bool)(w:d<D)(c:Verse F)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ):Era G ℝ:=
  word (Shrine (plate (sectionAt R W s d) w) c) φ x y o l

theorem linear (s:Bool)(w:d<D)(c b:Verse F)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ)(hx:0<x):
    filed R W s w (c-b) φ x y o l=filed R W s w c φ x y o l-filed R W s w b φ x y o l:=by
  have visits (v:Verse F):filed R W s w v φ x y o l=
      ∑z∈VisitsT φ x y o,drumB l x • planted R W s w (wheelC x y z φ.ψ o) v z:=by
    unfold filed word
    rw [pupil_eye l _ φ x y o hx]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  rw [visits,visits,visits,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [←smul_sub,WilsonOlderFreshSoftSocketVerseSeed.linear]

theorem original (s:Bool)(w:d<D)(e:ℕ):∃A:Alma F→ℝ, (∀a,0≤A a) ∧
    ∀(_S:Patch)(φ:Rarity D)(B x y:ℝ)(o:CellR)(l:ℕ),0<x→x≤1→Amplitude φ B→
    ∀(c:Verse F),Paid d e (filed R W s w c φ x y o l)
      (WilsonIndependentMatchedCoverProfile.charge φ 0 l x y (charge e c A) B):=by
  obtain ⟨A,hA,bank⟩:=WilsonIndependentMatchedFiledIncome.named R W s d w le_rfl e 0
  refine ⟨A,hA,?_⟩
  intro S φ B x y o l hx hx' test c
  have inc:=WilsonIndependentMatchedCoverProfile.submitted _ (bank c).1 _
    (fun j hj r=>(bank c).2.2 j r hj) φ x y o l S hx hx' test
  exact WilsonOlderFreshSoftSocketVerseProduct.collect inc

end YM.Integration.WilsonOlderFreshSoftSocketVerseWord
