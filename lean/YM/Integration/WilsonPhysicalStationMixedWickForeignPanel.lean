import YM.Integration.WilsonPhysicalStationMixedWickPivots
import YM.Integration.WilsonPhysicalStationMixedWickRespondents
import YM.Integration.WilsonPhysicalStationMixedWickPortfolio
import YM.Integration.WilsonPhysicalStationMixedNamedProbe
import YM.Integration.WilsonPhysicalStationMixedForeign
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerFrame

/-! Exact Maxwell orthogonality of the full registered mixed-rank ballots,
before scaling either of the original measured Gram coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickForeignPanel
open Filter Finset Function Lattice RG Wilson Labels Source Cells Extraction Table Maxwell Maxwell.Free
open PhysicalNext.Repeat.Legato MS MS.Menus MS.Land MS.Theater XSpace.Structure1
open Local.Physical Further.CorrectedLift
open WilsonPhysicalStationThermalBasisOffice (rank)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationMixedWickTest (reference)
open WilsonPhysicalStationMixedWickPivots (reflected)
open WilsonPhysicalStationMixedWickRespondents (independent reported)
open WilsonPhysicalStationMixedNamedProbe (coefficient)
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonMeasuredPublicEntranceNativeLowerFrame (panel)
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G)
local notation "C₀" => standard R.family

theorem ballot {l r:ℕ}(x:R.family.label l)(q:ℕ)(hom:∀i,x i≠0→ rank R.family l i=q)
    (b:(R.family.labels.level r).Index)(s:Signed)(side:Fin 2)(y:Points 2)(foreign:q≠rank R.family r b):
    reference R.family x (probe R.family b s side) y=0:=by
  let h:=max l r
  let dl:Fin (h+1):=⟨l,Nat.lt_succ_of_le (le_max_left _ _)⟩
  let dr:Fin (h+1):=⟨r,Nat.lt_succ_of_le (le_max_right _ _)⟩
  let stub:R.family.label l→ₗ[ℂ](C₀).Field l:=(C₀).project l
  let read:R.family.label l→ₗ[ℂ]ℂ:=(WilsonPhysicalStationMixedWickPortfolio.allowance R dl dr y
    (probe R.family b s side)).comp stub
  have actual (v:R.family.label l):read v=reference R.family v (probe R.family b s side) y:=
    WilsonPhysicalStationMixedWickPortfolio.evaluated R dl dr y _ v
  have split:(∑i,x i • (Pi.single i 1:R.family.label l))=x:=by
    funext i
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  rw [←actual,←split,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul,smul_eq_mul,actual]
  by_cases live:x i=0
  · rw [live,zero_mul]
  · rw [WilsonPhysicalStationMixedForeign.original R.family i b s side y (by
      change rank R.family l i≠rank R.family r b
      rwa [hom i live]),mul_zero]

theorem original (B:Deck G)(e:ℕ)(a:Axis)(y:Points 2)(i j:Glyph B e)(foreign:i.2.1.val≠j.2.1.val):
    panel R B e a y i j=0:=by
  let w:=reflected R B a i
  have realRead:independent R y w (named R B e j)=panel R B e a y i j:=by
    rw [reported]
    unfold reference WilsonPhysicalStationMixedWickTest.fields
    rw [Further.CorrectedLift.ladder_reads]
    rfl
  rw [←realRead,WilsonPhysicalStationMixedNamedProbe.original R B e j,map_sum]
  apply Finset.sum_eq_zero
  intro b _
  rw [map_smul,smul_eq_mul,reported]
  by_cases live:coefficient R B e j b=0
  · rw [live,zero_mul]
  · have rankB:rank R.family e b=j.2.1.val:=congrArg Prod.snd (WilsonPhysicalStationMixedNamedProbe.grades R B e j b live)
    rw [ballot R _ _ (WilsonPhysicalStationMixedWickPivots.original R B a i) b 1 0 y (by rwa [rankB]),mul_zero]

end YM.Integration.WilsonPhysicalStationMixedWickForeignPanel
end
