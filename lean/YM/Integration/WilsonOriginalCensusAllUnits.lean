import YM.Integration.WilsonOriginalCensusFixedUnit
import YM.Integration.WilsonOriginalCensusFixedRestriction
import YM.Integration.WilsonOriginalCensusPositiveSites

/-! Withdraw exactly the zero-grade entries and use the preselected positive census. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusAllUnits
open Function Finset Lattice RG Wilson Source Labels
open MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums
open WilsonReceivedCanonicalVerseBasis
open PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open WilsonThermometerDeclaredSeeds WilsonReceivedFixedDigitCanonical WilsonReceivedFixedDigitHistory
open WilsonOriginalCensusUnitVerse (observed)
open WilsonOriginalCensusUnitLamp (fee)
open WilsonOriginalCensusPositiveSites (Group names part mapped)
open scoped BigOperators Classical

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(k:I→ℕ){h:I→ℕ}
    (κ:(j:I)→Knob (h j))(pt:I→Chamber)(q:(j:I)→Choice R k j)(simple:G.Simple)
    (N K i:ℕ)(called:i≤K)(live:K≤N)(digit:Digits R.family.path.levels I)(o:I → Cover)(A:Case h)

include simple called live

theorem withdraw (u s:Finset I)(inside:u⊆s)(units:∀j∈u,k j=0 ∧ q j=.inl ()):
    let Y:=fixed R k κ pt N K i digit q o
    observed Y A s=(∏j∈u,fee κ pt A j) • observed Y A (s\u):=by
  intro Y
  induction u using Finset.induction_on generalizing s with
  | empty=>simp
  | @insert v u fresh ih=>
    have hv:=inside (mem_insert_self v u)
    have invest:=units v (mem_insert_self v u)
    have rest:u⊆s.erase v:=by
      intro j hj
      exact mem_erase.mpr ⟨fun same=>fresh (same ▸ hj),inside (mem_insert_of_mem hj)⟩
    have remaining:s\insert v u=(s.erase v)\u:=by
      ext j
      simp only [mem_sdiff,mem_insert,mem_erase]
      tauto
    rw [remaining,prod_insert fresh,mul_smul]
    exact (WilsonOriginalCensusFixedUnit.original R k κ pt q simple v invest.1 invest.2 N K i called live digit o A s hv).trans
      (congrArg (fun w:Era G ℝ=>fee κ pt A v • w) (ih (s.erase v) rest (fun j hj=>units j (mem_insert_of_mem hj))))

theorem original (s:(Replicum.Bud I).Mode)(paid:∀j∈s.val,k j=0 → q j=.inl ()):
    let e:=names k
    let Y:=fixed R k κ pt N K i digit q o
    let Z:=fixed R (k ∘ e) (h:=h ∘ e) (fun l=>κ (e l)) (pt ∘ e) N K i (fun d=>digit d ∘ e) (fun l=>q (e l)) (o ∘ e)
    observed Y A s.val=(∏j∈s.val.filter (fun j=>k j=0),fee κ pt A j) • observed Z (fun j=>A (e j)) (part k s).val:=by
  intro e Y Z
  let u:=s.val.filter (fun j=>k j=0)
  have aboard:s.val\u=(part k s).val.map e:=by
    rw [mapped]
    ext j
    simp [u]
    tauto
  have factor:=withdraw R k κ pt q simple N K i called live digit o A u s.val (filter_subset _ _) (by
    intro j hj
    exact ⟨(mem_filter.mp hj).2,paid j (mem_filter.mp hj).1 (mem_filter.mp hj).2⟩)
  change observed Y A s.val=(∏j∈u,fee κ pt A j) • observed Y A (s.val\u) at factor
  rw [aboard] at factor
  exact factor.trans (congrArg (fun w:Era G ℝ=>(∏j∈u,fee κ pt A j) • w)
    (WilsonOriginalCensusFixedRestriction.original R k κ pt q e simple N K i called live digit o A (part k s).val))

end YM.Integration.WilsonOriginalCensusAllUnits
