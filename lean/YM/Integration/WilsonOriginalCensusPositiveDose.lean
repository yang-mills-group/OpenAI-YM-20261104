import YM.Integration.WilsonOriginalCensusUnitDose
import YM.Integration.WilsonOriginalCensusPositiveSites

/-! The restored signed basis price factors with the original unrenormalized unit coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusPositiveDose
open Function Finset Lattice RG Wilson Source Labels
open MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums
open WilsonReceivedCanonicalVerseBasis
open PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds
open WilsonIndependentCollarOrbitalBasisPayment WilsonIndependentCollarPaidWindingPanel
open WilsonOriginalCensusPositiveSites (names part mapped)
open WilsonOriginalCensusUnitDose (enrolled)
open scoped BigOperators Classical

variable {G:Gauge}{n:ℕ}(R:Run G)(k:Fin n→ℕ)(N per K m:ℕ)(x:(j:Fin n)→R.family.label (k j))

def cost (j:Fin n)(a:Choice R k j):ℂ:=
  dose R k N per K x j a*Complex.ofReal ((Pert.Asymptotics.regulatorRun R.family N per K)⁻¹^(pole R k (WilsonThermometerDeclaredSeeds.entry R k j a))*
    (R.family.path.levels.S.a m/R.family.path.levels.S.a K)^(k j))

theorem table (s:Finset (Fin n))(a:Choices R k s):
    signed R k N per K m x s a=∏j∈s,cost R k N per K m x j (enrolled R k s a j):=by
  unfold signed
  rw [←Finset.prod_coe_sort s]
  apply prod_congr rfl
  intro j _
  simp only [enrolled,dif_pos j.property,cost]

def reduced (s:(Replicum.Bud (Fin n)).Mode)(a:Choices R k s.val):Choices R (k ∘ names k) (part k s).val:=
  fun j=>enrolled R k s.val a (names k j)

theorem original (s:(Replicum.Bud (Fin n)).Mode)(a:Choices R k s.val)
    (unit:∀j:s.val,k j=0 → a j=.inl ()):
    signed R k N per K m x s.val a=(∏j∈s.val.filter (fun j=>k j=0),x j 0)*
      signed R (k ∘ names k) N per K m (fun j=>x (names k j)) (part k s).val (reduced R k s a):=by
  let w:=fun j=>cost R k N per K m x j (enrolled R k s.val a j)
  have partition: (∏j∈s.val.filter (fun j=>k j=0),w j)*(∏j∈s.val.filter (fun j=>k j≠0),w j)=∏j∈s.val,w j:=
    prod_filter_mul_prod_filter_not s.val (fun j=>k j=0) w
  rw [table,←partition,←mapped]
  apply congrArg₂ (·*·)
  · apply prod_congr rfl
    intro j hj
    obtain ⟨here,zero⟩:=mem_filter.mp hj
    have chosen:=unit ⟨j,here⟩ zero
    simp [w,cost,enrolled,here,chosen,dose,WilsonThermometerDeclaredSeeds.entry,pole,WilsonOriginalStarSceneWords.scalar,zero]
  · rw [prod_map,table]
    apply prod_congr rfl
    intro j hj
    rw [enrolled,dif_pos hj]
    change w (names k j)=cost R (k ∘ names k) N per K m (fun j=>x (names k j)) j (enrolled R k s.val a (names k j))
    dsimp only [w]
    cases enrolled R k s.val a (names k j) with
    | inl u=>rfl
    | inr b=>rfl

end YM.Integration.WilsonOriginalCensusPositiveDose
