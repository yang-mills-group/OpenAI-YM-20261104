import YM.Integration.WilsonOriginalCensusFundedUnits
import YM.Integration.WilsonReceivedCanonicalVersePortfolio

/-! Removing unoccupied grade-zero coordinates from the elected inverse-matrix portfolio. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterUnitWallet
open Function Finset Lattice RG Wilson Source Labels
open MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums
open WilsonReceivedCanonicalVerseBasis
open PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds
open WilsonIndependentCollarOrbitalBasisPayment WilsonIndependentCollarPaidWindingPanel
open WilsonOriginalCensusPositiveSites (names part mapped)
open WilsonOriginalCensusUnitDose (enrolled)
open WilsonOriginalCensusPositiveDose (reduced)
open scoped BigOperators Classical

variable {G:Gauge}{n:ℕ}(R:Run G)(k:Fin n→ℕ)(N per K:ℕ)(x:(j:Fin n)→R.family.label (k j))

private theorem table (s:Finset (Fin n))(a:Choices R k s):
    WilsonReceivedCanonicalVersePortfolio.weight R k N per K x s a=∏j∈s,dose R k N per K x j (enrolled R k s a j):=by
  unfold WilsonReceivedCanonicalVersePortfolio.weight
  rw [←Finset.prod_coe_sort s]
  apply prod_congr rfl
  intro j _
  simp only [enrolled,dif_pos j.property]

theorem supported (s:(Replicum.Bud (Fin n)).Mode)(a:Choices R k s.val)
    (unit:∀j:s.val,k j=0 → a j=.inl ()):
    WilsonReceivedCanonicalVersePortfolio.weight R k N per K x s.val a=(∏j∈s.val.filter (fun j=>k j=0),x j 0)*
      WilsonReceivedCanonicalVersePortfolio.weight R (k ∘ names k) N per K (fun j=>x (names k j)) (part k s).val (reduced R k s a):=by
  let w:=fun j=>dose R k N per K x j (enrolled R k s.val a j)
  have partition: (∏j∈s.val.filter (fun j=>k j=0),w j)*(∏j∈s.val.filter (fun j=>k j≠0),w j)=∏j∈s.val,w j:=
    prod_filter_mul_prod_filter_not s.val (fun j=>k j=0) w
  rw [table,←partition,←mapped]
  apply congrArg₂ (·*·)
  · apply prod_congr rfl
    intro j hj
    obtain ⟨here,zero⟩:=mem_filter.mp hj
    have chosen:=unit ⟨j,here⟩ zero
    simp [w,enrolled,here,chosen,dose,WilsonThermometerDeclaredSeeds.entry,WilsonOriginalStarSceneWords.scalar]
  · rw [prod_map,table]
    apply prod_congr rfl
    intro j hj
    rw [enrolled,dif_pos hj]
    change w (names k j)=dose R (k ∘ names k) N per K (fun j=>x (names k j)) j (enrolled R k s.val a (names k j))
    dsimp only [w]
    cases enrolled R k s.val a (names k j) with
    | inl u=>rfl
    | inr b=>rfl


theorem absent (simple:G.Simple)(s:Finset (Fin n))(a:Choices R k s)
    (off:¬∀j:s,k j=0 → a j=.inl ()):
    WilsonReceivedCanonicalVersePortfolio.weight R k N per K x s a=0:=by
  classical
  simp only [not_forall] at off
  obtain ⟨j,zero,nonunit⟩:=off
  cases arm:a j with
  | inl u=>cases u;exact (nonunit arm).elim
  | inr c=>
    unfold WilsonReceivedCanonicalVersePortfolio.weight
    apply prod_eq_zero (mem_univ j)
    rw [arm]
    exact WilsonOriginalCensusSocketUnit.socket R simple k N per K x _ (by omega) c

end YM.Integration.WilsonReceivedChronologicalRosterUnitWallet
