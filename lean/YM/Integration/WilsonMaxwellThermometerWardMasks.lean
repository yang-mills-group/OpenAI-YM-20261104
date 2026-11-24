import YM.Integration.WilsonMaxwellThermometerWardCompanion
import YM.Integration.ActualRunCurvaturePackets

/-! The two original grade-four fields at their own periodic sites form the
four real companions of the earned upper equation. Their product remains on
the finite inversion law in each occupied face and keeps its true radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardMasks
open Function Filter Set Finset MeasureTheory Lattice Labels Source Wilson PertExtension PertExtension.Orb
open PertExtension.Orb.SlotEvaluation PertExtension.Series Chart Series.Radial Series.Tested
open PhysicalNext.Repeat.Legato WilsonMaxwellThermometerWardPupil
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} {n:Side} (R:Run G)
variable (c:Fin 2→(R.family.labels.level 4).Coeff) (L:Fin 2→(ℂ→L[ℝ]ℝ)) (z:Fin 2→Site n)

def companion (S:Finset (Fin 2)) (U:Config G n):ℝ :=
  ∏ j ∈ S, WilsonMaxwellThermometerWardPupil.selected (R.family.localSection 4) (c j) (L j) (z j) (next (F:=R.family.labels.level 4)) U

def rooms : Set (Site n) := ⋃j:Fin 2,↑((R.family.localSection 4).footprint (z j))

theorem admitted (S:Finset (Fin 2)):
    PreTest (companion R c L z S) ∧
    RadialOrder (2*S.card) (fun x:Dir G n=>companion R c L z S (representative x)) ∧
    LocalOn (rooms R z) (companion R c L z S) :=by
  let f (j:Fin 2):Config G n→ℝ := selected (R.family.localSection 4) (c j) (L j) (z j) (next (F:=R.family.labels.level 4))
  have ok (j):PreTest (f j):=WilsonMaxwellThermometerWardCoefficient.admitted (R.family.localSection 4) (c j) (L j) (z j)
    (R.makes.sections 4) (ActualRunGradedKernels.section_valuation R 4) _
  have eq (U:Config G n):companion R c L z S U=∏ j∈S,f j U:=rfl
  have hc:Continuous (companion R c L z S):= continuous_finsetProd _ (fun j _=>(ok j).continuous)
  refine ⟨⟨?_,⟨hc.comp continuous_links,?_⟩,hc⟩,?_,?_⟩
  · intro u hu U
    apply Finset.prod_congr rfl
    intro j _
    exact (ok j).gauge u hu U
  · change ContDiffAt ℝ ∞ (fun x:Dir G n=>∏ j∈S,f j (representative x)) 0
    exact contDiffAt_prod (fun j _=>(ok j).curved.germ)
  · intro u
    have hj (j): RadialOrder 2 (fun y:Dir G n=>f j (representative y)):=by
      apply WilsonMaxwellThermometerWardPupil.radial (R.family.localSection 4) (c j) (L j) (z j)
        (R.makes.sections 4) (ActualRunGradedKernels.section_valuation R 4)
      intro i hi
      exact ((mem_filter.mp hi).2 : ((R.family.labels.level 4).grades i).2=2).ge
    have joined:=bill_product S (fun _=>2) (fun (j:Fin 2) (t:ℝ)=>f j (representative (t • u))) (fun j _=>hj j u)
    have applyf : (∏ j∈S,fun t:ℝ=>f j (representative (t • u))) =
        fun t:ℝ=>companion R c L z S (representative (t • u)):=by
      funext t
      simp only [Finset.prod_apply,eq]
    rw [applyf] at joined
    simpa [Nat.mul_comm] using joined
  · intro U X hu
    apply Finset.prod_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    apply congrArg (fun a:ℝ=>L j (c j i)*a)
    change ((R.family.localSection 4).places (Pi.single i 1) (z j) U).re=((R.family.localSection 4).places (Pi.single i 1) (z j) X).re
    apply congrArg Complex.re
    apply (R.family.localSection 4).placed_local (z j) _ U X
    intro e a b
    exact hu e (Set.mem_iUnion.mpr ⟨j,a⟩) (Set.mem_iUnion.mpr ⟨j,b⟩)

end YM.Integration.WilsonMaxwellThermometerWardMasks
