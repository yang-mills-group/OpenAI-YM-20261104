import YM.Integration.WilsonMeasuredPublicEntranceGridDebit
import YM.Integration.WilsonMeasuredPublicEntranceSelected

/-! The signed upper-to-reporter grid award on the actual public columns with
their original measurement dates and their own pre-regulator quotas. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceFittedSlots
open Function Filter Lattice Wilson RG Source Labels
open Extraction Table Spec Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Work.G08
open Next.Foundations OPE.Therm Push.AbsoluteSums.Animals
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonAddressedRestartedColumn WilsonOriginalNullCorridor WilsonPositionProgramOriginalBlockedTrial
open WilsonMeasuredPublicEntranceGridDebit WilsonOriginalMicroscopicGuardedReporters
open WilsonPositionHomogeneousFrame WilsonThermometerUnitFilingFourSquare
open WilsonPositionProgramBlockedPublicExperiment WilsonAddressedPublicPool
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {ord : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family ord S) (l : Ultrafilter (ℕ×ℕ))

theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b)
    (wide : ∀j, 1 ≤ (R.family.path.levels.budget j).supportExponent)
    (quote : Poetry R.family.path.levels) (D target : ℕ) {η : ℝ} (pos : 0<η) :
    ∃ gate : ℕ, ∀ (I : Type) (d : I → Fin (D+1)) (v : (i : I) → S.Field (d i).val)
      (s M : I → ℝ) (L : (i : I) → WilsonMeasuredPublicSlots.Slot F l (d i).val (v i) (s i) (M i))
      (f n N p : ℕ) (_ : ∀i, gate ≤ (L i).j) (before : ∀i, (L i).j ≤ f)
      (live : f+n ≤ N) (_ : ∀i, (L i).j<N),
      ∃ A : (i : I) → R.family.label (d i).val ≃ₗ[ℂ] R.family.label (d i).val,
        (∀i x, Arrived R (d i).val (L i).j (f+n) N p target (by grind) live η (A i) x) ∧
        ∀i, let Y := (L i).arm.source (N,p)
            let B := R.family.S.a (L i).j ^ (d i).val*(M i*GapsContact.Ascent.cost F (d i).val (s i) (v i))
            let w := (A i).symm (fitted R (d i).val (L i).j N p Y)
            (R.family.labels.level (d i).val).coeffSize w ≤ stretch R η (L i).j (f+n)*(2*B) ∧
              ∀ o, settled R (d i).val (L i).j f n N p live (A i) Y o := by
  classical
  obtain ⟨a,sale⟩ := WilsonMeasuredPublicEntranceGridDebit.original R simple shop wide quote D target pos
  have opened : ∀ (d : Fin (D+1)), ∀ᶠ j : ℕ in atTop, ∀p, Opened R.family d.val j p :=
    fun d => open_late R.family simple d.val
  obtain ⟨b,ready⟩ := eventually_atTop.mp (Filter.eventually_all.mpr opened)
  refine ⟨max a b,?_⟩
  intro I d v s M L f n N p late before live deep
  obtain ⟨A,rows,got⟩ := sale I d (fun i => (L i).j) f n N p
    (fun i => (le_max_left ..).trans (late i)) before live deep
  refine ⟨A,rows,?_⟩
  intro i
  let Y := (L i).arm.source (N,p)
  let x := (R.family.factory (d i).val N p).terminal.symm Y
  let B := R.family.S.a (L i).j^(d i).val*(M i*GapsContact.Ascent.cost F (d i).val (s i) (v i))
  let q := (R.family.factory (d i).val N p).entries (L i).j x
  have priced : (R.family.labels.level (d i).val).coeffSize q.x ≤ B := by
    simpa only [Next.UVStress.quota, Y, x, q, B] using (L i).numerical N p (deep i)
  have pagePrice := (size_gap (d i).val N p (L i).j R.makes
    (ready (L i).j ((le_max_right ..).trans (late i)) (d i) p) (deep i).le x).1
  refine ⟨((rows i (fitted R (d i).val (L i).j N p Y)).1).trans ?_,?_⟩
  · refine mul_le_mul_of_nonneg_left (pagePrice.trans (mul_le_mul_of_nonneg_left priced zero_le_two)) ?_
    unfold WilsonOriginalMicroscopicGuardedReporters.stretch
    positivity
  · exact got i ((L i).owns.trans (before i)) Y

end YM.Integration.WilsonMeasuredPublicEntranceFittedSlots
end
