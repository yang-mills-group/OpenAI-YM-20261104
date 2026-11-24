import YM.Integration.WilsonThermometerUnitFilingFourSquare
import YM.Integration.WilsonPositionThermometerCapStation

/-! An uncorrected weak column and the sharp pool insertion representing it
on the same physical extraction. All labels and salaries refer to the filed
station itself. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFourPoolArms
open Filter Table Extraction Spec Climb OPE Next.UVStress
open GapsContact GapsContact.Stamps GapsContact.Ascent Trace.Terrace MergeProof.East
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingFourPool
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {l : Ultrafilter (ℕ×ℕ)} {F : Final C f S}

theorem sharp {r B : ℝ} {j m d : ℕ} (card : BookedArm F l r j m d B) :
    ∃ (V : ∀ i, Vane C i) (i : ℕ) (cap : d ≤ i) (T : Spin.change S d),
      (V i).k = j ∧ purchaseWidth (V i) = m ∧ ∀ v : S.Field d,
      ∃ y : Arm C S (l:Filter _) d v,
        (∀ z, y.source z = (V i).wheel.atCut z ⟨d,Nat.lt_succ_of_le cap⟩ (T.symm v)) ∧
        (∀ N p, j < N → quota C d j N p (y.source (N,p)) ≤ C.S.a j^d*B*cost F d r v) ∧
        ∀ᶠ z : ℕ×ℕ in f.fuse, Cards.PaidAt C.S z.1 z.2 m (C.beta z.1 z.2)
          (B*cost F d r v) (C.O z.1 z.2 (y.source z) 0) := by
  obtain ⟨V,i,cap,T,Z,atJ,atM,filed,tends,bills⟩ := card.station
  refine ⟨V,i,cap,T,atJ,atM,fun v => ?_⟩
  let a := T.symm v
  have obs : Continuous (fun k : (Cells.standard C).Field d →L[ℂ] C.label d => k a) :=
    continuous_id.clm_apply continuous_const
  have cut : Tendsto (fun z => (V i).wheel.atCut z ⟨d,Nat.lt_succ_of_le cap⟩ a)
      (l:Filter _) (𝓝 (Z a)) := by
    simpa only [Function.comp_def, heightV, dif_pos cap] using obs.continuousAt.tendsto.comp tends
  let y : Arm C S (l:Filter _) d v :=
    ⟨_, Z a, cut, (filed a).trans (T.apply_symm_apply v)⟩
  refine ⟨y,fun _ => rfl,?_⟩
  simpa [y,a] using bills a

open WilsonPositionThermometerCapStation

/-- The weak source is inserted with the original supplied vector at every
cutoff, so its public class follows from its actual limiting lift. -/
def weak {c : ℕ} (A : Group C c)
    (lands : Tendsto A.station.wheel.atCut (l:Filter _) (𝓝 A.lift))
    (j : Fin (c+1)) (p : (Bel C.book).Field j) :
    Arm C S (l:Filter _) j (S.project j (A.lift (index A j) p)) where
  source z := A.station.wheel.atCut z (index A j) p
  label := A.lift (index A j) p
  approaches := by
    have ev : Continuous (fun T : Lifts C A.horizon => T (index A j) p) :=
      (continuous_apply (index A j)).clm_apply continuous_const
    exact ev.continuousAt.tendsto.comp lands
  represents := rfl

end YM.Integration.WilsonThermometerUnitFilingFourPoolArms
