import YM.Integration.WilsonPositionProgramTrialPublicJointPivotComparison

/-! The normalized finite group measurement on each of the seven actual faces, at its native mesh clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotMesh
open Filter Finset Set MeasureTheory PowerSeries Maxwell Maxwell.Free XSpace XSpace.Normalize
open XSpace.Cirrus XSpace.Structure1 FVA2 FVA2.Scale FVA2.Arrival MS MS.Land
open RG17 Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open PhysicalNext.Repeat.Legato MS.Fleet MS.Book.Program FVA2.Register XSpace.Photo XSpace.Retirement
open WilsonPhysicalNormalizedSignedMenu (Row)
open WilsonPositionProgramTrialPublicJointPivotSeries (whole signed cash)
open scoped Topology BigOperators Classical Polynomial
variable {G : Gauge} (Z : WilsonPrescription G) {hG : G.Simple}
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {b : Bool} (H : Main.Match Z hG M σ b) (ν : ℝ)

include H ν in
theorem senses (d n k : ℕ) (p : Fin n → Sec G d) :
    Senses (conf n) (fun y => Rose.measureₓ Z.scheme Z.criterion d y k p)
      (fun x => Jury.fxt (Measure.start Z.scheme Z.criterion d) x k p) := by
  let data := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  intro x hx
  let z : Stage n := ⟨x,hx⟩
  change Tendsto _ (Gate x) (𝓝 (Jury.fxt (Measure.start Z.scheme Z.criterion d) z.val k p))
  rw [Jury.exactC,←Measure.together Z.scheme Z.criterion ν M σ hG data.Taylor data.still data.base]
  exact Measure.reaches Z.scheme Z.criterion ν M σ hG data.Taylor data.still data.base d n z k p

variable {ι : Type*}
private def Tracks (l : Filter ι) (a : ι → PowerSeries ℂ) (b : PowerSeries ℂ) : Prop :=
  ∀ k, Tendsto (fun i => coeff k (a i)) l (𝓝 (coeff k b))
private theorem add {l : Filter ι} {a b : ι → PowerSeries ℂ} {x y : PowerSeries ℂ}
    (A : Tracks l a x) (B : Tracks l b y) : Tracks l (fun i => a i+b i) (x+y) := by
  intro k
  simpa only [map_add] using (A k).add (B k)
private theorem sub {l : Filter ι} {a b : ι → PowerSeries ℂ} {x y : PowerSeries ℂ}
    (A : Tracks l a x) (B : Tracks l b y) : Tracks l (fun i => a i-b i) (x-y) := by
  intro k
  simpa only [map_sub] using (A k).sub (B k)
private theorem mul {l : Filter ι} {a b : ι → PowerSeries ℂ} {x y : PowerSeries ℂ}
    (A : Tracks l a x) (B : Tracks l b y) : Tracks l (fun i => a i*b i) (x*y) := by
  intro k
  simp only [PowerSeries.coeff_mul]
  exact tendsto_finsetSum _ (fun j _ => (A j.1).mul (B j.2))
private theorem two {l : Filter ι} {a : ι → PowerSeries ℂ} {x : PowerSeries ℂ}
    (A : Tracks l a x) : Tracks l (fun i => (2:ℂ) • a i) ((2:ℂ) • x) := by
  intro k
  simpa only [map_smul] using (A k).const_smul (2:ℂ)

include H ν in
theorem measured (d k : ℕ) (p : Fin 3 → Sec G d) :
    Senses (conf 3) (fun y => coeff k (signed (Rose.measureₓ Z.scheme Z.criterion d y) p))
      (fun x => coeff k (signed (Jury.fxt (Measure.start Z.scheme Z.criterion d) x) p)) := by
  intro x hx
  let m (s : Finset (Fin 3)) (y : Sample 3) := whole (Rose.measureₓ Z.scheme Z.criterion d y) (Rose.missing p s)
  let v (s : Finset (Fin 3)) := whole (Jury.fxt (Measure.start Z.scheme Z.criterion d) x) (Rose.missing p s)
  have h (s : Finset (Fin 3)) : Tracks (Gate x) (m s) (v s) := by
    intro j
    simpa only [m,v,WilsonPositionProgramTrialPublicJointPivotSeries.whole,coeff_mk] using senses Z M H ν d 3 j (Rose.missing p s) x hx
  exact (add (sub (h univ) (add (add (mul (h {0,1}) (h {2})) (mul (h {0,2}) (h {1})))
    (mul (h {1,2}) (h {0})))) (two (mul (mul (h {0}) (h {1})) (h {2})))) k

include H ν in
theorem original (d k : ℕ) (φ : Test 3) (p : Fin 3 → Sec G d) :
    Tendsto (fun f => Deposit f (fun y => coeff k (signed (Rose.measureₓ Z.scheme Z.criterion d y) p)) φ)
      Front (𝓝 (φ.applyTo (fun x => coeff k (signed (Jury.fxt (Measure.start Z.scheme Z.criterion d) x) p)))) := by
  exact sees_test (conf 3) φ _ (conf_open 3) (measured Z M H ν d k p) (fun _ _ _ => rfl) φ.tsupport_subset

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotMesh
