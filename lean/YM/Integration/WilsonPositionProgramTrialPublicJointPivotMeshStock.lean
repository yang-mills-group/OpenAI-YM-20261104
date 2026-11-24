import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMesh

/-! Uniform compact convergence of the signed finite measurements on bounded physical directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshStock
open Function Filter Set Finset MeasureTheory PowerSeries Maxwell Maxwell.Free XSpace XSpace.Normalize
open XSpace.Cirrus XSpace.Structure1 XSpace.Photo FVA2 FVA2.Scale FVA2.Arrival MS MS.Land
open RG17 Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open PhysicalNext.Repeat.Legato MS.Fleet MS.Book.Program FVA2.Register XSpace.Retirement
open WilsonPhysicalNormalizedSignedMenu (Row)
open WilsonPhysicalPositionTargetRows (rows)
open WilsonPositionProgramTrialPublicJointPivotWeights (salary paid)
open WilsonPositionProgramTrialPublicJointPivotSeries (signed)
open WilsonPositionProgramTrialPublicJointPivotMesh (measured)
open private add smul from YM.Integration.WilsonPositionProgramTrialPublicJointPivotSeries
open scoped Classical Topology BigOperators Polynomial
variable {G : Gauge} {d : ℕ}

def mark (A : ℕ → Row G d 3) (k : ℕ) : Row G d 3 :=
  MultilinearMap.mk' (fun p => coeff k (signed A p))
    (fun p i x y => by rw [add,map_add])
    (fun p i z x => by rw [smul,map_smul])

variable (Z : WilsonPrescription G) {hG : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG M σ dial) (ν : ℝ)

def finite (d : ℕ) (mesh : Mesh) (φ : Test 3) (k : ℕ) : Row G d 3 :=
  (mesh.spacing:ℂ)^(4*3) • ∑ y : mesh.Tuple (n:=3), mesh.smear (mesh.back y) φ •
    mark (Rose.measureₓ Z.scheme Z.criterion d ⟨mesh,mesh.back y,0⟩) k

theorem tested (d : ℕ) (mesh : Mesh) (φ : Test 3) (k : ℕ) (p : Fin 3 → Sec G d) :
    finite Z d mesh φ k p =
      Deposit mesh (fun y => coeff k (signed (Rose.measureₓ Z.scheme Z.criterion d y) p)) φ := by
  simp only [finite,_root_.smul_apply,_root_.sum_apply,smul_eq_mul,Deposit]
  rfl

def limit (d : ℕ) (φ : Test 3) (k : ℕ) : Row G d 3 :=
  WilsonPositionProgramTrialPublicJointPivotTarget.contracts φ
    (fun x=>mark (Jury.fxt (Measure.start Z.scheme Z.criterion d) x) k)
    (fun v=>φ.smearing (measured Z M H ν d k v).priced)

theorem compact (d k : ℕ) (p : Fin 3 → Sec G d) (K : Set (Points 3)) (hc : IsCompact K)
    (hk : K ⊆ conf 3) (ε : ℝ) (hp : 0 < ε) : ∀ᶠ mesh in Front, ∀ (φ : Test 3),
    tsupport φ ⊆ K → ∀ B : ℝ, TestBudget.Bound φ B →
      ‖finite Z d mesh φ k p-limit Z M H ν d φ k p‖ ≤ B*ε := by
  simp_rw [tested]
  exact graduate _ _ (conf_open 3) (measured Z M H ν d k p).priced hk hc (measured Z M H ν d k p)
    (fun _ _ _=>rfl) ε hp

theorem original (d q : ℕ) (K : Set (Points 3)) (hc : IsCompact K) (hk : K ⊆ conf 3)
    (ε : ℝ) (hp : 0<ε) : ∀ᶠ mesh in Front, ∀ (k : Fin (q+1)) (φ : Test 3),
    tsupport φ ⊆ K → ∀ B : ℝ, TestBudget.Bound φ B → ∀ p : Fin 3 → Sec G d,
      ‖finite Z d mesh φ k p-limit Z M H ν d φ k p‖ ≤ (∏ j, salary (p j))*(B*ε) := by
  have dates (k : Fin (q+1)) (b : Fin 3 → Pin G d) :=
    compact Z M H ν d k (fun j=>Module.finBasis ℝ (Sec G d) (b j)) K hc hk ε hp
  filter_upwards [Filter.eventually_all.mpr (fun k=>Filter.eventually_all.mpr (dates k))] with mesh window
  intro k φ supported B bounded p
  exact paid (finite Z d mesh φ k) (limit Z M H ν d φ k) p
    (mul_nonneg (TestBudget.bound_nonneg φ bounded) hp.le) (fun b=>window k b φ supported B bounded)

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshStock
