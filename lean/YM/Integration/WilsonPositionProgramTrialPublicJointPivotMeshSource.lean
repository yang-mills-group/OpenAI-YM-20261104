import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshSlice
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotInherited

/-! A single inherited basis is used by the signed physical row and every determining test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshSource
open Function Set Filter Finset Lattice RG Wilson Source Extraction MeasureTheory PowerSeries
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open PhysicalNext.Repeat.Legato RG17 FullVolume Spec Table OPE OPE.Orbits Climb PhysMS Trace.Pilot
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPhysicalNormalizedSignedMenu (Row positioned docket retag)
open WilsonPhysicalPositionTargetRows (rows)
open WilsonPositionPrescribedScreen (hierarchy)
open WilsonPositionProgramTrialPublicJointPivotNorm (moved)
open WilsonPositionProgramTrialPublicJointPivotMeshGauge (funded)
open WilsonPositionProgramTrialPublicJointPivotMeshCells (panel)
open WilsonPositionProgramTrialPublicJointPivotMeshRate (Dates)
open WilsonPositionProgramTrialPublicJointPivotEvidence (old)
open WilsonMaxwellThermometerPublicStation (aperture)
open WilsonMaxwellThermometerSignedWallet (board)
open scoped Classical BigOperators Topology
variable {G : Gauge} {R : Run G} {o : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family o S) (J : ℝ→PhysMS.tower S) (Z : WilsonPrescription G) {hG : G.Simple}
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
    {dial : Bool} (H : Main.Match Z hG M σ dial) (ν : ℝ)

open WilsonPositionProgramTrialPublicJointPivotMeshSlice (film)
open WilsonPositionProgramTrialPublicJointPivotWeights (salary)
variable {d n : ℕ}

def decoded (V : Pin G d→Sec G d) : Sec G d→ₗ[ℝ]Sec G d :=
  (Module.finBasis ℝ (Sec G d)).constr ℝ V

def Declared (V : Pin G d→Sec G d) (T : Change G d) : Prop :=
  (stand T).restrictScalars ℝ=decoded V

theorem index {V : Pin G d→Sec G d} {T : Change G d} (source : Declared V T) (i : Pin G d) :
    stand T (Module.finBasis ℝ (Sec G d) i)=V i := by
  have eq := LinearMap.congr_fun source (Module.finBasis ℝ (Sec G d) i)
  exact eq.trans ((Module.finBasis ℝ (Sec G d)).constr_basis ℝ _ i)

theorem elected (V : Pin G d→Sec G d) (A : FieldEnd G d)
    (source : A.restrictScalars ℝ=decoded V) (ward : A-1∈Change G d) : ∃! T : Change G d, Declared V T := by
  let T : Change G d := ⟨A-1,ward⟩
  have same : stand T=A := by change 1+(A-1)=A; abel
  have own : Declared V T := by rw [Declared,same]; exact source
  refine ⟨T,own,?_⟩
  intro U other
  apply Subtype.ext
  ext1 x
  have eq := LinearMap.congr_fun (other.trans own.symm) x
  change x+U.val x=x+T.val x at eq
  exact add_left_cancel eq

def Signed (V : Pin G d→Sec G d) (A W : Row G d n) (B e : ℝ) : Prop :=
  ∃ P : Row G d n,
    (∀ b : Fin n→Pin G d, (∏ j,salary (V (b j)))≤B) ∧
    (∀ b,‖rows A b - P (V ∘ b)‖≤e) ∧
    (∀ b,‖rows P b-rows W b‖≤e)

theorem returned {T : Change G d} {V : Pin G d→Sec G d} (same : Declared V T) {A W : Row G d n}
    {B e : ℝ} (bp : 0≤B) (ep : 0≤e) (paid : Signed V A W B e) : ‖rows A-rows (moved T W)‖≤(1+B)*e := by
  obtain ⟨P,bounded,actual,reading⟩ := paid
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) ep)).2
  intro b
  have placed : rows (moved T W) b=W (V∘b) := by
    change W (fun j=>stand T (Module.finBasis ℝ (Sec G d) (b j)))=W _
    simp_rw [index same]
    rfl
  change ‖rows A b-rows (moved T W) b‖≤_
  rw [placed]
  calc
    ‖rows A b-W (V∘b)‖ ≤ ‖rows A b-P (V∘b)‖+‖P (V∘b)-W (V∘b)‖ := by
      simpa only [dist_eq_norm] using dist_triangle (rows A b) (P (V∘b)) (W (V∘b))
    _ ≤ e+B*e := add_le_add (actual b) ((WilsonPositionProgramTrialPublicJointPivotWeights.paid
      P W (V∘b) ep reading).trans (mul_le_mul_of_nonneg_right (bounded b) ep))
    _ = _ := by ring

def Invested (s : ℝ→ℕ) (d : ℕ) (w : Dates) (rp : 0<w.1) (φ : Test 3) (q k : ℕ) (g : ℝ)
    (V : Pin G d→Sec G d) (B e : ℝ) : Prop :=
  let D := Z.store.survey d
  let Q := funded Z (board R (s w.1) w.1 w.2.2) d q g
  Signed V (old F J d φ rp) (film Z R d φ w.1 (s w.1) w.2.2 k g) B e ∧
    ∀ a : Fin D.n, Signed V ((hierarchy F J d w.1) (D.scope a).n (D.scope a).t)
      (Q (D.scope a).n (D.scope a).t) B e

include H ν in
theorem original (lead : Leading F J) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse) (s : ℝ→ℕ)
    (small : Tendsto (aperture R s) trail (𝓝 0)) (d : ℕ) (v : Fin 3→Sec G d) :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) (g : Dates→ℝ) (_ : Tendsto g (trail.curry U) (𝓝 0))
      (T : Dates→Change G d) (_ : Tendsto (fun w=>guide G d (T w)) (trail.curry U) (𝓝 0)),
      ∀ᶠ w : Dates in trail.curry U, ∀ (rp : 0<w.1) (φ : Test 3) (k : ℕ)
        (V : Pin G d→Sec G d) (_ : Declared V (T w)) (B e : ℝ) (_ : 0≤B) (_ : 0≤e)
        (_ : Invested F J Z s d w rp φ q k (g w) V B e),
      let W := film Z R d φ w.1 (s w.1) w.2.2 k (g w)
      ‖old F (WilsonPositionPrescribedFrame.positioned F J Z.store) d φ rp v-W v‖ ≤
        C*((1+B)*e)*(1+‖rows (moved (T w) W)‖) := by
  obtain ⟨C,cp,sale⟩ := WilsonPositionProgramTrialPublicJointPivotMeshSlice.original F J Z M H ν lead U prior s small d v
  refine ⟨C,cp,?_⟩
  intro q g cold T near
  filter_upwards [sale q g cold T near] with w settled
  intro rp φ k V same B e bp ep paid
  let D := Z.store.survey d
  let W := film Z R d φ w.1 (s w.1) w.2.2 k (g w)
  let Q := funded Z (board R (s w.1) w.1 w.2.2) d q (g w)
  let h := (1+B)*e
  have hp : 0≤h := mul_nonneg (by linarith) ep
  have station : ‖docket D (fun _:Unit=>hierarchy F J d w.1)-docket D (retag (fun _:Unit=>T w) (fun _:Unit=>Q))‖≤h := by
    apply (pi_norm_le_iff_of_nonneg hp).2
    intro i
    apply (pi_norm_le_iff_of_nonneg hp).2
    intro a
    exact returned same bp ep (paid.2 a)
  calc
    _ ≤ _ := settled rp φ k
    _ ≤ C*(h+h*‖rows (moved (T w) W)‖) := mul_le_mul_of_nonneg_left
      (add_le_add (returned same bp ep paid.1) (mul_le_mul_of_nonneg_right station (norm_nonneg _))) cp.le
    _ = _ := by dsimp only [h]; ring

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshSource
