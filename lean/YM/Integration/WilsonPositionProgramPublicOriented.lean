import YM.Integration.WilsonPositionProgramPublicFiniteMatrix
import YM.Integration.WilsonPositionProgramPublicPerturbation

/-! Joint numerical orientation of the two measured finite frames using
one decoded signed test array and all columns of the submitted horizon. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicOriented
open Function Filter Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open WilsonMatrixTicketLanesSmearedPivot WilsonThermometerUnitFilingFourSquare
open WilsonPositionProgramPublicMicroscopic WilsonPositionProgramPublicGram
open WilsonPositionProgramPublicFiniteMatrix WilsonPositionProgramPublicPerturbation
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (Z : WilsonPrescription G)
    {d : ℕ} {I : Type*} [Fintype I] (basis : Module.Basis I ℂ ((Bel R.family.book).Field d))

def Roster (B : Profiles R d) {r : ℝ} (hr : 0 < r) (u : Bool → I → ℕ×ℕ → R.family.label d)
    (L : (B.probes.index → ℂ) →L[ℂ] (Bel R.family.book).Field d) (z : ℕ×ℕ) : Prop :=
  let A (b : Bool) := measured F J Z B hr basis (u b) z
  ∃ V : (Bel R.family.book).Field d ≃ₗ[ℂ] (Bel R.family.book).Field d,
    (∀ x, L (A true (V x)) = L (A false x)) ∧
    (∀ x, ‖V x - x‖ ≤ (2*‖L‖)*‖A false x - A true x‖) ∧
    (∀ x, A false x = A true x → V x=x)

theorem submitted (B : Profiles R d) {r : ℝ} (hr : 0 < r)
    (L : (B.probes.index → ℂ) →L[ℂ] (Bel R.family.book).Field d)
    (reads : ∀ x, L (samples F J Z B r x) = x)
    {l : Filter (ℕ×ℕ)} [l.NeBot] (order : l ≤ f.fuse)
    (rows : Bool → (i : I) → Arm R.family S l d (homogeneous F J Z r d (basis i))) :
    ∀ᶠ z in l, Roster F J Z basis B hr (fun b i => (rows b i).source) L z := by
  let A (b : Bool) (z) := measured F J Z B hr basis (fun i => (rows b i).source) z
  have seen (b : Bool) := acquired L (samples F J Z B r) reads (A b)
    (WilsonPositionProgramPublicFiniteMatrix.converges F J Z B hr basis order (rows b))
  filter_upwards [seen false,seen true] with z old new
  obtain ⟨W⟩ := old
  obtain ⟨T⟩ := new
  exact ⟨W.change.trans T.change.symm,alignment L _ _ W T⟩

theorem original {Y : (Bel R.family.book).Hierarchy}
    (lead : Leading F J) (paid : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d)
    (simple : G.Simple) :
    ∃ B : Profiles R d, ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in trail,
      ∃ L : (B.probes.index → ℂ) →L[ℂ] (Bel R.family.book).Field d,
      ‖L‖ ≤ C ∧ (∀ x, L (samples F J Z B r x) = x) ∧
      (∀ x, ‖x‖^2 ≤ C^2*square (samples F J Z B r x)) ∧
      ∀ (hr : 0 < r) (l : Filter (ℕ×ℕ)) [l.NeBot], l ≤ f.fuse →
        ∀ rows : Bool → (i : I) → Arm R.family S l d (homogeneous F J Z r d (basis i)),
          ∀ᶠ z in l, Roster F J Z basis B hr (fun b i => (rows b i).source) L z := by
  obtain ⟨B,K,hK,all⟩ := WilsonPositionProgramPublicGram.original F J Z lead paid simple d
  let C := max K (WilsonPositionProgramPublicDecoder.fee basis*K)
  have cp : 0 < C := hK.trans_le (le_max_left ..)
  refine ⟨B,C,cp,?_⟩
  filter_upwards [all] with r heard
  have bound (x : (Bel R.family.book).Field d) : ‖x‖ ≤ K*‖samples F J Z B r x‖ := by
    simpa only [map_zero,sub_zero] using heard.1 x 0
  obtain ⟨L,reads,size⟩ := WilsonPositionProgramPublicDecoder.original basis (samples F J Z B r) hK.le bound
  refine ⟨L,size.trans (le_max_right ..),reads,fun x => ?_,fun hr _ _ order rows => ?_⟩
  · exact (heard.2.1 x).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hK.le (le_max_left ..) 2) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  · exact submitted F J Z basis B hr L reads order rows

end YM.Integration.WilsonPositionProgramPublicOriented
