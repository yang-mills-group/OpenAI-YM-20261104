import YM.Integration.WilsonPositionOriginalOrientedFrame
import YM.Integration.WilsonPositionCapTransport
import YM.PhysMS.Frame.Journey

/-! File the full finite field basis on the physical tower after the
original stress-shell normalization at grade four. The original station
and cutoff lift are retained by taking linear combinations on the same basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionTraceOrientedFrame

open Function Set Filter Lattice Wilson RG Source Extraction Table Spec OPE OPE.Orbits Climb
open PhysicalNext.Repeat.Legato RG17 Trace Trace.Pilot Next.UVStress Sundial PhysMS PhysMS.Frame
open MergeProof.East Next.Rank Next.Rank.East Maxwell WilsonPositionThermometerOrientedStation
open scoped Topology Classical BigOperators
open private compose_pose from YM.PhysMS.Frame.Journey
open private fitted_lead angles_staff from YM.PhysMS.Frame.Stage

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {I : Type} [Fintype I] (b : Module.Basis I ℂ ((Bel R.family.book).Field 6))

def atShell (P Q : ℝ → tower S) (A : ℝ → Filing R.family 6 I) (r : ℝ) : Filing R.family 6 I :=
  WilsonPositionThermometerStationBasis.onBasis b (A r) (fun i => (P r 6).symm (Q r 6 (b i)))

private theorem filed {Y : (Bel R.family.book).Hierarchy} {l : Ultrafilter (ℕ × ℕ)}
    (P Q : ℝ → tower S) (A : ℝ → Filing R.family 6 I)
    (paid : ∀ m : ℕ, ∀ᶠ r in trail, Filed (f:=f) (Y:=l) Y b r (P r) m (A r))
    (cost : localCost trail P Q) (m : ℕ) :
    ∀ᶠ r in trail, Filed (f:=f) (Y:=l) Y b r (Q r) m (atShell b P Q A r) := by
  let w (r : ℝ) (i : I) := (P r 6).symm (Q r 6 (b i))
  have limits (i : I) : Tendsto (fun r => w r i) trail (𝓝 (b i)) := cost 6 (b i)
  have projects : ∀ᶠ r in trail, ∀ i, Q r 6 (b i) = P r 6 (w r i) :=
    Eventually.of_forall fun r i => ((P r 6).apply_symm_apply (Q r 6 (b i))).symm
  exact WilsonPositionThermometerStationBasis.moving (f:=f) (Y:=l) (H:=Y) b P Q A paid w b limits projects m

variable (F : Final R.family f S) (simple : G.Simple) (H : (Bel R.family.book).Hierarchy)
    (arch : Terrace.Arch R.family) (l : Ultrafilter (ℕ × ℕ))

def Calibrated : Prop :=
  ∃ (P Q : ℝ → tower S) (shell : ℝ → ((Bel R.family.book).Field 4 ≃ₗ[ℂ] S.Field 4)) (φ : E4 → ℝ)
    (κ d e : ℝ → ℝ) (A : ℝ → WilsonPositionThermometerCapStation.Group R.family 6),
    (∀ᶠ r in trail, Q r 4 = shell r) ∧ Target.XScheme F simple H l (fun r => P r 4) shell φ ∧
    Target.FieldComparison F H arch (fun r => P r 4) shell κ d e ∧
    localCost trail P Q ∧ Leading F Q ∧ (∀ d, ∀ᶠ r in trail, Frame.obedient F H (Q r) d) ∧
    WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=H) A P ∧
    WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=H) (WilsonPositionCapTransport.through P Q A) Q ∧
    ∀ m : ℕ, ∀ᶠ r in trail, Filed (f:=f) (Y:=l) H b r (Q r) m
      (WilsonPositionCapTransport.roster (WilsonPositionCapTransport.through P Q A r) 6 b)

theorem on_bliss (bliss : Bliss F l arch H)
    (response : ∀ φ P P', Target.XScheme F simple H l P P' φ →
      ∃ κ d e, Target.FieldComparison F H arch P P' κ d e) :
    Calibrated b F simple H arch l := by
  obtain ⟨P,A,orders⟩ := WilsonPositionThermometerCapStation.simultaneous simple F H bliss
    (fun i : WilsonPositionCapTransport.Address R.family 6=>i.1) WilsonPositionCapTransport.entry
  have staff (m : ℕ) := (orders m).mono fun _ h => h.1
  have bills : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=H) A P := fun m => (orders m).mono fun _ h=>h.2
  have plot := (staff 4).mono fun _ h => h.angle
  have lead := fitted_lead simple F H P staff
  have work := leading_chores F P lead
  have joins := angles_staff simple F H P staff
  obtain ⟨φ,shape⟩ := Work.A05.has_window Pith.sail Pith.sail_at
  obtain ⟨shell,x,y,posed,normal⟩ := Sundial.spectrum_s F H simple bliss plot work shape
  have scheme : Target.XScheme F simple H l (fun r => P r 4) shell φ := ⟨plot,work,⟨x,y,posed⟩,normal⟩
  obtain ⟨κ,d,e,comparison⟩ := response φ (fun r => P r 4) shell scheme
  obtain ⟨Q,level,cost,obeys,leading⟩ := compose_pose simple F H bliss P plot lead joins posed normal
  have book := WilsonPositionCapTransport.transported F simple P Q A bills cost joins obeys
  exact ⟨P,Q,shell,φ,κ,d,e,A,level,scheme,comparison,cost,leading,obeys,bills,book,
    WilsonPositionCapTransport.simultaneous Q _ book 6 b⟩

universe u
theorem original (truth : Target.Result.{u} F simple) :
    ∃ H arch l, Bliss F l arch H ∧ Calibrated b F simple H arch l := by
  obtain ⟨H,arch,l,bliss,-,response⟩ := truth.stress
  exact ⟨H,arch,l,bliss,on_bliss b F simple H arch l bliss response⟩

end YM.Integration.WilsonPositionTraceOrientedFrame
