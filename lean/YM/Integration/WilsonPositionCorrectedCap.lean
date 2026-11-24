import YM.Integration.WilsonPositionCapTransport
import YM.Integration.WilsonPositionPrescribedLeading
import YM.Integration.WilsonPositionThermometerCorrectedUnit

/-! The independent measuring correction acts on the genuine common
station at each horizon. It commutes with signed rotations and conjugation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionCorrectedCap
open Function Filter Set Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize WilsonPositionPrescribedFrame
open WilsonPositionThermometerCapStation WilsonPositionCapTransport
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

theorem signed (F : Final C f S) (P : ℝ → tower S) (V : Store G) (H : (Bel C.book).RealSpin)
    (j : ℕ) (r : ℝ) : Coherent H H j (WilsonPositionPrescribedFrame.change F P V j r) := by
  let basis := Maxwell.Free.fields C.labels j
  let D := WilsonPositionPrescribedScreen.correction F P V j r
  have bar (x : (Bel C.book).Field j) : basis ((Bel C.book).conj H j x) = reel j (basis x) :=
    Subtype.ext (Maxwell.Free.address_star C.labels x)
  have axis (s : Signed) (x : (Bel C.book).Field j) :
      basis ((Bel C.book).mirror H j s x) = ori s.ortho j (basis x) := Subtype.ext (Maxwell.Free.address_motion C.labels s x)
  by_cases h : Bijective (stand D)
  · have row (x : (Bel C.book).Field j) : basis (WilsonPositionPrescribedFrame.change F P V j r x) = stand D (basis x) := by
      simpa only [basis,D,LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply] using
        congrArg basis (WilsonPositionPrescribedFrame.leg F P V h (basis x))
    constructor
    · intro v
      apply basis.injective
      simp only [row,bar,stood_reel]
    · intro s v
      apply basis.injective
      simp only [row,axis,stood_ori]
  · have absent : ¬Bijective (stand (WilsonPositionPrescribedScreen.correction F P V j r)) := h
    rw [WilsonPositionPrescribedFrame.change,dif_neg absent]
    exact ⟨fun _=>rfl,fun _ _=>rfl⟩

variable {R : Run G} {T : Table R.family.book} (F : Final R.family f T)
    (P : ℝ → tower T) (V : Store G) {H : (Bel R.family.book).Hierarchy}
    {l : Ultrafilter (ℕ × ℕ)} {c : ℕ}

def adjusted (A : ℝ → Group R.family c) (r : ℝ) : Group R.family c :=
  {A r with change := fun j => (WilsonPositionPrescribedFrame.change F P V j r).trans ((A r).change j)}

private theorem localCost_on (lead : Leading F P) : localCost trail P (positioned F P V) := by
  intro j x
  simp only [positioned,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
  exact WilsonPositionPrescribedLeading.applied F P V lead j x

theorem original (A : ℝ → Group R.family c) (paid : Book (f:=f) (l:=l) (H:=H) A P)
    (lead : Leading F P) : Book (f:=f) (l:=l) (H:=H) (adjusted F P V A) (positioned F P V) := by
  intro m
  have aim (i : Address R.family c) : Tendsto (fun r=> (adjusted F P V A r).change i.1 (entry i)) trail (𝓝 (entry i)) := by
    simpa only [adjusted,WilsonPositionCapTransport.through,positioned,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] using
      near P (positioned F P V) A paid (localCost_on F P V lead) i.1 (entry i)
  have close (i : Address R.family c) := Metric.tendsto_nhds.mp (aim i) _ (cost_pos m)
  filter_upwards [paid m,eventually_all.mpr close] with r h fee
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,?_,fun i=>(dist_eq_norm ..).symm.trans_le (fee i).le⟩
  intro j
  obtain ⟨axes,unit,coords⟩ := h.2.2.2.2.1 j
  have moved := signed F P V H.spin j r
  refine ⟨⟨?_,?_⟩,?_,fun x=>coords (WilsonPositionPrescribedFrame.change F P V j r x)⟩
  · intro x
    exact (congrArg ((A r).change j) (moved.stars x)).trans (axes.stars _)
  · intro s x
    exact (congrArg ((A r).change j) (moved.signed s x)).trans (axes.signed _ _)
  exact (congrArg ((A r).change j) (WilsonPositionThermometerCorrectedUnit.corrected_unit F P V j r)).trans unit

theorem mixed {I : Type} [Fintype I] (A : ℝ → Group R.family c) (paid : Book (f:=f) (l:=l) (H:=H) A P)
    (lead : Leading F P) (d : I → Fin (c+1)) (v : ∀ i, (Bel R.family.book).Field (d i)) (m : ℕ) :
    ∀ᶠ r in trail, projects (f:=f) (Y:=l) H d v (adjusted F P V A r) (positioned F P V r) m r := by
  have book := original F P V A paid lead
  have atSite (i : I) := (WilsonPositionCapTransport.simultaneous _ _ book (d i) (fun _ : Unit=>v i) m).mono
    fun r h => (h.2.2.2.2 ()).2
  filter_upwards [book m,eventually_all.mpr atSite] with r sent fees
  exact ⟨sent.1,sent.2.1,sent.2.2.1,sent.2.2.2.1,sent.2.2.2.2.1,fees⟩

end YM.Integration.WilsonPositionCorrectedCap
