import YM.Integration.WilsonPositionThermometerCapStation
import YM.Integration.WilsonPositionThermometerStationBasis

/-! Transport every signed station coordinate through the actual change
of the original stress-shell frame. All horizons use the same cutoff lift. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionCapTransport
open Function Filter Set Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open PhysMS PhysMS.Frame MergeProof.East Next.Rank Maxwell WilsonPositionThermometerOrientedStation
open WilsonPositionThermometerCapStation
open scoped Topology Classical BigOperators

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {l : Ultrafilter (ℕ × ℕ)} {H : (Bel C.book).Hierarchy} {c : ℕ}

abbrev Slot (C : Family G) (d : ℕ) := Fin (Module.finrank ℂ ((Bel C.book).Field d))
abbrev whole (C : Family G) (d : ℕ) := Module.finBasis ℂ ((Bel C.book).Field d)
abbrev Address (C : Family G) (c : ℕ) := Σ j : Fin (c+1), Slot C j
def entry (i : Address C c) := whole C i.1 i.2

def roster {I : Type} (A : Group C c) (j : Fin (c+1)) (v : I → (Bel C.book).Field j) : Filing C j I :=
  ⟨A.horizon,index A j,rfl,A.station,A.lift,fun i=>A.change j (v i)⟩

def basisFiling (A : Group C c) (j : Fin (c+1)) : Filing C j (Slot C j) :=
  roster A j (whole C j)

def Book (A : ℝ → Group C c) (P : ℝ → tower S) : Prop := ∀ m : ℕ, ∀ᶠ r in trail,
  projects (f:=f) (Y:=l) H (fun i : Address C c => i.1) entry (A r) (P r) m r

theorem filed (A : ℝ → Group C c) (P : ℝ → tower S) (priced : Book (f:=f) (l:=l) (H:=H) A P)
    (j : Fin (c+1)) (m : ℕ) :
    ∀ᶠ r in trail, Filed (f:=f) (Y:=l) H (whole C j) r (P r) m (basisFiling (A r) j) := by
  filter_upwards [priced m] with r h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun k=>⟨(h.2.2.2.2.1 j).2.2 (whole C j k),h.2.2.2.2.2 ⟨j,k⟩⟩⟩

private theorem render (A : Group C c) (j : Fin (c+1)) (x : (Bel C.book).Field j) :
    WilsonPositionThermometerStationBasis.render (whole C j) (basisFiling A j) x=A.change j x := by
  change (∑ k, (whole C j).repr x k • A.change j (whole C j k))=_
  calc
    _ = A.change j (∑ k, (whole C j).repr x k • whole C j k) := by simp only [map_sum,map_smul]
    _ = _ := congrArg (A.change j) ((whole C j).sum_repr x)

def through (P Q : ℝ → tower S) (A : ℝ → Group C c) (r : ℝ) : Group C c :=
  {A r with change := fun j => ((Q r j).trans (P r j).symm).trans ((A r).change j)}

theorem near (P Q : ℝ → tower S) (A : ℝ → Group C c) (paid : Book (f:=f) (l:=l) (H:=H) A P)
    (cost : localCost trail P Q) (j : Fin (c+1)) (x : (Bel C.book).Field j) :
    Tendsto (fun r => (through P Q A r).change j x) trail (𝓝 x) := by
  let w (r : ℝ) := (P r j).symm (Q r j x)
  have paidAt := filed A P paid j
  have h := WilsonPositionThermometerStationBasis.converges (f:=f) (Y:=l) (H:=H)
    (whole C j) P (fun r => basisFiling (A r) j) paidAt w x (cost j x)
  change Tendsto (fun r => (A r).change j (w r)) trail (𝓝 x)
  exact h.congr fun r => render (A r) j (w r)

theorem simultaneous {I : Type} [Fintype I] (P : ℝ → tower S) (A : ℝ → Group C c)
    (paid : Book (f:=f) (l:=l) (H:=H) A P) (j : Fin (c+1)) (v : I → (Bel C.book).Field j) (m : ℕ) :
    ∀ᶠ r in trail, Filed (f:=f) (Y:=l) H v r (P r) m (roster (A r) j v) := by
  have cost : localCost trail P P := fun d x => by simp
  have limits (i : I) : Tendsto (fun r => (A r).change j (v i)) trail (𝓝 (v i)) := by
    simpa only [through,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] using near P P A paid cost j (v i)
  have close (i : I) := Metric.tendsto_nhds.mp (limits i) _ (cost_pos m)
  filter_upwards [paid m,eventually_all.mpr close] with r h small
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun i=>⟨(h.2.2.2.2.1 j).2.2 (v i),(dist_eq_norm ..).symm.trans_le (small i).le⟩⟩

private theorem axes {j : ℕ} {P Q : PhysMS.tower S}
    (F : Final C f S) (simple : G.Simple) (p : Frame.obedient F H P j) (q : Frame.obedient F H Q j)
    {D : (Bel C.book).Field j ≃ₗ[ℂ] (Bel C.book).Field j} (hd : Coherent H.spin H.spin j D) :
    Coherent H.spin H.spin j (((Q j).trans (P j).symm).trans D) := by
  have left := obedient_realH F simple H p
  have right := obedient_realH F simple H q
  have inv := flips (show Coherent H.spin F.room.kernel.spin j (P j) from ⟨left.2,left.1⟩)
  constructor
  · intro v
    change D ((P j).symm (Q j ((Bel C.book).conj H.spin j v))) = _
    rw [right.2,inv.stars,hd.stars]
    rfl
  · intro i v
    change D ((P j).symm (Q j ((Bel C.book).mirror H.spin j i v))) = _
    rw [right.1,inv.signed,hd.signed]
    rfl

theorem transported (F : Final C f S) (simple : G.Simple) (P Q : ℝ → tower S) (A : ℝ → Group C c)
    (paid : Book (f:=f) (l:=l) (H:=H) A P) (cost : localCost trail P Q)
    (p : ∀ j, ∀ᶠ r in trail, Frame.obedient F H (P r) j) (q : ∀ j, ∀ᶠ r in trail, Frame.obedient F H (Q r) j) :
    Book (f:=f) (l:=l) (H:=H) (through P Q A) Q := by
  intro m
  have close (i : Address C c) := Metric.tendsto_nhds.mp (near P Q A paid cost i.1 (entry i)) _ (cost_pos m)
  filter_upwards [paid m, eventually_all.mpr (fun j : Fin (c+1) => (p j).and (q j)), eventually_all.mpr close]
    with r posted valid small
  refine ⟨posted.1,posted.2.1,posted.2.2.1,posted.2.2.2.1,?_, fun i => (dist_eq_norm ..).symm.trans_le (small i).le⟩
  intro j
  obtain ⟨signed,unit,moves⟩ := posted.2.2.2.2.1 j
  refine ⟨axes F simple (valid j).1 (valid j).2 signed,?_,?_⟩
  · change (A r).change j ((P r j).symm (Q r j ((Bel C.book).unit j)))=_
    rw [(valid j).2.unit,← (valid j).1.unit,LinearEquiv.symm_apply_apply,unit]
  intro x
  exact ((P r j).apply_symm_apply (Q r j x)).symm.trans (moves ((P r j).symm (Q r j x)))

end YM.Integration.WilsonPositionCapTransport
