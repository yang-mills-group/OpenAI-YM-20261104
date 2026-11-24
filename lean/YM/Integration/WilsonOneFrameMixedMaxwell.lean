import YM.Integration.WilsonOneFrameViewerZero
import YM.Integration.WilsonOneFrameMeasuredStress
import YM.PhysMS.Frame.Tensor
/-! The original occupied stress and all other filed slots at the homogeneous
measurement frame, at all real radii, viewer phases and fixed shape jets. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace YM.Integration.WilsonOneFrameMixedMaxwell
open Function Filter Set Lattice Wilson RG Source Spec Extraction Table Climb OPE OPE.Orbits
open PhysMS PhysMS.Frame Trace Trace.Pilot Trace.Pith Next.UVStress TraceExtension RG17
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open WilsonViewerElectedHierarchy (Selected)
open scoped Topology BigOperators Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    {F:Spec.Final R.family f S}{J:ℝ→PhysMS.tower S}{arch:Trace.Terrace.Arch R.family}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {L:EveryPhase.Almanac F}{Y:(Bel R.family.book).Hierarchy}{ℓ:Ultrafilter (ℕ×ℕ)}
    {simple:G.Simple}{cohort:Ultrafilter (ℕ×ℕ)→Prop}
    (run:Selected.{u} F L Q J Y arch ℓ simple cohort)(Z:WilsonPrescription G)
local notation "C" => R.family
local notation "U" => homogeneous F J Z

private lemma all_viewers {X A : Type*} [Nonempty A] {l : Filter X} {P : X → A → Prop}
    (h : ∀ f : X → A, ∀ᶠ x in l, P x (f x)) : ∀ᶠ x in l, ∀ a, P x a := by
  classical
  let f (x : X) := if bad : ∃ a, ¬P x a then bad.choose else Classical.arbitrary A
  filter_upwards [h f] with x hx a
  by_contra fails
  have bad : ∃ a, ¬P x a := ⟨a,fails⟩
  exact bad.choose_spec (by simpa only [f,dif_pos bad] using hx)

include run in
theorem columns {X : Type*} {l : Filter X} (ρ : X → ℝ) (hr : Tendsto ρ l trail) {n : ℕ} (d : Caps n) (u : X → (i : Fin n) → S.Field (d i)) (v : MaxwellSlots C d)
    (hu : ∀ i, Tendsto (fun r => (U (ρ r) (d i)).symm (u r i)) l (𝓝 (v i)))
    (j : ℕ) (K : Set (Points n)) (compact : IsCompact K) (sep : K ⊆ conf n)
    (ε : ℝ) (pos : 0 < ε) : ∀ᶠ r in l, ∀ x ∈ K, ∀ p : Viewers F,
      ‖iteratedFDeriv ℝ j (fun y => S.classMoment (spectator F p) d (ρ r • y) (u r)) x -
        iteratedFDeriv ℝ j (WickGoal v) x‖ < ε := by
  let w (r : X) (i : Fin n) := (U (ρ r) (d i)).symm (u r i)
  have along (p : X → Viewers F) :
      TendstoUniformlyOn (fun r => iteratedFDeriv ℝ j (measured F (p r) (U (ρ r)) (w r) (ρ r)))
        (iteratedFDeriv ℝ j (WickGoal v)) l K := by
    apply measured_tensor F (hr.eventually (self_mem_nhdsWithin : ∀ᶠ r in trail, 0 < r))
      d j (fun i => Module.finBasis ℂ ((Bel R.family.book).Field (d i))) compact sep _ hu
    intro b
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [hr.eventually (WilsonOneFrameViewerZero.original run Z
      (fun i => Module.finBasis ℂ ((Bel R.family.book).Field (d i)) (b i)) j K compact sep δ hδ)] with r h x hx
    rw [dist_comm, dist_eq_norm]
    exact h x hx (p r)
  have every := all_viewers (l:=l) (P := fun r (p : Viewers F) => ∀ x ∈ K,
    ‖iteratedFDeriv ℝ j (measured F p (U (ρ r)) (w r) (ρ r)) x -
      iteratedFDeriv ℝ j (WickGoal v) x‖ < ε) (fun p =>
    (Metric.tendstoUniformlyOn_iff.mp (along p) ε pos).mono fun r h x hx => by
      simpa only [dist_comm (iteratedFDeriv ℝ j (WickGoal v) x), dist_eq_norm] using h x hx)
  filter_upwards [every] with r h x hx p
  have eqn : measured F p (U (ρ r)) (w r) (ρ r) =
      fun y => S.classMoment (spectator F p) d (ρ r • y) (u r) := by
    funext y
    unfold PhysMS.measured
    simp only [w, LinearEquiv.apply_symm_apply]
  simpa only [eqn] using h p x hx



abbrev Slot (C₀ : Family G) := (Bel C₀.book).Tag ⊕ (Axis × Axis)
def cap {C₀ : Family G} : Slot C₀ → ℕ
  | .inl q => q.1
  | .inr _ => 4
def wick {C₀ : Family G} : (s : Slot C₀) → (Bel C₀.book).Field (cap s)
  | .inl q => q.2
  | .inr ij => Pert.freeStress C₀.labels ij.1 ij.2

def filed (r : ℝ) : (s : Slot C) → S.Field (cap s)
  | .inl v => U r v.1 v.2
  | .inr ij => r^4 • F.sector.energy ij.1 ij.2

include run in
theorem original {n : ℕ} (q : Fin n → Slot C) (j : ℕ) (K : Set (Points n))
    (compact : IsCompact K) (sep : K ⊆ conf n) (ε : ℝ) (pos : 0 < ε) :
    ∀ᶠ r in trail, ∀ x ∈ K, ∀ p : Viewers F,
      ‖iteratedFDeriv ℝ j (fun y => S.classMoment (spectator F p) (cap ∘ q)
          (r • y) (fun i => filed (F:=F) (J:=J) Z r (q i))) x -
        iteratedFDeriv ℝ j (WickGoal (fun i => wick (q i))) x‖ < ε := by
  have aligned (s : Slot C) : Tendsto
      (fun r => (U r (cap s)).symm (filed (F:=F) (J:=J) Z r s)) trail (𝓝 (wick s)) := by
    cases s with
    | inl v =>
      change Tendsto (fun r => (U r v.1).symm (U r v.1 v.2)) trail (𝓝 v.2)
      simp only [LinearEquiv.symm_apply_apply]
      exact tendsto_const_nhds
    | inr ij => exact WilsonOneFrameMeasuredStress.original run Z ij.1 ij.2
  exact columns run Z id tendsto_id (cap ∘ q) _ _ (fun i => aligned (q i)) j K compact sep ε pos

end YM.Integration.WilsonOneFrameMixedMaxwell
end
