import YM.SchemeConversionRG11.Read.Nested
import YM.SchemeConversionRG11.Coupling.Sequence

/-!
# Cancellation at finite regulator

One array on the same cutoff. The normalization must succeed in small neighboring charts on
both base and retuned columns; a divergent high-order column change is allowed. No premise
that all bare coefficients themselves converge in the bare coupling. Unlike Kinetic.converted,
no comparing densities/claiming agreement here -- this is only the field/parameter orbit,
 used before estimating any regulator-approximation errors.
-/

set_option autoImplicit false
noncomputable section

namespace YM.SchemeConversionRG11.Bridge

open Function Filter Maxwell Issue Series Tape Detector Pert.Position Horizon Affine Orbit Coupling
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {F : Labels.Frames G} {n d : ℕ}

/-- Position-field reset alone. -/
def positions (P : Poll F d) (A : Issue F d) := imprint (P.press A) A

/-- Scalar position coupling readout **of the position-frame reset data**, not the raw input
 frame. Always the fixed choice at horizon six. -/
def scaleMeter (P : Poll F 6) (A : Issue F 6) := meter (positions P A)

/-- One candidate retuning comparison: B(z(g)) with its columns changed X(g) at the regulator.
 This algebra step is NOT a claim that B is itself the common regulator or that any
 retuning is physically permissible. In particular constructing a trajectory from the
 independent MS prescription satisfying the convergence of these data is a separate task. -/
def tune (B : Issue F d) (z : Series ℝ) (X : Series (Buffer F d)) := imprint X (insertSeries z B)

variable {P : Poll F d}

lemma sub_data (A : Issue F d) {x : Series ℝ} (hx : x 0 = 0) :
    P.getTest (insertSeries x A) = subJet (P.getTest A) x := by
  funext i j
  let T := P.tapeL j
  have h := trunc_represents (P.getTest A) i
  have hp := trunc_represents x i
  have he := (h.linear (F:=Tape F d (P.table j).r ℂ) T).subJet hp hx
  have hb := (h.subJet hp hx).linear (F:=Tape F d (P.table j).r ℂ) T
  have hw := he.unique hb i le_rfl
  exact hw

lemma survives (A : Issue F d) (V : Series (Buffer F d)) {x : Series ℝ} (hx : x 0 = 0) :
    insertSeries x (imprint V A) = imprint (subJet V x) (insertSeries x A) :=
  funext (fun _ ↦ funext fun _ ↦ tape_substitute hx)

lemma fares_sub (A : Issue F d) {x : Series ℝ} (hx : x 0 = 0) :
    P.fares (insertSeries x A) = subJet (P.fares A) x := by
  funext j
  have h := trunc_represents (P.getTest A) j
  have hp := trunc_represents x j
  have he : subJet (P.getTest A) x j = P.getTest (insertSeries x A) j := congrFun (sub_data A hx).symm j
  rw [Poll.fares, ← he]
  exact ((h.subJet hp hx).linear (F:=Buffer F d) P.fareL).unique
    (((h.linear (F:=Buffer F d) P.fareL).subJet hp hx)) _ le_rfl

lemma constant_position {x : Series ℝ} (hx : x 0 = 0) : subJet P.target x = P.target := by
  funext j
  have h : Represents j (Function.const ℝ (P.scan (P.blank,0))) P.target :=
    record_represents contDiffAt_const
  exact (h.subJet (trunc_represents x j) hx).unique h j le_rfl

lemma pinned_moving (A : Issue F d) (V : Series (Buffer F d)) (hi : P.Pinned A V n) {x : Series ℝ}
    (hx : x 0 = 0) : P.Pinned (insertSeries x A) (subJet V x) n := by
  unfold Poll.Pinned
  rw [← survives _ _ hx, fares_sub _ hx, ← constant_position (P:=P) hx]
  exact hi.subst_jet Through.rfl hx

section cancellation
variable {α : Type*} {l : Filter α}
variable {B : α → Issue F d} {z : α → Series ℝ}
  {X : α → Series (Buffer F d)}

lemma framedTune (B : Issue F d) (v : Series (Buffer F d)) (Z : Series ℝ)
    (p : Series (Buffer F d)) : imprint p (tune B Z v) = imprint (chain v p) (insertSeries Z B) :=
  funext fun _ ↦ funext fun _ ↦ tape_join.symm

/-- Includes even all tests not used in the frame solve. Neighborhood and eventual statements
 are only at this **finite** horizon. -/
theorem common_normal {L : α → Issue F d} (hz : ∀ᶠ a in l, z a 0 = 0)
    (hc : Tendsto (fun a ↦ X a 0) l (𝓝 0))
    (hEq : ∀ a, L a = tune (B a) (z a) (X a))
    (hb : Tendsto (fun a ↦ P.getTest (B a) 0) l (𝓝 P.blank))
    (hl : Tendsto (fun a ↦ P.getTest (L a) 0) l (𝓝 P.blank)) :
    ∀ᶠ a in l, positions P (L a) = insertSeries (z a) (positions P (B a)) := by
  obtain ⟨hu,hue⟩ := Poll.reaches hb
  obtain ⟨hv,hve⟩ := Poll.reaches hl
  let D (a:α) := subJet (P.press (B a)) (z a)
  let C (a:α) := chain (X a) (P.press (L a))
  have he : Tendsto (fun a ↦ D a 0) l (𝓝 0) := hu.congr' (hz.mono fun _ ha ↦ (subJet_base ha).symm)
  have ht : Tendsto (fun a ↦ C a 0) l (𝓝 0) := by
    have h0 := ((after_regular (F:=F) (d:=d)).continuous.tendsto (0,(0:Buffer F d))).comp (hc.prodMk_nhds hv)
    simp only [after_zero_left] at h0
    simp_rw [C, starting]; exact h0
  let g (a:α) := insertSeries (z a) (B a)
  have hp : Tendsto (fun a ↦ P.getTest (g a) 0) l (𝓝 P.blank) := hb.congr'
    (hz.mono fun _ ha ↦ Eq.symm ((congrFun (sub_data (P:=P) _ ha) 0).trans (subJet_base ha)))
  filter_upwards [hz, hue, hve, (hp.prodMk_nhds ht |>.prodMk_nhds he).eventually P.close_inj] with a ha hb hl hk
  have HE : positions P (L a) = imprint (C a) (g a) := by
    rw [positions,hEq a]; unfold C g; rw [hEq a]; exact framedTune ..
  rw [HE]; unfold positions; rw [survives _ _ ha]
  have HH : C a = D a := by
    funext i
    have hs := hk (g a) (C a) (D a) rfl rfl rfl
    have hu : P.Pinned (g a) (C a) i := by rw [Poll.Pinned, ← HE]; exact hl i
    have hv : P.Pinned (g a) (D a) i := pinned_moving _ _ (hb i) ha
    exact hs i (hu.trans hv.symm) i le_rfl
  exact congrArg (fun v ↦ imprint v (g a)) HH

-- Useful finite-order version: retuning identities can be known only through a finite order.
lemma press_through {A B : Issue F d} (h : Identifies n A B)
    (he : ContDiffAt ℝ ω P.solution (P.getTest A 0)) : Through n (P.press A) (P.press B) :=
  (show Through n (P.getTest A) (P.getTest B) from fun i hi ↦ funext fun k ↦ h (P.table k).r (P.table k).f i hi).lift he

theorem eventual_normal_through {L : α → Issue F d} (hz : ∀ᶠ a in l, z a 0 = 0)
    (hc : Tendsto (fun a ↦ X a 0) l (𝓝 0))
    (hEq : ∀ᶠ a in l, Identifies n (L a) (tune (B a) (z a) (X a)))
    (hb : Tendsto (fun a ↦ P.getTest (B a) 0) l (𝓝 P.blank))
    (hl : Tendsto (fun a ↦ P.getTest (L a) 0) l (𝓝 P.blank)) :
    ∀ᶠ a in l, Identifies n (positions P (L a)) (insertSeries (z a) (positions P (B a))) := by
  let l' a := tune (B a) (z a) (X a)
  have hL : Tendsto (fun a ↦ P.getTest (l' a) 0) l (𝓝 P.blank) :=
    hl.congr' (hEq.mono fun _ h ↦ funext fun i ↦ h (P.table i).r (P.table i).f 0 (Nat.zero_le _))
  have he : ContDiffAt ℝ ω P.solution P.blank := (Classical.choose_spec P.discovers).diff
  filter_upwards [hEq, common_normal hz hc (L:=l') (fun _ ↦ rfl) hb hL, hl.eventually (he.eventually (by simp))] with a ha hv he
  rw [← hv]
  exact fun m i ↦ Tape.tape_through (press_through ha he) (ha m i)
end cancellation
end YM.SchemeConversionRG11.Bridge
