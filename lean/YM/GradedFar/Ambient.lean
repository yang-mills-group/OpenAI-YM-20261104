import YM.GradedFar.Transport
import YM.GradedFar.Funds
import YM.PhysMS.Frame.Measured
import YM.OPE.Orbits.System
/-!
# Towards physical comparison of the same operands

Use `F : Final C f S` *unchanged*. `P` argument in this file is a variable **assigned** physical
tower (all radii already chosen, not perturbative!), to be instantiated by the proof's H frame,
`WilsonPositionHomogeneousFrame.homogeneous`, and by `Sec` convention at each horizon. `t` argument
in the application of the precision assertions below is the real `reading` used to make that H.

Pricing inputs **required on these exact objects** in the supplied proof. We don't put a different
physical scale, extraction hierarchy or pert order in the center terms. No mixing of phases/viewers.

`FrameForecast`, `RoundPoint`, `PhysicalPacket`: translations of value and size estimates used
(see source proof), with uniform quantifiers where required. They are **hypotheses** in proofs using
them unless otherwise noted. Not definitions of having proved calendar/precision on the original
election. In particular nothing in these definitions assumes `NearFarDelta` or its precision on
the *two* types of compensated residual (don't project D first). Given only `G9`, can't do the
physical comparison: its Far fields are H_r normalized, not the H_{s} we need below. Similarly
under only `G6`, the large operator comparison to MS stays open. Keep these hypotheses separate.

It suffices to use `Fin n` etc and work in the same basis norm of the M2 prediction. Throughout,
onsets for T large can be chosen after all parameters specified. No θ bounds from the independent
regulator used here. The operands in the `forecasts` are all continuum (or formal continuum) ones,
not the rounded-grid implementation or the joint-limit statements of `RoundMeter(ii)`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Function Filter Set PowerSeries
open Source Extraction Table Spec OPE OPE.Orbits Climb Trace.Pilot PhysMS
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.GradedFar
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (P : ℝ → tower S)
variable {n m l h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}

def sites (o : E4) (r : ℝ) (x : Points n) (i : Fin n) := o + r • x i
-- tuples in the exact common shapes (no underlying lattice for this implication)

def assign (r : ℝ) (d : ℕ) : Sec G d ≃ₗ[ℂ] S.Field d :=
    (Maxwell.Free.fields C.labels d).symm.trans (P r d)

def labels (r : ℝ) (v : Inputs G d) : Labels S d := fun i => assign P r (d i) (v i)

/-- Real whole moment (complex value), using that viewer's spectator at arbitrary center.
Keep the scale `s'` used on Far fields as an argument as distinct from the distances `s`
often `r*T`. Takes arbitrary frame `P` as already specified for all r. Kernel in these
Sec arguments already is multilinear. -/
def today (ω : Viewers F) (o : E4) (r s s' : ℝ) (x : Points n) (y : Points m) : Both G d e :=
  (MultilinearMap.compLinearMapₗ (fun i => (assign P s' (e i)).toLinearMap)).compMultilinearMap
    ((OPE.Orbits.moment (S:=S) (d:=Sum.elim d e) (spectator F ω)
      (beside (sites o r x) (sites o s y))).currySum.compLinearMap (fun i => (assign P r (d i)).toLinearMap))

lemma today_apply (ω : Viewers F) (o : E4) (r s s' : ℝ) (x : Points n) (y : Points m)
    (u : Inputs G d) (v : Inputs G e) : today F P ω o r s s' x y u v = OPE.Orbits.whole (spectator F ω)
      (sites o r x) (labels P r u) (sites o s y) (labels P s' v) := by
  unfold OPE.Orbits.whole; apply congrArg (OPE.Orbits.moment (S:=S) (d:=Sum.elim d e) _ _)
  funext i; cases i <;> rfl

def relative (r s : ℝ) (l : ℕ) := (assign P s l).trans (assign P r l).symm
lemma atHome (r s : ℝ) (x : Sec G l) : assign P r l (relative P r s l x) = assign P s l x := by
  rw [relative, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

abbrev atLength (ω : Viewers F) (o : E4) (r T : ℝ) (x : Points n) (y : Points m)
    (u : Inputs G d) (v : Inputs G e) : ℂ := today F P ω o r (r*T) (r*T) x y u v
abbrev atCenter (h : ℕ) (ω : Viewers F) (o : E4) (r T : ℝ) (y : Points m) (v : Inputs G e) :=
  response (h:=h) (today F P ω o r (r*T) (r*T) 0 y) v -- Fin 1 at shape 0, cap h, SAME Far fields

lemma relative_full (ω : Viewers F) (o : E4) (r T : ℝ) (x : Points n) (y : Points m)
    (u : Inputs G d) (v : Inputs G e) : atLength F P ω o r T x y u v =
      today F P ω o r (r*T) r x y u (fun i=> relative P r (r*T) (e i) (v i)) := by
  unfold atLength; rw [today_apply, today_apply]; congr 1; funext i; exact (atHome ..).symm
lemma center_length (ω : Viewers F) (o : E4) (r T : ℝ) (y : Points m)
    (v : Inputs G e) (a : Sec G h) : atCenter F P h ω o r T y v a =
      atLength F P (d:=Output h) ω o r T 0 y (fun _ => a) v := response_apply ..

/-- Physical packet from the *same Reader*, converted to the measuring coordinates at center
(thus not a function of any Far field or viewer). -/
def packet (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (h : ℕ) (o : E4) (r : ℝ) (x : Points n) (v : Inputs G d) : Sec G h :=
  (assign P r h).symm (R.packet h (sites o r x) (labels P r v) o)

variable (t : ℝ → ℝ) (A : Arenas G)
local notation "g" => strength G
-- operator part & onsets for physical (G.1) *growing B-version*. W is GroupS.gaugeN in all uses.
def FrameForecast (W : ℝ → Frames G) (d : ℕ) (U B : ℝ) : Prop :=
    (∃ b : ℝ, 1 ≤ b ∧ ∀ᶠ r in trail, ∀ T : ℝ, 1 ≤ T → T ≤ U*(g r)^(-B) →
      opField (relative P r (r*T) d).toLinearMap ≤ b*T^d) ∧
    ∀ L : ℕ, ∀ᶠ q : ℕ in atTop, ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ r in trail, ∀ T : ℝ, 1 ≤ T → T ≤ U*(g r)^(-B) →
      opField ((relative P r (r*T) d).toLinearMap - cropK W (-Real.log T) q (t r) d) ≤ M*(g r)^L

-- G9 physical RoundMeter (pointwise part; layouts enlarged as needed from fixed compacta).
def RoundPoint (hd : Through l d) (he : Through l e) (U B : ℝ) (p : ℕ)
    (K : Set (Points n)) (S' : Set (Points m)) : Prop :=
    ∃ M : ℝ, 0 ≤ M ∧ ∃ j : ℕ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ᶠ r in trail,
    ∀ T : ℝ, T₀ ≤ T → T ≤ U*(g r)^(-B) → ∀ x ∈ K, ∀ y ∈ S', ∀ o : E4,
    ∀ (ω : Viewers F) (u : Inputs G d) (v : Inputs G e), Box u 1 → Box v 1 →
    ‖today F P ω o r (r*T) r x y u v - constantCrop A (-Real.log T) hd he x y p (t r) u v‖ ≤
      M*(g r)^(p+1)*(1+Real.log T)^j

-- G6 physical packet on receding geometry, *don't vary Q*. One estimate required from G.6;
-- compare with its others plus full statement `HorizonFork`. Fix D externally to control exponent
-- independence needed in selections. Thus B is varied after fixing D.
def PhysicalPacket (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (d : Fin n → ℕ) (e : Fin m → ℕ) (h : ℕ)
    (U B D : ℝ) (K : Set (Points n)) (S' : Set (Points m)) : Prop :=
    ∃ M : ℝ, 0 ≤ M ∧ ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ᶠ r in trail,
    ∀ T : ℝ, T₀ ≤ T → T ≤ U*(g r)^(-B) → ∀ x ∈ K, ∀ y ∈ S', ∀ o : E4,
    ∀ (ω : Viewers F) (u : Inputs G d) (v : Inputs G e), Box u 1 → Box v 1 →
    ‖atLength F P ω o r T x y u v - atCenter F P h ω o r T y v (packet F P Q h o r x u)‖ ≤
      M*(g r)^(-D)*(r*T+(T^(h+1))⁻¹)
end YM.Integration.GradedFar
