import YM.GradedFar.Physical.Legs

/-!
# Hypothesis boundary for the continuation to genuine physical and all-order comparison

This file keeps the **physical hypotheses** of the respective sections of the
natural-language argument; no claim constructing them. Give consequences of the paid
physical assumptions, and say just which parts are called: read the exact types.
-/
namespace YM.FVA2.GradedFar.Physical
noncomputable section
open Filter Function Real PowerSeries Set
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O.Score O.Enh
open Continuation Continuation.Window
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m h : ℕ} (N : WilsonPrescription G) {d : Fin n → ℕ} {e : Fin m → ℕ}
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple}
    {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J : FramesH P)
    (Q : OPE.Orbits.Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (t : ℝ → ℝ)

local notation "g" => gYM G
/-- Fields part of (G.1), any `B`, C and target power (can choose `k'` specifically in the
application to power `p+2`, with `k'≥p+5`). States explicitly in `ReplacementAt` the
hypothesis on the actual change on t and fields. `windows_eventually` expresses the T-limit
notation here. The source claim includes more (scales down to T=1). -/
def Scaled : Prop := ∀ n p : ℕ, ∀ B C : ℝ, 0<B → 0<C → ReplacementAt N M n (adjusted J) (upper G C B) t p

/-- G.9 value part on the full, center and vacancy requirements, at these compacta.
On the genuine H_r fields, hypotheses compare even if positions move to `T` as in
G.9. Hypotheses retain view i: unselected S or any phase and any o. Arity second block can
be zero. `row` is G.9 formal prediction, before applying any K. The lemmas don't
assert versions including derivative expenses or on grids, reported estimates etc.
-/
def SourceCost : Prop := ∀ n m : ℕ, ∀ (d : Fin n → ℕ) (e : Fin m → ℕ) p (K : Set (Points n))
    (S : Set (Points m)), IsCompact K → K ⊆ conf n → IsCompact S → S ⊆ O.Enh.Outside m →
    ∀ B C : ℝ, 0<B → 0<C → RoundedAt N (Y0 U J d e) (upper G C B) K S t p

/-- G.6's first residual only. Exponent independent of B.

Geometry in these hypotheses is given by fixed shape compacta. So e.g. the Near and Far
separations in their own units, supremum norms of the x, y, etc., are as in the
problem; `T₀` can be taken sufficiently large for the clearance between them. Fin1 on
center (choose this singleton index convention also in G.6).
-/
def OldCost : Prop := ∀ n m : ℕ, 0 < n → ∀ (d : Fin n → ℕ) (e : Fin m → ℕ) h (K : Set (Points n))
    (S : Set (Points m)), IsCompact K → K ⊆ conf n → IsCompact S → S ⊆ O.Enh.Outside m →
    ∀ L L' C : ℝ, 0<C → ∃ D : ℝ, 0 ≤ D ∧ ∀ B, 0<B →
      Spatial (adjusted J) (Y0 U J d e) (Y0 U J (fun _ : Fin 1 => h) e) (packet U J Q d h) (upper G C B) D L L' K S

variable {J Q t N M} (ht : Tendsto (fun r => t r/gYM G r) (𝓝[>] (0:ℝ)) (𝓝 1))
variable {U} {K : Set (Points n)} {S : Set (Points m)}
  (source : SourceCost N U J t) (frame : Scaled N M J t)
  (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m)
-- d,e may be Nat, through legit sectors
include H ht source frame hK hx hS hy
/-- (M.2) first line, on single point rows. Any fixed `B`. Use also for `Fin 1` Near,
including price of all cap-h fields. Here `C` and `T₀` uniform for all `View U`.
-/
theorem first (d : Fin n → ℕ) (e : Fin m → ℕ) {B C : ℝ} (hb : 0<B) (hc : 0<C)
    (p : ℕ) (L R' : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∃ a : ℕ, ∀ᶠ (w : Window) in windows (upper G C B), ∀ i : View U, ∀ x ∈ K, ∀ y ∈ S,
      ∀ u : Inputs G d, Within L u → ∀ v : Inputs G e, Within R' v →
        ‖Ywide U J w i x y u v - crop p (t w.len) (Yx N M x y u v w.sep)‖ ≤
          D*w.Stretch^(∑ j, e j)*gYM G w.len^(p+1) * (1+w.sep)^a := by
  simp_rw [full_same]
  exact paid_first H _ _ t p (Y0 U J d e) hK hx hS hy ((paid_reading simple t ht).mono fun i h=>h.2.2.2)
    (fun i=>frame (e i) p B C hb hc) (source n m d e p K S hK hx hS hy B C hb hc) L R'
end
end YM.FVA2.GradedFar.Physical
