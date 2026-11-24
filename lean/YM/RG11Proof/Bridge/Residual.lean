import YM.RG11Proof.Rate.Frames
/-!
# Residual form on finite-regulator separated correlations

Here A is the W-frame continuum perturbative array and B is the independent MS continuum array.
Input V regulator pivot measurements in W parameter, D regulator MS-matching
stencils in MS parameter, and raw transfer t(g),Z(g) from top-vector solves (row
convention: Z sends MS basis into W basis). Desired result B=Z;A(t(g)), i.e.
substitute on A with c in regulator orientation c.act A=B. Keep this orientation
when attaching OPE, stress and scale laws; reverse it for final transformation.

One fixed regulator schedule budget and finite field horizon. Per-mark remainder
relative to **simultaneous** slot replacement, with the following per-slot alternatives: a
slot is residual (kernel sign/test costs must be paid into `E` by the producer)
or converted, and in the latter case the raw converting matrix is OUTSIDE the
estimate. This is a power-series identity (coefficients at MARK TESTS), not
an identity/contraction on arbitrary represented density and not automatic
from separated unrelated regulator limits. `Saves` leaves this as a precise
input with finite-order quantifiers. The singular-site/IR and real-vacuum links,
representation origins/norms, common-regulator matching and regulator-removal
rates (satisfying these hypotheses on A/Fk, MS and their common test rules) are
substantive external obligations. For eventual equalities adapt via `Eventually`
lemmas, or define residual as the difference including finite-regulator mismatch
with `Saves` costs. Never assert it on an unrelated choice of Final.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Bridge
open PowerSeries YM.PertExtension.Position YM.RG11.Jets YM.RG11.Formal YM.RG11.Rate Filter
open scoped BigOperators Classical
variable {R J P α : Type*} [Fintype J] {shape : P→ℕ}
local notation "PS"=>PowerSeries ℝ

/-- Mask h = slots KEPT AS RESIDUALS (nonempty); `w` = pivot label on EACH
slot, but for residual slots these can be repetitions with zeros (one may
pin/pad them to a single address; actual choice cannot lose support costs in E).
Retain full v correlations. -/
def TailTerms (J R : Type*) {P} (shape : P→ℕ) := (v : Mark J shape) → Finset (Fin (shape v.1))→
    (Fin (shape v.1)→J)→PowerSeries R

def tail (e : TailTerms J R shape) (Z : Square J (PowerSeries R)) [CommSemiring R] (v : Mark J shape) : R⟦X⟧ :=
  ∑ h : Finset (Fin (shape v.1)), if h=∅ then 0 else
    ∑ w, e v h w * ∏ i∈ (Finset.univ \ h), Z (v.2 i) (w i)

variable {k : Budget α} {T : α→Change ℝ J} {e : α→TailTerms J ℝ shape} {n : ℕ}

-- ALL tests/costs on the same finite arity v. Does not require residual
-- estimates without the h attachments, but the coefficient price here is AFTER
-- any required conversion to the MS ruler (or use an adapter paying that
-- conversion BEFORE assuming `LeanTail`).
def LeanTail (k : Budget α) (n : ℕ) (e : α→TailTerms J ℝ shape) (v : Mark J shape) :=
  ∀ h:Finset (Fin (shape v.1)), h.Nonempty→ ∀ w, Pieces k n (fun a=>e a v h w) (fun _=>0)

theorem LeanTail.carries {v : Mark J shape} (H : LeanTail k n e v) (hn : 0<n) {w : α→ℝ} {T' : α→Change ℝ J} (hc : OnChange k w n T T') :
    Unpaid k w n (fun a=> tail (e a) (T a).Z v) (fun _=>0) := by
  have he : (fun _:α=> (0:PS))=(fun a=> tail (fun _ _ _=> (0:PS)) (T' a).Z v) := by
    funext a; simp [tail]
  rw [he]
  refine Unpaid.sum Finset.univ (fun u _=> ?_)
  by_cases hp:u=∅
  · simp only [hp, ↓reduceIte]; exact Unpaid.const _
  simp only [if_neg hp]
  exact Unpaid.sum Finset.univ (fun i _=>Unpaid.mul hn (Unpaid.of_pieces w (H u (Finset.nonempty_iff_ne_empty.mpr hp) i))
     (Unpaid.prod _ hn (fun l _=> hc.fields _ _)))

-- Eventual finite-regulator readout hypothesis after exact re-expression.
-- Extra `Near` comparison term usable for truly external mismatch already in
-- same Euler units with NO unknown coefficient multipliers. No assumption
-- that the main tail itself is Near without the above law.
structure Saves (k : Budget α) (M : ℕ) (m : Finset (Mark J shape)) (V D : α → ArrayAt J ℝ shape)
    (c : α → Change ℝ J) where
  bits : α → TailTerms J ℝ shape
  slips {v} (h : v∈m): LeanTail k M bits v
  values {i} : i ≤ M → ∀ v ∈ m, NearFn k
      (fun a=>coeff i (D a v)) (fun a=> coeff i ((c a).act (V a) v + tail (bits a) (c a).Z v))

-- Useful variant: spec with `Through` equality only eventual.
def Saves.of_eq {M : ℕ} {m : Finset (Mark J shape)} {V D : α → ArrayAt J ℝ shape}
    {c : α → Change ℝ J} {bits : α → TailTerms J ℝ shape}
    (slips : ∀ v∈m, LeanTail k M bits v)
    (h : ∀ v∈m, ∀ᶠ a in k.along,Through M (D a v) ((c a).act (V a) v + tail (bits a) (c a).Z v)) : Saves k M m V D c :=
  ⟨bits,fun {i} hi=> slips i hi,fun {i} hi v hv=> ⟨0,le_rfl,(h v hv).mono (fun a he=>by simp only [he i hi,sub_self,abs_zero,zero_mul]; exact le_rfl)⟩⟩

variable {V D : α→ArrayAt J ℝ shape} {M:ℕ} {m:Finset (Mark J shape)}

theorem Saves.unpaid (H : Saves k M m V D T) (hn : 0<n) (hm : n ≤ M) {w : α→ℝ}
    {T' : α→Change ℝ J} (hc : OnChange k w n T T') {v : Mark J shape} (hV : v∈m):
    Carry k w (fun a=> coeff n (D a v)) (fun a=> coeff n ((T a).act (V a) v)) := by
  have he : LeanTail k n H.bits v:= fun i h j=> (H.slips hV i h j).of_le hm
  have hv := (he.carries (v:=v) hn hc).top
  have h := (H.values hm v hV).carry w
  simp only [map_zero] at hv
  simp only [map_add] at h
  exact h.trans (by simpa only [add_zero] using (Carry.refl (fun a=> coeff n ((T a).act (V a) v))).add hv)
end YM.RG11.Bridge
