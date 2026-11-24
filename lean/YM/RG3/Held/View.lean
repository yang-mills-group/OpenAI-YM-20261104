import YM.RG3.Press.Voucher
/-!
# Passive held-variable version of the representation bound

Θ can encode any **announced demand** (e.g. unit balls for each slot in the
smooth external shape test norms, or stipulated addressed/jet data). This
doesn't validate the encoding or the paid support geometry of those tests;
must be supplied, along with common coupons for their entire range. Kept
Θ arguments are fixed even during merged evaluations / eligibility tests;
so no extra derivatives at all at Θ, in particular no increase in required
test order with number of attachments or perturbative order. All data are
quotient-free: pay all addresses also through any testing-sup enlargement.
No assumption of comparing old and new sup AFTER choosing presentation
for each Θ. Provide common labels & profile, so can take supremum on each
component (and interpret later with tensor/multilinear receipts). This doesn't
compare source systems whose markers or roots move with a supplied test inside
Θ (frame transforms, alternative-root aggregation, must bridge first or use
with all permitted origins at *same* stage).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Held
open Wilson RG Lattice Overlay Marker Function Ac RG3.Ink RG3.Press Push.Corrected MeasureTheory Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable (Ω : Type*) (V : Type*) [DecidableEq V] (G : Gauge) (n : Side)

/-- Common Bands view for a parameter set. P and R fixed, even for zeros.
For Captions provide parallel. -/
structure View (P : Rep G n) (R : Census V) where
  origins : V → Site n
  rays : ℕ → R.Mode
  branch : ℕ → Support n
  marks : ℕ → ℕ → R.Mode
  global : Ω → V → ℂ
  regular : Ω → ℕ → Config G n → ℂ
  force : Ω → ℕ → ℕ → Config G n → ℂ

namespace View
variable {Ω V G n R} {P : Rep G n} (L : View Ω V G n P R)

def terms (x : Ω) : Bands R P := ⟨L.origins,L.global x,L.branch,L.rays,L.regular x,L.marks,L.force x⟩

abbrev costR (w : V→ℝ) (b : ℕ → ℝ) (i : V) (j : ℕ) := if i∈(L.rays j).val then Poly.toll w (L.rays j)*P.p.mass (L.branch j) (b j) else 0
abbrev costK (w : V→ℝ) (b : ℕ×ℕ→ℝ) (i : V) (j : ℕ×ℕ) := if i ∈ (L.marks j.1 j.2).val then Poly.toll w (L.marks j.1 j.2)*P.p.mass (P.activities.forced j.1).support (b j) else 0

/-- Predicate taking the supremum INSIDE the summands. Caption channels
added later. Includes every actual held field and root direction used in
Regular supBounds, width/threshold still declared by P; no constant with
Fintype V outside those exported.
-/
structure Passport (w : V→ℝ) (q r t b : ℝ) where
  white : ℕ→ℝ
  black : ℕ×ℕ→ℝ
  active (x:Ω) : (L.terms x).Active
  radii i : 0 < w i
  divisor : 0 < b
  unit x i : w i*‖L.global x i‖ ≤ q
  bulk i : 0≤white i ∧ ∀ x s, s∈(L.rays i).val → P.p.supBounds (L.origins s) (L.branch i) (L.regular x i) (white i)
  bulkCap i : SumBudget (L.costR w white i) r
  spends i j : 0≤black (i,j) ∧ ∀ x U, ‖L.force x i j U‖ ≤ black (i,j)
  till i : SumBudget (L.costK w black i) (t*b)

lemma identifies {w q r t b} (ht : L.Passport w q r t b) (x : Ω) :
    (L.terms x).Active ∧ (L.terms x).Radial w q r t b :=
  ⟨ht.active _,ht.radii,ht.unit x,ht.divisor,⟨ht.white,fun i => ⟨(ht.bulk i).1,fun _ hs => (ht.bulk i).2 x _ hs⟩,ht.bulkCap⟩,
    ⟨ht.black,fun i j => ⟨(ht.spends i j).1,(ht.spends i j).2 x⟩,ht.till⟩⟩

variable {v : V → Site n} {α : Type*} [Countable α] (d : Ω → Article α P.p G R v) (slot : α → ℕ)

variable [Nonempty Ω] [Nonempty V]

def impression : View Ω V G n P R := {
  L with
    marks := ((d (Classical.arbitrary Ω)).impression (L.terms (Classical.arbitrary Ω)) slot).marks
    force x := ((d x).impression (L.terms x) slot).entries }

@[simp] lemma enrolled (x : Ω) : (L.impression d slot).terms x = (d x).impression (L.terms x) slot := rfl

theorem issued (v' : L.origins=v)
    (h : ∀ x,(d x).Sound) (hO : ∀ x,(d x).Hosting P slot)
    (y : α→ Poly R) (w : V→ℝ)
    (hA : ∀ i x U,Width.Covered ((d x).flow i U) (y i)) -- same profile on all x
    {γ : ℝ}
    -- Hosting implies spans/v flags actually fixed. Receipt there with no volume factor.
    (H : Hit (fun i => (P.activities.forced (slot i)).support) P.p.B (fun i => Poly.price w (y i)) P.p.supportExponent γ)
    {q r t b : ℝ} (he : γ ≤ t*b) (hb : 0<b) (hw : ∀ i,0 < w i)
    (hL : ∀ x, Article.Contents (L.terms x))
    (white : ℕ→ℝ) (hu : ∀ x i,w i * ‖L.global x i‖ ≤ q)
    (HM : ∀ i,0≤white i ∧ ∀ x s, s∈(L.rays i).val → P.p.supBounds (L.origins s) (L.branch i) (L.regular x i) (white i))
    (hh : ∀ i, SumBudget (L.costR w white i) r) :
    Nonempty ((L.impression d slot).Passport w q r t b) := by
  let Z i := (P.activities.forced (slot i)).support
  have hes x : (d x).span=Z := funext ((hO x).equal_span)
  let T := L.impression d slot
  change Nonempty (T.Passport _ _ _ _ _)
  have ht x := (d x).chosen_profile (L.terms x) slot (hO x) (h x) hw (y:=y) (fun i U=> hA i x U) (A:=γ) (by rw [hes]; exact H)
  let z := Article.voucher slot v Z y
  refine ⟨white,z,fun x => ?_,hw,hb,hu,HM,hh, fun i j => ?_,fun i => ?_⟩
  · rw [show T.terms x=(d x).impression (L.terms x) slot from rfl]
    exact (d x).impressed_active _ _ (hO x) v'.symm (hL x) (h x)
  · exact ⟨show 0≤z _ from by dsimp only [z]; rw [← hes (Classical.arbitrary Ω)]; exact ((ht (Classical.arbitrary Ω)).1 i j).1,
      fun x U => show _ ≤ z (i,j) from by dsimp only [z]; rw [← hes x]; exact ((ht x).1 i j).2 U⟩
  unfold costK
  refine budget_loosen ?_ he
  dsimp only [z]; rw [← hes (Classical.arbitrary Ω)]
  exact (ht (Classical.arbitrary Ω)).2 i

end View
end YM.RG3.Held
