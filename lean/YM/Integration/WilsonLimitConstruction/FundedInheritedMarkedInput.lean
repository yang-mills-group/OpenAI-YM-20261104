import YM.Integration.OriginalCoverReanchoring
import YM.Integration.OriginalIssuedMarkedRows
import YM.WilsonCoeffUV.Marked.Bounds.FiniteInterval

/-! Reissue every genuine compound marked sector on a finite blocking
interval. The full untruncated Gears family is retained at all positions,
including coincident independent insertions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedInheritedMarkedInput
open Filter Function Lattice RG RG.Supply Wilson Precision Tree
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Winding
open WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Bank.Mosaic.Near
open FundedMarkedPathSelection IndependentSourcePathFamily OriginalCoverReanchoring Work.F08
open scoped Topology BigOperators Classical

variable {V : Type} [DecidableEq V] [Fintype V] {G : Gauge} {D k : V→ℕ}
    {e m b N : ℕ} (Q : Realm G (e+1) Credit.leanC)

def horizon (i b : ℕ) := Q.y i + (Q.draws.S.scale b-Q.draws.S.scale i) + ((b-i : ℕ):ℝ)

def fee (K : V→ℕ) (i b : ℕ) (A : ℝ) := (tollStep G D k K e Credit.leanC Credit.leanC).buy (horizon Q i b)^(b-i)*A

variable (hm : Q.anchor ≤ m) (hi : m+1≤b) (last : b≤N)
    (closed : Cloze D k Q Credit.leanC) (K : V→ℕ)

abbrev current (P : Outerm G D) := Gears Q.draws Q.paid K k N b (m+1) P

include hm hi in
theorem charge (A : ℝ) (ha : 0≤A) :
    0≤fee (D:=D) (k:=k) Q K (m+1) b A := by
  let mid : Q.anchor ≤ m+1 := hm.trans (Nat.le_succ m)
  have pad := PadRank.frugal Q mid hi
  have one : 1≤horizon Q (m+1) b := (Q.depth _ mid).trans (pad.year _ le_rfl hi)
  exact mul_nonneg (pow_nonneg (zero_le_one.trans ((tollStep G D k K e Credit.leanC Credit.leanC).purchase one)) _) ha

include last closed in
theorem uniform (P : Outerm G D) (well : Wellness k P) {A : ℝ} (ha : 0≤A)
    (loaded : Uniform Q P b ((hm.trans (Nat.le_succ m)).trans hi) A) :
    Uniform Q (current (k:=k) Q K (m:=m) (b:=b) (N:=N) P) (m+1) (hm.trans (Nat.le_succ m))
      (fee (D:=D) (k:=k) Q K (m+1) b A) :=
  nearFit (K':=K) closed P well (hm.trans (Nat.le_succ m)) hi last loaded ha
    (PadRank.frugal Q (hm.trans (Nat.le_succ m)) hi)

def input (P : Outerm G D) (well : Wellness k P) {A : ℝ} (ha : 0≤A)
    (loaded : Uniform Q P b ((hm.trans (Nat.le_succ m)).trans hi) A) (S : Finset V)
    (cells : (V → Cover)→V→Site (loose Q.draws m).L) :
    Input Q hm S k D (fee (D:=D) (k:=k) Q K (m+1) b A) where
  familyAt y := current (k:=k) Q K (m:=m) (b:=b) (N:=N) P (chartIn (loose Q.draws m) y (cells y))
  offsets := cells
  empty _ := (Cog Q.draws Q.paid (K':=K) last P well Q.hG Q.green hi).quiet' _
  degree _ := (Cog Q.draws Q.paid (K':=K) last P well Q.hG Q.green hi).level' _
  price _ J _ i h r := uniform Q hm hi last closed K P well ha loaded _ J i h r

def inputAt (z : ℝ) (span : PadRank Q (m+1) b z) (P : Outerm G D) (well : Wellness k P)
    {A : ℝ} (ha : 0≤A) (loaded : Uniform Q P b ((hm.trans (Nat.le_succ m)).trans hi) A)
    (S : Finset V) (cells : (V → Cover)→V→Site (loose Q.draws m).L) :
    Input Q hm S k D ((tollStep G D k K e Credit.leanC Credit.leanC).buy z^(b-(m+1))*A) where
  familyAt y := current (k:=k) Q K (m:=m) (b:=b) (N:=N) P (chartIn (loose Q.draws m) y (cells y))
  offsets := cells
  empty _ := (Cog Q.draws Q.paid (K':=K) last P well Q.hG Q.green hi).quiet' _
  degree _ := (Cog Q.draws Q.paid (K':=K) last P well Q.hG Q.green hi).level' _
  price _ J _ i h r := nearFit (K':=K) closed P well (hm.trans (Nat.le_succ m)) hi last loaded ha span _ J i h r

variable {I : V→Type} [∀v,Fintype (I v)] (seeds : ∀v,I v→Seed G (D v))

def base (hb : Q.anchor≤b) := bill seeds k e (4*(Q.mint b hb).σ)

theorem first (hb : Q.anchor≤b) (legal : ∀v s,(seeds v s).rank≤k v+(seeds v s).head) :
    0≤base (k:=k) Q seeds hb ∧ Uniform Q (independent seeds) b hb (base (k:=k) Q seeds hb) := by
  let width := (Q.mint b hb).σ
  have hp : 0<width := (perk (R:=Q) hb).trans_le (min_le_right _ _)
  have row (y : V → Cover) := preblock seeds (k:=k) y Finset.univ e (show 0<4*width by positivity) legal
  refine ⟨(row 0).1,?_⟩
  intro y s i hi r
  have paid := (row y).2.2.2 s (Finset.subset_univ _) i hi r
  have split : steep (4*width)=width := by unfold steep;ring
  rw [split] at paid
  exact paid

def actual (legal : ∀v s,(seeds v s).rank≤k v+(seeds v s).head)
    (S : Finset V) (cells : (V → Cover)→V→Site (loose Q.draws m).L) :
    Input Q hm S k D (fee (D:=D) (k:=k) Q K (m+1) b
      (base (k:=k) Q seeds ((hm.trans (Nat.le_succ m)).trans hi))) :=
  let paid := first (k:=k) Q seeds ((hm.trans (Nat.le_succ m)).trans hi) legal
  input Q hm hi last closed K (independent seeds) (deposited seeds legal).1 paid.1 paid.2 S cells

theorem ancestors (legal : ∀v s,(seeds v s).rank≤k v+(seeds v s).head)
    (S : Finset V) (cells : (V → Cover)→V→Site (loose Q.draws m).L) (y : V → Cover) :
    (actual Q hm hi last closed K seeds legal S cells).familyAt y =
      Gears Q.draws Q.paid K k N b (m+1) (independent seeds) (chartIn (loose Q.draws m) y (cells y)) := rfl

include hi last in
theorem symmetry (legal : ∀v s,(seeds v s).rank≤k v+(seeds v s).head) :
    ∀u,ramble u (current (k:=k) Q K (m:=m) (b:=b) (N:=N) (independent seeds)) :=
  (iterated seeds Q.draws Q.paid K hi last Q.hG Q.green legal).2

end YM.Integration.WilsonLimitConstruction.FundedInheritedMarkedInput
end
