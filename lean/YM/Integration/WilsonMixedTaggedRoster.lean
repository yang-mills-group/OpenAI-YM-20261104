import YM.RG05Readout.Many.Consider

/-! Boolean alternatives for a fixed finite physical roster on the original
address tree. The projected block, address, engineering label and one-mark
tape are the originals. A true-bit alternative has the zero body. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedRoster
open Function Finset Set MeasureTheory Lattice Wilson RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout
open RG05Readout.Many Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage
open scoped Classical BigOperators

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]

def census (B : Census V) : Census (V × Bool) := Lift B Prod.fst

theorem project (B : Census V) : License B (census B) Prod.fst := chamber B Prod.fst

def advance (π : V → W) : V × Bool → W × Bool := fun x => (π x.1, x.2)

theorem licensed {B : Census V} {C : Census W} {π : V → W} (h : License C B π) :
    License (census C) (census B) (advance π) := by
  intro s hs
  have h0 : Lit C (Prod.fst ∘ advance π) s := (Lit.chain s).2 hs
  have h1 : Lit (Lift C π) Prod.fst s := (Lit.chain s).1 h0
  refine (chamber B Prod.fst) _ ⟨?_,h1.2⟩
  exact h _ (Finset.mem_filter.mp h1.1).2

section addresses
variable {G : Gauge} {C : Family G} {n p : ℕ} {V : ℕ → Type} {W : Type*}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (A : Planner C p n V W)

private def splitChildren (i : ℕ) (h : n ≤ i) :
    V (i+1) × Bool ≃ (V i × Bool) × Address.Bud C p i where
  toFun x := (((A.narrows i h x.1).1,x.2),(A.narrows i h x.1).2)
  invFun y := ((A.narrows i h).symm (y.1.1,y.2),y.1.2)
  left_inv x := by simp
  right_inv y := by simp

def planner : Planner C p n (fun i=>V i × Bool) W where
  labelY i v := A.labelY i v.1
  supportX i v := A.supportX i v.1
  motion := A.motion
  narrows := splitChildren A
  loyal i h x := A.loyal i h x.1
  future i h x := A.future i h x.1

def bodies (I : ∀ i,V i → Body) (i : ℕ) (v : V i × Bool) : Body :=
  if v.2 then 0 else I i v.1

omit [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] in
theorem prepared {I : ∀ i,V i → Body} {b m : ℕ} {hb : n ≤ b}
    (h : PreparedA A I b m hb) : PreparedA (planner A) (bodies I) b m hb := by
  intro i hi hm x
  rcases x with ⟨x, bit⟩
  cases bit
  · exact h i hi hm x
  · change 0 = headFee C p i ((A.narrows i (hb.trans hi)) x).2 0
    rw [map_zero]

omit [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] in
theorem caps {I : ∀ i,V i → Body} {s : W → ℕ} {b : ℕ}
    (h : ∀ x, Cap (s (A.labelY b x)+2) (I b x) 1) :
    ∀ x, Cap (s ((planner A).labelY b x)+2) (bodies I b x) 1 := by
  rintro ⟨x,bit⟩
  cases bit
  · exact h x
  · intro i _ y _
    change ‖iteratedFDeriv ℝ i (0:E4 → ℂ) y‖ ≤ 1
    simp

omit [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] in
theorem body_imprint (I : ∀ i,V i → Body) (T : Pens C p W)
    (h : C.Makes) {j N : ℕ} (hj : j ≤ N) (x : V j × Bool) :
    imprint h (planner A) (bodies I) T j hj x =
      if x.2 then 0 else imprint h A I T j hj x.1 := by
  rcases x with ⟨x,bit⟩
  cases bit
  · rfl
  · simp only [imprint,bodies,↓reduceIte,map_zero,View.spin_zero]

theorem step_license {H : ∀ i,Census (V i)} {i : ℕ} {h : n ≤ i}
    (hL : License (H i) (H (i+1)) (Prod.fst ∘ A.narrows i h)) :
    License (census (H i)) (census (H (i+1))) (Prod.fst ∘ (planner A).narrows i h) :=
  licensed hL

end addresses

omit [DecidableEq V] in
theorem occupancy {n : Side} {o : V → Site n} {k : ℕ} (h : Occupancy o k) :
    Occupancy (o ∘ (Prod.fst : V × Bool → V)) (k*2) := by
  intro y
  have he : univ.filter (fun x:V×Bool=>o x.1=y) =
      (univ.filter fun x:V=>o x=y) ×ˢ (univ : Finset Bool) := by ext x; simp
  change (univ.filter (fun x:V×Bool=>o x.1=y)).card ≤ k*2
  rw [he,card_product]
  simpa using Nat.mul_le_mul_right 2 (h y)

end YM.Integration.WilsonMixedTaggedRoster
