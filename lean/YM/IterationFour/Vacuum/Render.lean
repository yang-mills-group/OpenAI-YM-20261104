import YM.IterationFour.Vacuum.Payload

/-!
# Finite-order *render* interface and automatic beta-readjustment bill

Concrete INPUT to iteration -- receive ADDITIONAL vacuum analytic packets
through a fixed finite order. On output positions here, already rendered
with their true masks and indicators and their coupling-INDEPENDENT
coefficient payloads (in particular the stencil/path choices need not be
made anew when resetting a beta). In using with the independent WilsonX
prescription, the packet `powers` are fluctuation orders, `ranks` account
for the fields already present in their real renders, so typical prefactor is
`g^(power-rank)`; H.rep.path etc remain in place as the lower prescriptions.
E.g. if doing invariant packet completion, leave the mask, entire group
field function of the packet and full curvature paths intact. Source-column
powers of g from field normalization are *not* here.

This doesn't define which diagrams or orders the producer should supply nor
prove that this realizes that prescription. All theorem uses are conditional
on the concrete outputs, including mask re-expression errors, and must take
the SAME render lists and estimates.

Prove the coupling-rescale argument including propagation of Vac-step kinetic
uncertainty. Done on complete lists before hatted estimates. No quotient under
which representations with equal `eval` are identified.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Vacuum
open Lattice Wilson RG Function Currency
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side}

structure Piece (G : Gauge) (n : Side) where
    power : ℕ
    rank : ℕ
    packet : Payload G n
    credit : ℝ

variable (S : List (Piece G n))
namespace Render

/-- order in `g`, as it multiplies the analytic curvature-field slot -/
def stepOrder (w : Piece G n) : ℤ := (w.power:ℤ)-w.rank

def dollars (k : Piece G n → ℝ) : List (Piece G n)→ℝ
  | [] => 0
  | s::l => k s * s.credit + dollars k l

def adorn (k : Piece G n → ℝ) (A : Activities G n) : List (Piece G n) → Activities G n
  | [] => A
  | s::l => s.packet.attach (k s) (adorn k A l)

def append (R : Rep G n) (k : Piece G n → ℝ) : Rep G n :=
    { R with activities:= adorn k R.activities S }

def renders (k : Piece G n → ℝ) (p : BudgetPoint) (U : Config G n) : List (Piece G n) → ℝ
  | [] => 0
  | s::l => k s * s.packet.amount p U + renders k p U l

def prefactor (g : ℝ) (w : Piece G n) := g ^ stepOrder w

def permits (p : BudgetPoint) : Prop := ∀ s∈S,s.packet.Invoice p s.credit

/-- Render inputs are through one internal order. If using more orders later,
    consume a new truncation of the SAME underlying independent coefficients. -/
def gradings (r : ℕ) := ∀ w∈S, 3≤w.power ∧ w.power≤r

variable {S} {p : BudgetPoint}
lemma seated {v : Piece G n} (h : permits (v::S) p) : permits S p := fun w hw=> h w (List.mem_cons_of_mem _ hw)
lemma first {v : Piece G n} (h : permits (v::S) p) : v.packet.Invoice p v.credit := h _ List.mem_cons_self
lemma price_mono (h : permits S p) {f g : Piece G n→ℝ} (hp : f ≤ g) : dollars f S ≤ dollars g S := by
  induction S with
  | nil => exact le_rfl
  | cons a l ih=> exact add_le_add (mul_le_mul_of_nonneg_right (hp a) (a.packet.nonneg (first h))) (ih (seated h))
lemma straight (S : List (Piece G n)) (f : Piece G n→ℝ) (x : ℝ) : dollars (fun i=>x*f i) S=x*dollars f S := by
  induction S with
  | nil => simp [dollars]
  | cons a l ih => rw [dollars,dollars,ih]; ring
lemma loose (h : permits S p) (f : Piece G n→ℝ) (hf : ∀ i,0 ≤ f i) : 0 ≤ dollars f S := by
  induction S with
  | nil => exact le_rfl
  | cons u l ih => exact add_nonneg (mul_nonneg (hf u) (u.packet.nonneg (first h))) (ih (seated h))

variable (f : Piece G n→ℝ) {d z : ℝ} {R : Rep G n}
lemma addition (h : permits S R.p) (H : R.activities.Valid R.p d z) :
    (append S R f).activities.Valid R.p (d + dollars (fun i=>‖f i‖) S) z := by
  induction S with
  | nil => exact (by unfold dollars; rw [add_zero]; exact H)
  | cons s l ih =>
    have hk := Payload.payment (f s) (first h) (ih (seated h))
    rw [dollars, add_comm (‖f s‖ * s.credit) (dollars _ l), ← add_assoc]
    exact hk
lemma additive (h : permits S R.p) (H : R.activities.Valid R.p d z) (U : Config G n) :
    (append S R f).activities.additive R.p U = R.activities.additive R.p U + renders f R.p U S := by
  induction S with
  | nil => rw [renders,add_zero]; rfl
  | cons s l ih =>
    change (s.packet.attach (f s) (append l R f).activities).additive .. = _
    rw [Payload.pays_add _ (first h) (addition f (seated h) H), ih (seated h), renders]
    ring
lemma gas (A : Activities G n) (S) (p : BudgetPoint) :
    (adorn f A S).gas p=A.gas p := by
  induction S with
  | nil => rfl
  | cons s l ih => rw [adorn, Payload.unchanged]; exact ih
lemma generated (h : permits S R.p) (H : R.activities.Valid R.p d z) (U : Config G n) :
    (append S R f).eval U = R.eval U * Real.exp (-renders f R.p U S) := by
  have hp : (append S R f).exponent U = R.exponent U - renders f R.p U S := by
    unfold Rep.exponent
    change _- (append S R f).activities.additive R.p U=_
    rw [additive f h H U]; unfold append; dsimp only; ring
  rw [Rep.eval,hp,sub_eq_add_neg,Real.exp_add,Rep.eval]
  rw [show (append S R f).activities.gas (append S R f).p U = R.activities.gas R.p U from congr_fun (gas f _ _ _) U]
  ring
lemma render_sub (S) (k : Piece G n→ℝ) (p : BudgetPoint) (U : Config G n) :
    renders (f-k) p U S=renders f p U S-renders k p U S := by
  induction S with
  | nil => simp [renders]
  | cons s l ih=> simp only [renders, Pi.sub_apply, ih]; ring

variable (S)
/-- At most this incurred just evaluating the printed model at beta in `stripe b`. -/
def unitBill (b : ℝ) := dollars (fun i=> gainFee (stepOrder i:ℝ) * (gain b)^(stepOrder i)) S
/-- β-Hessian shift conversion bill; use for appended difference packets. -/
def shiftBill (b : ℝ) := dollars (fun i=> tiltFee (stepOrder i:ℝ) * b⁻¹ * (gain b)^(stepOrder i)) S

lemma unit_span {p : BudgetPoint} (h : permits S p) {b x : ℝ} (hb : 0 < b) (hx : x∈stripe b) :
    dollars (fun i=> ‖prefactor (gain x) i‖) S ≤ unitBill S b := by
  have hp:=stripe_pos hb hx
  apply price_mono h; intro i
  unfold prefactor; simp_rw [← Real.rpow_intCast]; rw [Real.norm_of_nonneg (show 0≤(gain x)^(stepOrder i:ℝ) from by unfold gain; positivity)]
  have he := gain_receipt (stepOrder i:ℝ) hb hx
  exact he
lemma unit_nn (h : permits S p) {b : ℝ} (hb : 0 < b) : 0 ≤ unitBill S b := by
  refine loose h _ (fun i => mul_nonneg (gainFee_pos _).le ?_)
  unfold gain; positivity
lemma shift_nn (h : permits S p) {b : ℝ} (hb : 0 < b) : 0 ≤ shiftBill S b := by
  refine loose h _ (fun i => mul_nonneg (mul_nonneg (tiltFee_nonneg _) (inv_pos.mpr hb).le) ?_)
  unfold gain; positivity
lemma change_b (h : permits S p) {b x y : ℝ} (hb : 0 < b) (hx : x∈stripe b) (hy : y∈stripe b) :
    dollars (fun i=> ‖((prefactor (gain x) - prefactor (gain y)):Piece G n→ℝ) i‖) S ≤ shiftBill S b *|x-y| := by
  rw [mul_comm, shiftBill, ← straight]
  apply price_mono h; intro i
  dsimp only
  rw [Pi.sub_apply, prefactor,prefactor,← Real.rpow_intCast,← Real.rpow_intCast, Real.norm_eq_abs,
    mul_comm (|x-y|),← Real.rpow_intCast]
  exact gain_compare (stepOrder i:ℝ) hb hx hy

/-- No changes of any forced predicate and cancellation *after* masks are set on
    the actual fields. -/
lemma actual_reset (h : permits S R.p) (H : R.activities.Valid R.p d z)
    (f k : Piece G n→ℝ) : (append S (append S R (f-k)) k).eval=(append S R f).eval := by
  funext U
  have hk : (append S R (f-k)).activities.Valid _ _ _ := addition (f-k) h H
  rw [generated k (R:=append S R (f-k)) (show permits S _ from h) hk U, generated f h H U, generated (f-k) h H U]
  · change _ * Real.exp (-renders k R.p U S) = _
    rw [mul_assoc,← Real.exp_add,render_sub]
    ring_nf
end Render
end YM.IterationFour.Vacuum
