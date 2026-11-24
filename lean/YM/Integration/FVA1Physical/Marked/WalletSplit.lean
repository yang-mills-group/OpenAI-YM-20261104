import YM.Integration.FVA1Physical.Marked.LongRows
import YM.Integration.FVA1Physical.Marked.LongCutoff
import YM.Qlocal.Moonset.Rooms
import YM.Qlocal.Feud.Drifts

/-! Identify the short part already present in an inherited wallet and give
the actual field readings and labeled supports of the missing long terms.
The short failed-mask contribution is kept explicitly. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Marker Qlocal Qlocal.Quipu Quipu.Sonnet Tern Moonset
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] {B : Census V} {G : Gauge} {c : Side}

def maskFailure (p : BudgetPoint) (S : Support c) (f : Config G c → ℝ)
    (U : Config G c) := if Healthy p.threshold S U then 0 else f U

theorem maskSplit (p : BudgetPoint) (S : Support c) (f : Config G c → ℝ)
    (U : Config G c) : masked p.threshold S f U + maskFailure p S f U = f U := by
  by_cases h : Healthy p.threshold S U <;> simp [maskFailure, h]

/-- Every accepted long row contributes exactly twice-partitioned mass.
Both summands are evaluated at the same field and same path support.
Signs, the original activation and the spatial matching condition survive. -/
theorem long_parts (A : Tale B G) (choose : A.Decision) (o : V → Site c)
    (s : Senses B) (e : Fin (A.depth+1)) (n : Fin (e.val+A.boom s+1))
    (p : BudgetPoint) (l : Lattice.Order) (w : ℕ) (field : Config G c)
    {a C : ℝ} (ha : 0 < a) (hA : A.Allows a C) :
    let book := A.array s e n
    let x := o (Sonnet.root s)
    let live := fun j => choose s e n j ∧ w < (book j).momentum ∧ (book j).stage.Hears o
    HasSum (fun j : ℕ => if live j then
      masked p.threshold ((book j).cone l x) ((book j).read x A.method) field +
        maskFailure p ((book j).cone l x) ((book j).read x A.method) field else 0)
      (A.playing (A.long choose w) o s e n field) := by
  dsimp only
  let book := A.array s e n
  let live := fun j => (A.long choose w s e n j) ∧ (book j).stage.Hears o
  have h := (Album.global_sum live book (o (Sonnet.root s)) field A.method (hA.pay s e n) ha).hasSum
  refine h.congr_fun ?_
  intro j
  unfold Album.readout
  by_cases hp : choose s e n j ∧ w < (book j).momentum ∧ (book j).stage.Hears o
  · have hp' : live j := ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩
    rw [if_pos hp, if_pos hp', maskSplit]
  · have hp' : ¬live j := fun h => hp ⟨h.1.1, h.1.2, h.2⟩
    rw [if_neg hp, if_neg hp']
    rfl

variable {Ω : Type} [Fintype V] {ξ : V → ℕ} {d b : ℕ}
    {o : V → Site c} {P : Rep G c}

/-- The full unmasked prediction on this wallet equals its physically rendered
coefficient plus the failed short sector and the long correction. This uses the
wallet's own activation, amplitude, coupling, support and test. -/
theorem wallet_full_coefficient (W : Rooms.Wallet Ω o P B ξ d b) (t : Ω)
    (s : Senses B) (w : ℕ) (g : ℝ) (field : Config G c) {a C : ℝ}
    (ha : 0 < a) (hA : (Stanza.son (W.prediction t) b).Allows a C) :
    let A := Stanza.son (W.prediction t) b
    let K := Tale.court P.p.B (o (Sonnet.root s))
    let short := A.wake s (A.short (W.activation t) w) o g
    let long := A.wake s (A.long (W.activation t) w) o g
    ((W.weight t s * A.wake s (W.activation t) o g field : ℝ) : ℂ) =
      ((W.render w g t field).part s.val) +
        ((W.weight t s * (maskFailure P.p K short field + long field) : ℝ) : ℂ) := by
  dsimp only
  rw [Rooms.Wallet.only]
  let A := Stanza.son (W.prediction t) b
  let C₀ := Tale.court P.p.B (o (Sonnet.root s))
  let short := Tale.wake s A (A.short (W.activation t) w) o g
  let long := Tale.wake s A (A.long (W.activation t) w) o g
  have h := congrFun (congrFun (Feud.Peak.splitCost (n := w) A (W.activation t) s o hA ha) g) field
  have hs : short field = A.wake s (W.activation t) o g field - long field := by
    dsimp only [short, long]
    rw [Tale.notationW, Tale.notationW, Tale.notationW, ← sub_div]
    exact congrArg (fun u : ℝ => u/g^(A.boom s)) h
  change ((W.weight t s * A.wake s (W.activation t) o g field : ℝ) : ℂ) =
    ((W.weight t s * masked P.p.threshold C₀ short field : ℝ) : ℂ) +
      ((W.weight t s * (maskFailure P.p C₀ short field + long field) : ℝ) : ℂ)
  rw [← Complex.ofReal_add, ← mul_add, ← add_assoc, maskSplit]
  congr 2
  linarith only [hs]

end YM.Integration.FVA1Physical.Marked
