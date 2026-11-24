import YM.FormalOPE.RG10.Capture.Wheel
import YM.FormalOPE.RG10.Transit.Meeting

/-!
# Root address-delta transport budget before using any test

The root-address transport at each finite episode carries every derivative in declared address horizon of β
(there is no restriction on size of predicates that may enter modes, but as used β is finite),
with its *actual* physical test direction in mesh convention (typically already includes μᵢ^kᵥ
from taking kᵥ derivatives in native units). Use only with verification of that interpretation.
Exact identity for **all** those smooth tests at each requested order, before unrelated gauge
field estimates. Spare strength: addresses confined to the named `park i z` set (think bounded in
mesh units; e.g. closed central cell). Not requiring no cancellation (may use transported Taylor
measure representation per order, per root). No extra count in root, key or gauge sizes; sum the
true fare before calculating. The *source stability estimate itself* requires RG08 analytic
supplies on this same `Depot` basis when used. Do not presume this from kernel norm values for
true RG transfers or on unperiodized arrays.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Capture
open MvPolynomial Function Finset MeasureTheory Filter Route Transit
open scoped Topology BigOperators Classical
variable {X : Type} [MeasurableSpace X] {T U J : ℕ→ Type} {α β : Type*}

structure Locale (T:ℕ→Type) (X:Type) (α β:Type*) where
  point : ∀ i,T i→X
  park : ∀ i,T i→ Set X
  differential : ℕ→ β → α→ X→ℂ
  blank : β
  first : ∀ φ i,differential i blank φ=differential 0 blank φ

namespace Locale
variable (S : Locale T X α β)

def test (φ:α) := S.differential 0 S.blank φ
end Locale
variable (W : Scale X U) (S : Locale T X α β) (i : ℕ) (z : T i)

/-- One presented root row; `p` counts coupling, with **only** kept orders. -/
structure Strip (S : Locale T X α β) (U : ℕ→Type) (i : ℕ) where
  number : ℕ
  print (j : Fin number) : β
  base (j : Fin number) : Measure X
  currency (j : Fin number) : X→ℂ
  field (j : Fin number) : Letters (U i)
namespace Strip
variable (z : T i) (P : Strip S U i)
-- Sum of finite measures times integrable coefficients. Always through-order and in
-- the SAME presentation of all tests; no independently priced frame after mixing.
structure Meets (z : T i) (P : Strip S U i) : Prop where
  pays j : Integrable (P.currency j) (P.base j)
  focus j : ∀ᵐ x∂(P.base j), x∈S.park i z
  each j φ : Integrable (fun x=>S.differential i (P.print j) φ x * P.currency j x) (P.base j)

variable (φ : α) (n r : ℕ)

def readAt (z : Strip S U i) (φ:α) (j : Fin z.number) := ∫ x, S.differential i (z.print j) φ x * z.currency j x ∂(z.base j)
def strings (φ : α) : Packet (U i) := ∑ j, MvPolynomial.monomial (P.field j) (readAt S i P φ j)
def size (j : Fin P.number) := ∫ x, ‖P.currency j x‖ ∂(P.base j)
def worthAt := ∑ j,fare (W.eyes i (W.tape.sphere (S.point i z) 0)) n (P.field j) * P.size S i j

variable {i}
lemma Strip_sign (j : Fin P.number) : 0 ≤ P.size S i j := integral_nonneg (fun _=> norm_nonneg _)
lemma worthAt_nn : 0≤ P.worthAt W S i z n := sum_nonneg fun _ _ => mul_nonneg (fare_pos _ (W.alive _ _) _ _).le (Strip_sign ..)
variable {S P φ z}
lemma used (h : Meets S i z P) {C:ℝ} (he : ∀ x∈ S.park i z,∀ v, ‖S.differential i v φ x‖ ≤ C) (j : Fin P.number) :
    ‖P.readAt S i φ j‖ ≤ P.size S i j*C := by
  unfold readAt size; rw [← integral_mul_const]
  apply norm_integral_le_of_norm_le ((h.pays j).norm.mul_const _)
  filter_upwards [h.focus j] with x hx
  rw [norm_mul, mul_comm ‖P.currency j x‖]; exact mul_le_mul_of_nonneg_right (he x hx _) (norm_nonneg _)
lemma prices (h : Meets S i z P) {C:ℝ} (he : ∀ x∈ S.park i z,∀ v, ‖S.differential i v φ x‖ ≤ C) :
    worth (W.eyes i (W.tape.sphere (S.point i z) 0)) n (P.strings S i φ) ≤ P.worthAt W S i z n*C := by
  unfold strings; apply (worth_sum _ (W.alive _ _) _ _ _).trans; unfold worthAt; rw [Finset.sum_mul];
  apply sum_le_sum; intro j hj; rw [worth_monomial,mul_assoc]; exact mul_le_mul_of_nonneg_left (used h he j) (fare_pos _ (W.alive _ _) _ _).le
lemma dead (h : Meets S i z P) (ht : ∀ x∈ S.park i z,∀ v, S.differential i v φ x=0) : P.strings S i φ=0 := by
  unfold strings; apply sum_eq_zero; intro j _; rw [show P.readAt S i φ j=0 from ?_,map_zero]; unfold readAt
  apply (integral_congr_ae (show _=ᵐ[P.base j] 0 from ?_)).trans (integral_zero ..); filter_upwards [h.focus j] with x hx; rw [ht x hx,zero_mul]; rfl
end Strip

-- cost prescription. A lift may also carry additional data; verify replacing its tested
-- input by strips before running the lift-specific stable proof, if that projection needs them.
-- No assumption here that every such fit annihilates any subcomponents in apparatus.

def Fits (b : Skin T U α i) (n r : ℕ) (C : ℝ) := ∀ j≤r,∀ z : T i, ∃ P : Strip S U i,
    (∀ φ : α, PowerSeries.coeff j (b z φ)=P.strings S i φ) ∧ Strip.Meets S i z P ∧ P.worthAt W S i z n ≤ C
end YM.FormalOPE.RG10.Capture
