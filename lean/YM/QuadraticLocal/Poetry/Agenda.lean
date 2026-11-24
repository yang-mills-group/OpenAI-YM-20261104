import YM.QuadraticLocal.Poetry.Queen
import YM.QuadraticLocal.Poetry.Meer
/-!
# Later heights of each earned spectral rank reservation: budget future remainders
 after subtracting an annotated root book, preserving positivity scale.Calendar Ready.Plan
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry
open Function Filter Lattice Laurent Wilson RG Gauge Precision Tree Exterior
open Matrix Finset Push Uniform
open AbsoluteSums AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Field AllOrder.Ink.Money
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sunrise Sunrise.Focus Sunrise.Aviary Stationary
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V G0:Type} {ι α M: Type} [Nonempty ι] [Fintype M] [Fintype α][DecidableEq M] {G:Gauge} (H:Finset M)(q:M)(I:M→ Loan) {a C D b:ℝ} {n m:Side}{k d N l:ℕ}
local notation "Ω" => (Coarse G ⊕ M)
local notation "Z"=> Point M
local notation "E"=> Point (Coarse G⊕M)
namespace Agenda
variable {Γ:ι→ℝ}
abbrev guard (I:M→Loan)(H:Finset M)(e:ℕ):= plusK I H e+2
variable (X:ι→ Roll G M)
def Booked (Γ:ι→ℝ)(e:ℕ)(a:ℝ)(l:ℕ) : Prop := ∃ C:ι→ℝ,CreditF Γ l C∧∀ i:ι,(X i).Faith H q (guard I H e) a (C i) ∧ (X i).honest -- I
local notation "λ₀" e=> guard I H e
-- at absolute height Transfer param κ.Exponent projected.hidden.World.P.
def descent (a:ℝ)(I:M→Loan)(H:Finset M)(N:ℕ):= a / (8*(guard I H N)+1:ℕ)
local notation "x'"=> descent a I H N
lemma day (H:Finset M)(I:M→Loan)(N:ℕ)(ha:0<a) : 0< descent a I H N ∧ descent a I H N≤a∧ descent a I H N*(4*(guard I H N):ℕ) ≤ a/2 := by
 let x:ℝ:= ↑(plusK I H N)+2; unfold descent; refine ⟨div_pos ha (by positivity), div_le_self ha.le (by push_cast; exact le_add_of_nonneg_left (by positivity)),?_⟩; push_cast; change a/(8*x+1)*(4*x) ≤ a/2; rw [div_mul_eq_mul_div,div_le_iff₀ (by unfold x; positivity : 0 < 8*x+1)]; linarith -- nonlinear distribution
variable (HP:0 < b)(hb:b ≤ descent a I H N)(hk:k≤N) (d)
local notation "P" z=> Roll.Posture M G H q z a b (guard I H k) k
lemma scope (j:ℕ) (hN:j≤N)(hp:0<a) (hb':b≤descent a I H N)(hv:0<b)(hk:k≤N): ∃ U:ℝ,Roll.Posture M G H q U a b (guard I H k) k j:=by
 have hL:guard I H k + (j-k) ≤ guard I H N:=by unfold Agenda.guard plusK; omega
 obtain ⟨g,hg,hG⟩:= Lantern.allowed hp hv (hb'.trans (day H I N hp).2.1) H G q (d:=j) (e:=k) (by omega) hL ((mul_le_mul_of_nonneg_right hb' (Nat.cast_nonneg _)).trans (day H I N hp|>.2.2)) (by unfold Agenda.guard plusK; omega)
 exact ⟨_,⟨hv,hg.le,hG⟩⟩
variable (hX:Booked H q I X Γ k a l)
include hX hk hb HP
lemma status (ha:0<a) : ∃ f:ℕ→ι→ℝ, (∀ j≤N,CreditF Γ l (f j)) ∧ ∀ j≤N, ∀ i:ι, let F:=(X i).folded k j;
    -- rank refinement for j≥k. for j<k, still `folio=0`, express pointwise.
    F.Good b (f j i) (guard I H k + (j-k)) ∧ Picket.Fixed H q F ∧ ∀ n (v:rule M n),
      Haiku.Vernal G n (fun j z=> ((X i).folded k j).table n (mingle z v)) j ∧ ∀ A:Link G n, (j<k → F.table n (mingle A v)=0) ∧ (j=k → F.table n (mingle A v)=Roll.total (X i) n A v)∧ ∀ x:Site n,F.site n x (mingle A v)=∑' r,Lantern.gleam ((X i).leg r) x v k j A:=by
 obtain ⟨C,hc,h⟩:= hX; choose f hf using fun i (h':i≤N)=> scope (G:=G) H q I i h' ha hb HP hk; let U(i:ℕ):= if h:i≤N then f i h else 0; have hu i (h:i≤N): Roll.Posture M G H q (U i) a b (guard I H k) k i:= by unfold U; rw [dif_pos h]; exact hf i h
 let V i x:=U i * C x;
 refine ⟨V, fun j hj=> ?_, fun j hj i=> ?_⟩; · simpa [V] using (freeC _ (hu j hj).allot).mul hc
 intro F; let p:= X i; have hr: p.Faith H q (guard I H k) a (C i):= (h i).1; refine ⟨p.warmth H q k (hu j hj) hr, p.stays H q k (hu j hj) hr,fun n v=> ⟨ (X i).spirit H q k hr (h i).2 v hu hj,fun A=>⟨ (X i).nil_before H q k (hu j hj) hr A v, (X i).summit H q k (hu j hj) hr A v,fun x=> (X i).renew H q k (hu j hj) hr A x v⟩⟩⟩
-- Transfer width when shrinking availability on already paid Rolls. Just end-of-grade.
omit HP hk hb
lemma booked_turn (hp:b≤a): Booked H q I X Γ k b l:= by
 obtain ⟨Z',hZ,h⟩:=hX; refine ⟨Z',hZ,fun i=>⟨⟨(h i).1.pinned,Local.sumBudget_mono (h i).1.price (fun j=>Lantern.fee_nn ..) (fun j=>?_) le_rfl⟩,(h i).2⟩⟩
 unfold Roll.price Lantern.money; have ht:= Texture.mag_nonneg ((X i).leg j).atom; gcongr
end Agenda
end YM.QuadraticLocal.Poetry
