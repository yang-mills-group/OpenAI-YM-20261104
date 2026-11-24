import YM.QuadraticLocal.Poetry.Rupture
/-!
# Algebra for publishing stamps before current photos. Resolution of Spectator role field. Width.
 Use with Φ.Document later. Mint Lumi.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry
open Function Filter Lattice Laurent Wilson RG Gauge Precision Tree Exterior
open Matrix Finset Push Uniform
open AbsoluteSums AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Field AllOrder.Ink.Money
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sunrise Sunrise.Focus Sunrise.Aviary Stationary Picket
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V G0:Type} {ι α M: Type} [Nonempty ι] [Fintype M] [Fintype α][DecidableEq M] {G:Gauge} (H:Finset M)(q:M)(I:M→ Loan) {a C D b:ℝ} {n m:Side}{k d N l:ℕ}
local notation "Ω" => (Coarse G ⊕ M)
local notation "Z"=> Point M
local notation "E"=> Point (Coarse G⊕M)
namespace Agenda
variable {Γ:ι→ℝ}
local notation "J"=> Link G n
local notation "W"=> rule (Coarse G⊕M) n
-- V rank.Pay.PostPicture plus snapshot. Commercial audits.News.C.F. Along Vernal.
local notation "λ'" e:max=> guard I H e
variable (T: ℕ→ι→Ink.Field (Coarse G⊕M))(P:ℕ→ι→Roll G M)
def pay (d:ℕ)(a:ℝ) (I:M→Loan)(H:Finset M)(N:ℕ):= Poetry.entry (Agenda.descent a I H N) (guard I H d)
def path (a:ℝ)(I:M→Loan)(H:Finset M)(N:ℕ): ℕ→ℝ
 | 0=> a
 | i+1=> pay i (path a I H N i) I H N
local notation "b'(" d ")" => path a I H N d
lemma solid (N:ℕ)(ha:0<a)(d:ℕ): 0<Agenda.path a I H N d:= by induction d with | zero=>exact ha | succ d h=> exact entry_pos _ (day _ _ N h|>.1)
lemma stub (N:ℕ)(ha:0<a): Antitone (Agenda.path a I H N):= antitone_nat_of_succ_le fun i=> by
 let b:= (Agenda.path a I H N i); let d:=descent b I H N; have h:= (day H I N (solid H I N ha i)); have ht:0 ≤ d:= h.1.le; let z:=d/(guard I H i+1:ℕ); have hz:0 ≤ z:= by unfold z; positivity
 show z/2 ≤ b; apply le_trans ?_ h.2.1; exact (half_le_self hz).trans (div_le_self ht (by exact_mod_cast Nat.le_add_left 1 _)) -- notation quote.Pre
variable (h:Marquis I Γ H a N l T)(hq:q∈ H)
include h hq
lemma inherit (he:k≤N) (hp:Shelled H q I T P Γ l k (path a I H N k)): ∃ R:ℕ→ι→ Roll G M, Shelled H q I T R Γ l (k+1) (path a I H N (k+1)):= by
 let hL:=stub H I N h.pos; let H₀:=hL (Nat.le_succ k); let V:= (path a I H N); let hx:=solid H I N h.pos k; obtain ⟨p,hI,Hx⟩:=mirth H q I T P h hx (hL (Nat.zero_le k)) he hp hq
 let h₁ : 0<V (k+1):= solid H I N h.pos (k+1); let R(j:ℕ):= if j=k then p else P j; let w:= V (k+1); obtain ⟨f,h₃,h4⟩:= status H q I p (day H I N h₁|>.1) (le_refl (descent w I H N)) he hI h₁
 have hh(v:ι)(n:Side)(t:rule (Coarse G⊕M) n)(j) : (∑ e∈Finset.range (k+1),((R e v).folded e j).table n t)= lapse P v t k j + ((p v).folded k j).table n t:= by
    rw [Finset.sum_range_succ]; unfold lapse; unfold R; rw [if_pos rfl]; exact congr_arg (·+ _) (Finset.sum_congr rfl (fun i hi=> by rw [if_neg ( (Finset.mem_range.mp hi).ne)])) -- notation.Nat.ne. unfold maybe occurrence.
 refine ⟨R,?_,?_⟩
 · intro i h; have ht:= Nat.le_of_lt_succ h; rcases lt_or_eq_of_le ht with ht|rfl; unfold R; rw [if_neg ht.ne]; exact booked_turn H q I (P i) (hp.booking i ht) H₀;
   unfold R; rw [if_pos rfl]; exact hI
 intro i hi v n A w; rw [hh v n]; have h₂ := (h4 i (Nat.le_trans (Nat.le_of_lt_succ hi) he) v).2.2 n w; have h':= h₂.2 A; rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with H | h''; rw [h'.1 H, add_zero]; exact hp.recollects i H v n A w; subst i; rw [h'.2.1 rfl]; exact Hx ..
omit hq in
lemma begins : ∃ R:ℕ→ι→Roll G M,Shelled H q I T R Γ l 0 a:= ⟨fun _ _=> (⟨Empty,Empty.elim⟩ : Roll G M), fun i hi=> False.elim (Nat.not_lt_zero _ hi),fun i hi=> False.elim (Nat.not_lt_zero _ hi)⟩
-- No curvature assumed; render T(Cover) with REAL pure marked operators owned.
theorem volume : ∃ R:ℕ→ι→Roll G M,Shelled H q I T R Γ l (N+1) (path a I H N (N+1)):=by
 suffices h:∀ k≤N+1, ∃ R:ℕ→ι→Roll G M,Shelled H q I T R Γ l k (path a I H N k) from h (N+1) le_rfl
 intro k hk; induction k with
 | zero=> exact begins H q I T h
 | succ k ih=> obtain ⟨X,hX⟩:= ih (by omega); exact Agenda.inherit H q I T X h hq (by omega) hX
end Agenda
end YM.QuadraticLocal.Poetry
