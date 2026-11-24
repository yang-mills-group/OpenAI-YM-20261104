import YM.QuadraticLocal.Poetry.Fleece
import YM.QuadraticLocal.Poetry.Dollars
/-!
# Summability of a family of marked terms

A `Lantern` consists of an atom and its list of marked roots. Under
`Roll.Faith`, the atom rank plus the number of roots is bounded, and the
prices have a sum budget. Applying `Lantern.slide` to each term preserves
the marked roots and multiplies the budget bound by at most `Lantern.plastic G k`.
For positive `a`, `Roll.aperture` bounds each evaluated term by its price
times a common constant. `Roll.confirmed` uses this bound to prove summability.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry
open Function Filter Lattice Laurent Wilson RG Gauge Precision Tree Exterior
open Matrix Finset Push Uniform
open AbsoluteSums AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sunrise Sunrise.Focus Stationary
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V G0:Type} {ι α M: Type}[Fintype M][Fintype α][DecidableEq M] {G:Gauge} (H:Finset M)(q:M) {a C D b:ℝ} {n m:Side}{k d:ℕ}
local notation "Ω" => (Coarse G ⊕ M)
local notation "Z"=> Point M
local notation "E"=> Point (Coarse G⊕M)
abbrev swallow (α:Type) (L:List (Point M)) : Slip (Point (α⊕M)) := L.map (Prod.map id Sum.inr)
structure Lantern (G:Gauge)(M:Type) where
 r : ℕ
 atom : Atom G r
 roots : List (Point M)
structure Roll (G:Gauge)(M:Type) where
 Ty : Type
 leg : Ty → Lantern G M
namespace Lantern
variable (p:Lantern G M)
def faced := p.r+p.roots.length
def length := meter p.roots+p.atom.length
structure Bears (p:Lantern G M)(T:Finset M)(q:M)(k:ℕ):Prop where
 tall: p.faced ≤ k
 considered : Depicted T (swallow (Coarse G) p.roots)
 owns : (0,q)∈p.roots
local notation "Λ"=> Texture.scarf
abbrev slide (p:Lantern G M):Lantern G M:= {p with atom:= Λ p.atom}
protected def money (a:ℝ) := p.atom.magnitude* Real.exp (a*p.length)
def frame (x:Site n)(A:Stationary.Link G n) (v:rule M n):= p.atom.poly (fun i=> Work.F03.faceCurl (Work.F03.slotFace (p.atom.leg i) x) (arm G n 1 A)) * AllOrder.Ink.invoice x p.roots v -- rank r physical leading only!
def light (x:Site n)(A:Config G n) (v:rule M n):= p.atom.unmasked A x * AllOrder.Ink.invoice x p.roots v -- full unmasked
lemma rank (x:Site n)(u:Stationary.Link G n) (v:rule M n)(z:G.El →₀ℝ)(h:Texture.Spray G z k)(h':p.r ≤ k): (slide p).frame x u v=∑ i∈z.support,z i* p.frame x (Stationary.stain i u) v:= by
 unfold frame slide; rw [Texture.song _ z h _ h', Finset.sum_mul]; refine Finset.sum_congr rfl fun i _=> ?_; unfold Texture.scarf; simp_rw [Pinned.adjoint_here]; exact mul_assoc ..
lemma fee_nn (a:ℝ):0≤p.money a:= mul_nonneg (Texture.mag_nonneg _) (Real.exp_pos _).le
lemma length_slide : (Texture.scarf p.atom).length=p.atom.length:= rfl
lemma card_le (h:p.faced≤k):p.r≤k∧p.roots.length≤k:= ⟨le_trans (Nat.le_add_right ..) h,le_trans (Nat.le_add_left ..) h⟩
def plastic (G:Gauge)(k:ℕ):ℝ:= ∑ i∈Finset.range (k+1),(Fintype.card (Texture.Tooth G i):ℝ)
lemma plastic_nn (G:Gauge) (k:ℕ): 0 ≤ plastic G k:= Finset.sum_nonneg fun _ _=> Nat.cast_nonneg _
lemma dues (h:p.faced≤k)(a:ℝ) : (slide p).money a≤ plastic G k*p.money a:= by
 unfold Lantern.money; have he:= card_le p h; have hx : (Fintype.card (Texture.Tooth G p.r):ℝ) ≤ plastic G k:= Finset.single_le_sum («f»:=fun i=> (Fintype.card (Texture.Tooth G i):ℝ)) (fun i hi=> Nat.cast_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le he.1)); rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right ((Texture.budget p.atom).trans (mul_le_mul_of_nonneg_right hx (Texture.mag_nonneg _))) (Real.exp_pos _).le
end Lantern
namespace Roll
variable (T:Roll G M)(x:Site n) (A:Stationary.Link G n)(v:rule M n)
def dusk := fun i:T.Ty => (T.leg i).frame x A v
def goal := ∑' i,T.dusk x A v i
def price (a:ℝ)(i:T.Ty):=(T.leg i).money a
structure Faith (T:Roll G M)(H:Finset M)(q:M)(k:ℕ)(a C:ℝ): Prop where
 pinned : ∀ i,(T.leg i).Bears H q k
 price : SumBudget (T.price a) C
variable (h:Faith T H q k a C)
def illuminate (T: Roll G M): Roll G M :=⟨T.Ty,fun i=> Lantern.slide (T.leg i)⟩
include h
lemma luster : (illuminate T).Faith H q k a (Lantern.plastic G k*C):= by
 constructor; · exact fun i=> ⟨(h.pinned i).tall,(h.pinned i).considered,(h.pinned i).owns⟩
 exact Local.sumBudget_mono (Local.sumBudget_mul_left h.price (Lantern.plastic_nn G k)) (fun i=> Lantern.fee_nn ..) (fun i=> Lantern.dues (T.leg i) (h.pinned i).tall a) le_rfl
variable (hp:0<a)
include hp
lemma aperture {n:Side}(A:Stationary.Link G n)(v:rule M n):∃ D≥(1:ℝ),∀ (x:Site n) (i:T.Ty), ‖T.dusk x A v i‖ ≤ D*T.price a i := by
 let f:= dColor G n 1 (arm G n 1 A); let U:ℝ:= 1+‖f‖; let V:= 1+‖v‖; have hu:1≤U:= le_add_of_nonneg_right (norm_nonneg _); have hv:1 ≤ V:=le_add_of_nonneg_right (norm_nonneg _); let C':= U^k*V^k; refine ⟨C',one_le_mul_of_one_le_of_one_le (one_le_pow₀ hu) (one_le_pow₀ hv),fun x i=> ?_⟩;
 let z:=T.leg i; have hh:= Lantern.card_le z (h.pinned i).tall; have H := Field.ticket x (z.roots); unfold dusk Lantern.frame; rw [norm_mul]; let v₀:=z.atom.magnitude; have hz:v₀≤ T.price a i:= le_mul_of_one_le_right (Texture.mag_nonneg _) (Real.one_le_exp (mul_nonneg hp.le (by positivity))); have ht₁ : ∀ j:Fin z.r, ‖Work.F03.faceCurl (Work.F03.slotFace (z.atom.leg j) x) (arm G n 1 A)‖ ≤ U:= fun j=> (norm_le_pi_norm f _).trans (le_add_of_nonneg_left zero_le_one)
 refine (mul_le_mul ?_ (show ‖Ink.invoice x z.roots v‖≤V^k from (by simpa only [one_mul] using H.2.2 v : |Ink.invoice x z.roots v| ≤ V^(z.roots.length)).trans (pow_le_pow_right₀ hv hh.2)) (norm_nonneg _) (mul_nonneg (show 0 ≤ T.price a i from Lantern.fee_nn ..) (pow_nonneg (show 0≤ U from by positivity) k))).trans_eq (by unfold C'; ring)
 · exact (Work.F03.poly_bound z.atom (fun i=>_) _ ht₁).trans (mul_le_mul hz (pow_le_pow_right₀ hu hh.1) (by positivity) (Lantern.fee_nn ..))
lemma confirmed (x:Site n)(A:Stationary.Link G n)(v:rule M n): Summable (T.dusk x A v):= by
 obtain ⟨D,hD,hE⟩:= aperture H q T h hp A v; exact Summable.of_norm_bounded (h.price.2.1.mul_left D) (hE x)
omit hp
lemma bright (u: (illuminate T).Ty): (((illuminate T).leg u)).atom.Invariant:= Texture.keeps _
end Roll
end YM.QuadraticLocal.Poetry
