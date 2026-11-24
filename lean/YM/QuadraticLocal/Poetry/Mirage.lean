import YM.QuadraticLocal.Poetry.Skyline
/-!
# Earn analytic Roll table with budget preserving rank and all roots.
 At lowest unmatched grade ONLY. h_geom output projection authenticity.K Post.L witness. Prefer
 not fix spectrum Loans here; reusable Vernal & width. Use on projected S atop.B.
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
variable {V G0:Type} {ι α M: Type}[Fintype M][Fintype α][DecidableEq M] {G:Gauge} (H:Finset M)(q:M) {a C D b:ℝ} {n m:Side}{k d N:ℕ}
local notation "Ω" => (Coarse G ⊕ M)
local notation "Z"=> Point M
local notation "E"=> Point (Coarse G⊕M)
open Pinned Rovers Knot Picket
variable {Γ C₁:ι→ℝ}
def Roll.honest (T:Roll G M): Prop := ∀ i,(T.leg i).atom.Invariant
def Roll.total (P:Roll G M)(n:Side)(A:Link G n)(v:rule M n):= ∑ x:Site n, P.goal x A v
def entry (b:ℝ)(k:ℕ): ℝ:= (b/(k+1:ℕ))/2
lemma entry_pos (k:ℕ)(ha:0<a):0< entry a k:= by unfold entry; positivity
variable (R:ι→AllOrder.Ink.Field (Coarse G⊕M)) -- notation R shadows??
variable (ha:0<a)(he:CreditF Γ d C₁)(hg:∀ i:ι,(R i).Good a (C₁ i) k)(h:∀ i:ι,∀ j:(R i).Ty,Depicted H ((R i).slip j))
variable (hG:∀ (i:ι) n (A:Link G n)(v:rule M n)(p:BaseSites G n), (R i).table n (mingle A v)=(R i).table n (mingle (A-gradientA G n p) v))
variable (hU:∀ (i:ι) n (A:Link G n)(v:rule M n)(u:G.El), (R i).table n (mingle (stain u A) v)=(R i).table n (mingle A v))
include h he hg hG hU ha
lemma mirage (hq:q∈H): ∃ (T:ι→ Roll G M)(D:ι→ℝ), CreditF Γ d D ∧ ∀ i:ι,(T i).Faith H q k (entry a k) (D i)∧ (T i).honest∧∀ n (A:Link G n)(v:rule M n),(T i).total n A v=(R i).table n (mingle A v):= by
 let b' := a/(k+1:ℕ); have hb :0<b':= div_pos ha (by positivity); let F(i:ι):= Picket.wheel q (R i); have hh:b'*(k+1:ℕ)≤ a:= (div_mul_cancel₀ a (by positivity : (↑(k+1:ℕ):ℝ)≠0)).le; have hX i: (F i).Good b' (C₁ i) k:= gears H q hq (R i) (h i) (hg i) hh hb.le
 have hT i n: (F i).table n=(R i).table n:= funext fun x=> echoes H q hq (R i) (h i) (hg i) hh hb.le n x
 obtain ⟨z,hz,hZ⟩:= Knot.addon k 1 zero_lt_one (half_pos hb); simp_rw [one_mul] at hZ;
 let Q i:= Rovers.planet (F i); let x':=z*Real.exp (b'/2*(4*k:ℕ)); let W i:= x'* C₁ i; have hw:0< x':= by unfold x'; positivity
 have hx i: (Q i).Faith H q k (entry a k) (W i):= loose H q (F i) (found H q hq _ (h i)) (hX i) hb z hz.le hZ; -- scope
 let hC :0<entry a k:= entry_pos k ha; refine ⟨fun i=>Roll.illuminate (Q i),_, (show CreditF Γ (0+(0+d)) _ from (freeC _ (Lantern.plastic_nn G k)).mul ((freeC x' hw.le).mul he))|>.up (by omega), fun i=> ⟨ (Q i).luster H q (hx i), fun j=> Texture.keeps _,fun n A v=>?_⟩⟩
 rw [← hT,Field.table_apply]; refine Finset.sum_congr rfl (fun x _=>?_); change (Roll.illuminate (planet (F i))).goal x A v=_; apply Eq.symm; apply Rovers.gallery H q _ (found H q hq _ (h i)) (hX i) A v x _ hb (hx i) hC; · intro n A v u; rw [hT]; exact hU i n A v u
 intro n A v p; rw [hT]; exact hG i n A v p
end YM.QuadraticLocal.Poetry
