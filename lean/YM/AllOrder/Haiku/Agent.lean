import YM.AllOrder.Haiku.Coat
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Haiku
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Response Ink Ink.Method Ink.Money
open Tree Wilson Exterior Precision Push Pressure Next.Fluctuations MeasureTheory
open Stationary
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n m c:Side}{a C D:ℝ}{k N:ℕ} {ι:Type}
local notation "L"=> Coarse G
-- defeq Ward.Link footing
local notation "F[" n "]"=> Stationary.Link G n

namespace Coat
open PertExtension.Series Radial Bloch Stationary.Haiku
variable {Λ:ι→ℝ}{A:ι→Ink.Money.Bills (Coarse G)} (Q:PictureT Λ A (k+1))
structure Admits (F:Ink.Money.Bills (Coarse G)): Prop where
 rise n : AnalyticAt ℝ (F n) 0
 lull n : tolerant (F n)
 color n : Stained G (F n)
 garn n (s:Signed) (x:Link G n): F n (orderTurn (G:=G) s x)= F n x
lemma votes {A : ℕ→Ink.Money.Bills (Coarse G)}(h:∀ n,Etiquette A n k) (hs:∀ n,Station k n A) (hf:∀ n,Plausible (A k n)): Admits (A k):= ⟨fun n=> (hf n).smooth.contDiffAt.analyticAt,fun n=>(h n).steady (hs n),fun n u=> Eventually.of_forall ((h n).paints u),fun n=>(h n).rotates⟩
abbrev billT (_k:ℕ) (α:Gauge)(n:Side) := orderTurn (G:=α) (m:=n) (1:Signed)
lemma Admits.rotate {F:Ink.Money.Bills (Coarse G)}(h:Admits F)(n:Side): Lit k (F n):=by intro s; unfold noteAt beat; rw [show F n ∘ orderTurn (G:=G) s=F n from funext (fun x=> h.garn n s x)]
variable (ha:∀ x, Admits (A x))
include ha
lemma colors_t (i:ι): Features (Q.shape i) Q.heigh (Q.fee i) := by
 let a0:=Ink.Echo.amplify three; have hx:=ha i; refine purchased_At (F:=fun p=> A i (a0 p)) (Ink.Echo.limitless three) tendsto_const_nhds (Q.price i) (fun p=> ?_) (fun i=> hx.rise _) (fun p=> hx.color _) (fun p=> hx.lull _)
 rw [mul_zero]; exact Q.period i _
lemma matchT (Q:PictureT Λ A 1)(i:ι): TributeColor (Q.shape i) Q.heigh (Q.fee i) Unsigned := by
 let a0:=Ink.Echo.amplify three; have hx:=ha i; refine charter (F:=fun p=> A i (a0 p)) (Ink.Echo.limitless three) (Q.price i) tendsto_const_nhds (fun p=>?_) (fun i=> hx.rise _) (fun i=>hx.lull _) (fun i=> hx.color _) (fun i s _=> Eventually.of_forall (fun x=>hx.garn _ s x)); rw [mul_zero]; exact Q.period i _

-- skin family independent of torus. from earned exact orientation period.
lemma gloss : ∃ t D,0<t ∧ t ≤ Q.heigh ∧ 0≤D ∧ ∃ f:ι→Skin G (k+1), ∀ i, Shades (f i) (Q.shape i) t (Q.fee i*D) := by
 rcases k with _|k
 · obtain ⟨t,D,h,hL,hD,H⟩:= veins G _ Q.pos; choose F hF h' using fun i=> H (Q.fee i) 0 (Q.shape i) (Q.bill.nonneg _) (colors_t Q ha i) (multiLens (matchT ha _ i)); exact ⟨t,D,h,hL,hD,F,hF⟩
 obtain ⟨t,D,h,hL,hD,H⟩:=strokes G (k+1+1) (by omega) _ Q.pos; choose F hF using fun i=>H _ _ (Q.bill.nonneg i) (colors_t Q ha i); exact ⟨t,D,h,hL,hD,F,hF⟩
-- Gram packet, age. Used for cancellations k and beyond. Need aperture equality ∀ periods directly (no residual O). mark asserts not norm.
abbrev Packet (G:Gauge)(r:ℕ):= ℕ→ Atom G r
def Letter (Λ:ι→ℝ) (V:ι→Packet G k) (t:ℝ)(C:ι→ℝ):Prop:= Grade Λ C ∧ ∀ i, (SumBudget (fun j=> (V i j).budget t) (C i))∧∀ j,(V i j).Invariant
abbrev Curled (Λ:ι→ℝ)(u:ι→Packet G k): Prop:=∃ t:ℝ,0<t∧∃ C, Letter Λ u t C
lemma palette (k:ℕ)(H:Ready Λ A (k+1)): ∃ P:ι→ Packet G (k+2), Curled Λ P ∧ ∀ i n, Radial.jet (A i n) (k+2)=jet (turnSeries (P i) (m:=n)) (k+2) := by
  obtain ⟨Q⟩:=H; obtain ⟨t,D,h,hL,hD,f,hf⟩:= gloss Q ha;
  let P(i:ι): Packet _ _:= issue (f i); have ht i:= artery_funded (hf i); refine ⟨P,⟨t,h,_,(by refine ⟨?_,ht⟩; exact (((Q.bill.mul (gia D hD)).mul (gia _ (inkCost_nonneg _ _ _)))) )⟩,fun i n=>?_⟩;
  ext1 x; unfold jet; rw [aperture_eq (colors_align (A i n) (ha i|>.rise _) ((ha i).rotate n) _ _ (hf i) h (Q.period i n))] -- rewrite likely reverse.
end Coat
end YM.AllOrder.Haiku
