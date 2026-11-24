import YM.AllOrder.Floe.Forty
import YM.AllOrder.Floe.Era
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j w N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}
namespace Aero
open Bloch Extra.Iteration Pace StateE Exterior Bid
variable {ι:Type} {Ω T:ι→ℝ} {a ε μ δ w:ℝ}{k l:ℕ}
local notation "Y"=> Ink.Money.Bills (Coarse G)
variable {X:ι→ Ink.Money.Bills (Coarse G)}(H: ∀ i,Haiku.Coat.Admits (X i))(B:ι→Bed) {R:ι→PathData G}{q : Clip}
variable (g:G.Simple) (hx:∀ i,(B i).metric.strip μ C) (hA:∀ i, Attached (B i) (R i))(hh:∀ i n,Floor (B i) q n ε δ)(hs:∀ i n,Bid.Sworn (B i) n G)(he:∀ i,(R i).Bounds q a w (Ω i))
-- refund.Down full base Hessian. With Grade heights. revive from velocity1 only.
section above
variable (p:Clip)(V:PathData G) (h:V.Bounds p σ C Z)
include h
lemma headTwo : jet (Stationary.intended p V (m:=n)) 2=jet (inputSeries p V (m:=n)) 2:= by
 let A:= inputSeries p V (m:=n); let s:= turnSeries (m:=n) V.cubic; let t:=turnSeries (m:=n) V.quartic; let hp:= stain_knit (m:=n) V p h; have hs:= turns_analytic (m:=n) V.cubic h.width h.three; have ht:=turns_analytic (m:=n) V.quartic h.width h.four
 rw [intent]; funext x; rw [jet_add (show ContDiffAt ℝ ω (A+s) 0 from hp.analytic.contDiffAt.add hs.contDiffAt) ht.contDiffAt, jet_add hp.analytic.contDiffAt hs.contDiffAt];
 have h0(k:ℕ) (v:ℕ→Atom G k)(hf:Extra.Iteration.Charged v σ C)(he:2<k): jet (turnSeries v) 2 x=0:= by unfold jet; rw [(rays_jet (turns_analytic _ h.width hf) _).1 (turns_low _ h.width hf) 2 he]; simp
 rw [h0 _ V.cubic h.three (by decide), h0 _ V.quartic h.four (by decide),add_zero,add_zero]
include g
lemma spry : Haiku.Coat.Admits (Pace.base p V 0) := let H:= Pace.base_pose (N:=0) p V h g; votes (fun i=> H _ le_rfl i |>.2) (fun n i hi=>by omega) (fun n=> (H _ le_rfl n).1.read)
end above
include hh he hA hs hx
lemma living (i:ι)(n:Side)(hμ:0<μ) : Recorded (slots (B i).metric G) (Pace.base q (R i) 0 n) 0:= by
 have hp : Recorded (slots (B i).metric G) (inputSeries q (R i) (m:=n)) 0:= according ((B i).metric.rights μ C (hx i) hμ.le) (low_columns (he i) (hA i) (hh i n) (hs i n)).2.2
 rw [show Pace.base q (R i) 0 n=jet (intended q (R i) (m:=n)) 2 from rfl,headTwo q (R i) (he i)] -- syntax
 exact remake _ _ (Haiku.Project.self _ ((stain_knit (m:=n) (R i) q (he i)|>.analytic).contDiffAt) 2).symm hp
omit hh he hA hs hx
def Capped (T:Y) (k:ℕ)(V : ℕ→ Atom G k):=∀ n,jet (T n) k=jet (turnSeries V (m:=n)) k
-- width selection relevant rank. Choose exterior options, monotone. combine
open Haiku.Coat Stationary.Haiku
-- high grant from `strokes` on rank≥3 via colors_t.No quota.Heights.
def Castle (G: Gauge)(u v:ℝ)(r:ℕ): Prop:=∀ (ι:Type)(L:ι→ℝ)(l:ℕ)(X:ι→Ink.Money.Bills (Coarse G)), money L X (r-1) l u→(∀ i,Admits (X i)) →∃ f:ι→ℝ,CreditF L l f∧∃ F:ι→ℕ→Atom G r,∀ i,Quoted (F i) v (f i) ∧ Capped (X i) r (F i)
lemma towersK (G:Gauge) (u:ℝ) (t:ℕ)(hu:0<u) (hr:3≤t): ∃ a:ℝ,0<a∧∀ v,0<v→v≤a→Castle G u v t:= by
 obtain ⟨r,hr'⟩:= Nat.exists_eq_add_of_le hr; -- hr' inspect
 have hj : t=r+3:= by omega
 clear hr'; subst t
 obtain ⟨a,A,h,hL,hA,H⟩:=strokes G (r+2) (by omega) u hu; refine ⟨a,h,fun v hv he ι L l X hh hx=>?_⟩
 obtain ⟨f,p,hp,hT,hF⟩:= (show money L X (r+2) l u from hh); let M:PictureT L X (r+2):=⟨f,u,p,hu,hp.grade,hF,fun i n=> hT n i⟩; choose g hG using fun i=>H (p i) (f i) (hp.nonneg i) (colors_t M hx i);
 refine ⟨_,((hp.mul (freeC A hA)).mul (freeC (inkCost G (r+2) a) (inkCost_nonneg ..))), (fun i=>issue (g i)),fun i=> ⟨?_,?_⟩⟩
 · obtain ⟨h,i⟩:= artery_funded (hG i); exact ⟨Extra.Iteration.Charged.mono h he le_rfl,i,fun hk=>by omega⟩
 intro n; ext1 x; unfold jet; rw [aperture_eq (colors_align _ (hx i|>.rise n) ((hx i).rotate n) _ _ (hG i) h (hT n i))]

def June (G:Gauge) (v u C:ℝ) := ∀ (ι:Type) (L:ι→ℝ)(l:ℕ) (F T:ι→Ink.Money.Bills (Coarse G)) (X:ι→Bed),
   money L F 1 l v → (∀ i,Admits (F i))→ (∀ i, Admits (T i))→
   (∀ i,(X i).metric.strip v C∧(X i).metric.read 0=1) → (∀ i n, Recorded (slots (X i).metric G) (T i n) 0)→
      ∃ (α:ι→ℝ) (f:ι→ℝ) (K:ι→ℕ→Atom G 2), Pace.Cost L l α ∧ CreditF L l f ∧∀ i,Quoted (K i) u (f i)∧ Capped (F i-α i • T i) 2 (K i)
lemma july (G:Gauge)(g:G.Simple)(v C:ℝ)(hv:0<v)(hC:0≤C):∃ u:ℝ,0<u ∧ ∀ x,0<x→x≤u→June G v x C:= by
 obtain ⟨μ,M,hμ,hV,hM,H⟩:= Aero.alive G g (σ:=v) (M:=C) hv; refine ⟨μ,hμ,fun x hx ht ι L l F T X hh hf hT hX hR=>?_⟩
 obtain ⟨p,f,hF,hp,hψ⟩:=hh; let b:= Classical.choice (colorAvail G g); let α(i:ι):= alphaPay b (p i); let B(i:ι):= f i+|α i| *bedCharge v C; have ha:0≤tollN v:= by unfold tollN; positivity
 have hA : Pace.Cost L l α:= CreditF.down (hF.mul (freeC _ ha)) (fun i :ι=> alpha_fee (hψ i) b) (fun i:ι => abs_nonneg _)
 choose K hK hY hω hz using fun i=> H _ _ (f i) (p i) b (X i).metric (hX i).1 (hX i).2 (hF.nonneg i) hC (hψ i) (hf i) (hT i) (fun n=>hp n i) (hR i);
 refine ⟨α,(fun i=> B i*M),K,hA, (hF.add ((show CreditF L l (fun i=> |α i|) from hA).mul (freeC _ (bedCharge_nonneg (σ:=v) hC)))).mul (freeC _ hM),fun i=>⟨⟨Extra.Iteration.Charged.mono (hK i) ht le_rfl,hY i,fun _=> hω i⟩,hz i⟩⟩
end Aero
end YM.AllOrder.Floe
