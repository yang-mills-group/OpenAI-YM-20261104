import YM.AllOrder.Floe.Dawn
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
variable (F:Forest S.ratio)(P:Layout G)(A:Finset Age)(i:Age)
local notation "Y"=>Poll.Body (Precision.Key F G)
local notation "X"=>Apex c G×Y
local notation "E"=>ℝ×X
variable {α:Type*}{L:Finset α}{R:PathData G}{p:Clip}{o:ChartRatio G}{t:S.Choices}
variable {B:ℝ→ Config G f→ℝ}
variable (V:Desk F o B t) (hp:Legal A P)
open PertExtension GaussianScore
local notation "q"=> fderiv ℝ V.quiet 0
local notation "U"=>Impulse (q) V.high V.paid
def books := Impulse (fderiv ℝ V.quiet 0) (V.high+ venue F P A) V.paid
local notation "U₁"=> books F P A V
variable (l:Finset Age)
local notation "u"=> books F P l V
local notation "d"=> castle V.hard V.quiet V.pay.steer
include hp
variable {i}
def note_n : ℕ→ X→ℝ:=spine (fderiv ℝ V.quiet 0) (spark F P i) 2
include i
lemma frost_at (h:i∈A)(hj:j < i.e): note_n (i:=i) F P V j=0:= by ext1 x; unfold note_n spine; rw [spark_zero F P A i hp h (j+2) (by omega)]; rfl
def goldL (i:Apex c G→L[ℝ] Y):X →L[ℝ] X:= (ContinuousLinearMap.fst ..).prod ((i ∘L ContinuousLinearMap.fst ℝ (Apex c G) Y)+ContinuousLinearMap.snd ℝ (Apex c G) Y)
lemma lush (hx:i∈A) (hj:i.e≤j): note_n (i:=i) F P V j= jet (far F P i) (j-i.e+i.r) ∘ goldL F (q):= by
 ext1 x; have he:=far_capsule F P A hp hx; unfold note_n spine; change jet (spark F P i) (j+2) (1,(goldL F (q)) x)= _; rw [show jet (spark F P i) (j+2) _=_ from favor_exp (far F P i) he.1 1 ((goldL F (q)) x) (j+2) i.stamp]; rw [if_pos (show i.stamp ≤ j+2 from (by have := i.recovery; omega)), one_pow,one_mul,show j+2-i.stamp=j-i.e+i.r by have := i.recovery; omega]; rfl
omit i
lemma amber (j:ℕ) : U₁ j= (U j) - ∑ i∈A, note_n (i:=i) F P V j:= by
 by_cases hi:j=0; subst j; rw [books,Impulse,Impulse,win0,win0]; rw [Finset.sum_eq_zero (fun i hi=> frost_at F P A V hp hi (by have ht:=i.senior; omega)),sub_self]; -- implicit i inserted order check
 rw [books,Impulse,Impulse,win_atn _ hi,win_atn _ hi]; ext1 x; let hR:=V.pay.activity; let w:=colorful (q) x; rw [Pi.sub_apply,Finset.sum_apply]; unfold token; change _- jet (V.high+venue F P A) (j+2) w= (jet (Real.log ∘ V.paid) _ w -jet V.high _ w)- _; rw [jet_add hR (smoothV F P A hp|>.1),venue,goth (fun i hi=> (show ContDiffAt ℝ ω (spark F P i) 0 from (contDiffAt_fst.pow _).mul (ContDiffAt.comp (g:=far F P i) (f:=Prod.snd) (0:E) (far_capsule F P A hp hi|>.1) contDiffAt_snd))) w (j+2)]; change _= _ - ∑ i∈A, jet (spark F P i) (j+2) w; unfold spine w; rw [Nat.add_zero]; abel
variable (hl:l⊆ A) (he:∀ i∈ A,i∉l→ k ≤ Age.e i)
include hl
lemma legal_less : Legal l P:= ⟨fun i hi=> hp.rent _ (hl hi),fun i hi=> hp.symm _ (hl hi)⟩
include he
lemma precede (hj:j<k) : U₁ j=u j:= by
 have h i (hi:i∈A) (hz:i∉l) : note_n (i:=i) F P V j=0:= frost_at F P A V hp hi (hj.trans_le (he _ hi hz)); rw [amber F P A V hp _,amber F P l V (legal_less P A hp l hl), Finset.sum_subset hl h] -- order

set_option quotPrecheck false
local notation "B'"=> (EuclideanSpace.basisFun (Precision.Key F G) ℝ).toBasis
lemma orient (hj:j<k): distilled (augment F P A V hp) j= distilled (augment F P l V (legal_less P A hp l hl)) j:= by
 have hx : arrowR (d) volume U₁ j=arrowR (d) volume u j:= by
    obtain ⟨L,h,hV⟩:= proviso (d) B' volume («u»:=U₁) (v:=u) (win0 _) (win0 _) (fun i=>impulse_rank ..) (fun i=>impulse_rank ..) (fun j hj=>precede F P A V hp l hl he hj) hj; exact h.trans hV.symm
 funext x; change Response.connected (d) volume U₁ j _=Response.connected (d) volume u j _
 rw [← final_hot _ volume («u»:=U₁) (win0 _) (fun i=>impulse_rank ..), ← final_hot _ volume («u»:=u) (win0 _) (fun i=>impulse_rank ..)]; unfold Fire.booked; exact congr_arg (fun f:(Book X)=> (∑ i∈ range (3*j+1), f i) (x,0)) hx
end YM.AllOrder.Floe
