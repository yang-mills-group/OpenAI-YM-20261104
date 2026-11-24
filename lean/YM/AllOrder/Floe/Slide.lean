import YM.AllOrder.Floe.Barge
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
-- extra map added under stationary power at positive order. signs explicit. x,y not weight-rescaled.
variable {α:Type*}{L:Finset α}{R:PathData G}{p:Clip}{o:ChartRatio G}{t:S.Choices}
variable {B:ℝ→ Config G f→ℝ}
def spark : E→ℝ:=fun x=> x.1^i.stamp*far F P i x.2
def venue : E→ℝ:= ∑ i∈A, spark F P i
-- operation out of ANY formal policy at order, not assuming R.κ fixed.
abbrev spend (A:Finset Age)(B:ℝ→ Config G f→ℝ)(t:ℝ) : Config G f→ℝ:= B t + ∑ i∈A, sketch P i f t
variable (V:Desk F o B t) (hp:Legal A P)
section rotor
variable {Espace:Type} [NormedAddCommGroup Espace][NormedSpace ℝ Espace] {g:α→Espace→ℝ}
-- notation shadow
lemma goth (h:∀ i∈L, ContDiffAt ℝ ω (g i) 0)(x:Espace)(j:ℕ) : jet (∑ i∈L,g i) j x=∑ i∈L, jet (g i) j x:= by
 induction L using Finset.induction_on with
 | empty=> simp [jet]
 | insert i L hi ih=> rw [sum_insert hi,sum_insert hi]; let hv:=fun i hi=> h i (mem_insert_of_mem hi); rw [jet_add (h i (mem_insert_self ..)) (show ContDiffAt ℝ ω (∑ i∈L,g i) 0 from ?_), ih hv]; exact (by simp_rw [← show (fun x=> ∑ i∈L,g i x)= (∑ i∈L,g i) from funext fun i=> (Finset.sum_apply ..).symm]; exact ContDiffAt.sum hv)
end rotor
include hp
lemma spark_zero (hi:i∈A)(r:ℕ)(h:r < i.e+2):jet (spark F P i) r=0:= by
 have hx:=far_capsule F P A hp hi; ext1 ⟨z,x⟩; exact favor_pocket _ hx.1 _ _ _ _ hx.2 z x i.recovery h
lemma smoothV : ContDiffAt ℝ ω (venue F P A) 0 ∧ (∀ r:ℕ,r ≤ 2 → jet (venue F P A) r=0):= by
 have hh i (h:i∈A) :ContDiffAt ℝ ω (spark F P i) 0:=(contDiffAt_fst.pow _).mul (ContDiffAt.comp (g:=far F P i) _ (far_capsule F P A hp h|>.1) contDiffAt_snd)
 unfold venue; constructor; · rw [← show (fun x=> ∑ i∈A, spark F P i x)=(∑ i∈A,spark F P i) from funext fun x=> (Finset.sum_apply ..).symm]; exact ContDiffAt.sum hh
 intro i hi; ext1 x; rw [goth hh]; refine Finset.sum_eq_zero fun j hj=>?_ ; rw [spark_zero F P A j hp hj i (by have := j.senior; omega)]; rfl
lemma acute:Treaty V.hard V.quiet (V.high+venue F P A) V.paid:= by
 obtain ⟨hx,h⟩:= smoothV F P A hp; refine ⟨V.pay.steer,V.pay.activity.add hx,fun j hj=>?_,V.pay.ample⟩; funext x; rw [jet_add V.pay.activity hx,h j hj,V.pay.rank j hj]; exact add_zero _
lemma palette : ∀ᶠ x in 𝓝 (0:E), 0<x.1 → let U:= represent (Uniform.tint G _ x.2.1); poundA F t (spend P A B) (fun _=> U) x.1 (draw F U x.2.2)* Next.SectorChange.pay o (windmill F x.2.2)= Real.exp (-(V.high x+venue F P A x)/x.1^2)*V.paid x := by
 filter_upwards [V.aff] with x hx hh; obtain ⟨b,y,z⟩:=x; let x':=(b,y,z); let U:= represent (Uniform.tint G _ y); let T:= draw F U z; let W:=F.drape T; intro Q; have hx : poundA F t B (fun _=>U) b T *Next.SectorChange.pay o (windmill F z) = Real.exp (-V.high x' / b^2) * V.paid x':= hx hh
 change poundA F t (spend P A B) _ b T * _= Real.exp (-(V.high x'+venue F P A x')/_)*V.paid x'; rw [show poundA F t _ _ b T=Real.exp (-venue F P A x'/b^2)* poundA F t B (fun _=>U) b T from ?_,mul_assoc,hx,←mul_assoc,← Real.exp_add]
 · exact congr_arg (· * _) (congr_arg Real.exp (by ring)) -- goal? swap
 unfold poundA rootA; rw [← Real.exp_add]; congr 1
 unfold venue; simp_rw [spend,Pi.add_apply,Finset.sum_apply]; let g:= noiseTaylor S U W t; change -(B b W + _+ g)/_= -(∑ i∈A, spark F P i x') /_+ _; change -(B b W + _+ g)/_= -(∑ i∈A, sketch P i f b W) /_+ _ -- `f` shadow! 
 ring
-- mention `r` horizon
noncomputable def augment : Desk F o (spend P A B) t where
 hard:=V.hard
 quiet:=V.quiet
 high:=V.high+venue F P A
 paid:=V.paid
 pay:=acute F P A V hp
 aff:=palette F P A V hp
end YM.AllOrder.Floe
