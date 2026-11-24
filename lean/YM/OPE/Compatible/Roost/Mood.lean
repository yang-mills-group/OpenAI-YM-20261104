import YM.OPE.Compatible.Streams.Music
/-!
# single-count transition, ray metric and morphism on Turns. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b u:ℝ}{A:Alps K T i v}{D:Alps K T j v'} {U:Boxes G P' K.K}
local notation "Y!"=>solar G d τ
local notation "T!"=> Tracts G d τ
open JetS
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)
-- x operator Ω.Inv Sch.C.
variable (H hs) (t:Town A D U R u)(h:Aware d τ)(hi:4 ≤ i)(hj:4 ≤ j)
noncomputable abbrev MotionX : Tracts G d τ →L[ℝ] Tracts G d τ:= (Fallix _ h K D.gear hj).symm.toContinuousLinearMap ∘L (yankV D t H hs h∘L (Fallix G h K A.gear hi).toContinuousLinearMap)
lemma HexMood (p:T!) : MotionX H hs t h hi hj (Gift G h p)= Gift G h (MotionX H hs t h hi hj p):=by
     let F:=Fallix G h K A.gear hi; let E:=Fallix G h K D.gear hj; let Y:=MotionX H hs t h hi hj; let W:= yankV D t H hs h; change E.symm (W (F _))= _ ; apply E.injective; rw [E.apply_symm_apply,show F (Gift G h p)= _ from Flick h A.gear hi p]; let v:= F p; have hh : E (Gift G h (Y p))=trellisA G h (W v):=(Flick h D.gear hj (Y p)|>.trans (congr_arg (trellisA G h) (E.apply_symm_apply _))); rw[hh]; exact (pulseA h H hs t v).symm
-- generic lip crossing
lemma lipY (x:Phase)(p:solar G d τ)(hx:∀ i<x,p.val i=0):
    let D:=yankV D t H hs h p; let W:=actor A U R 0 ⟨hs,H,t.eph⟩ h p.val
    (∀ i<x,W i=0)∧∀ i≤ x,D.val i=W i:=by
        intro D W; let R':RollD A U R:=⟨hs,H,t.eph⟩; have hu(i:Phase)(hi:i<x): W i=0:=by
             unfold W; rw [actorA]; apply Finset.sum_eq_zero; intro j _; by_cases he:j<x; rw [hx j he,map_zero]; rw [show Drift.chamber _ _ _ _ _ _ _ _=0 from acceptZ 0 _ _ _ R' h i j (lt_of_lt_of_le hi (le_of_not_gt he))]; rfl
        refine ⟨hu,fun i hi=>?_⟩; change rebase G h _ W i=_; by_cases hx:i=2; swap;· exact sail _ _ _ _ hx
        subst i; rw [Drift.sip,hu 0 (lt_of_lt_of_le (by decide) hi),map_zero,smul_zero,add_zero]
end YM.OPE.Stroke
