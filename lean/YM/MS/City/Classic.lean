import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Odelta
import YM.MS.City.Routes
/-!
# Smooth real Landau lengths and the canonical shell

Recovery `table` polynomial T. Includes gauge charge at birth. Does not close anomalies. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.City
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Cylinder Lab Landau Native Lattice Tone Momentum Heat Real Frame
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{P A : Type}(F:Dot G Cover)
-- absolute shell
abbrev BH (G:Gauge):= Branch G Axis
abbrev Z (G:Gauge):= send (C:=G.ColorIndex) (wave (A:=Axis))
abbrev Cpu (G:Gauge) := LegsK (A:=G.ColorIndex) (wave (A:=Axis))
abbrev Mood (G:Gauge) := LegsX (A:=G.ColorIndex) (wave (A:=Axis))
abbrev Then (G:Gauge) (r:ℝ): Flux (BH G) QP ℂ:= (Z G).change (Cpu G r)
lemma localeX (G:Gauge) (r:ℝ): Then G r=LegsY wave r:= given wave r wave_neg

variable (G:Gauge)
lemma X_even (r:ℝ): closed (Cpu G r) parity false:= closure _ (L_cl r)
lemma X_odd (r:ℝ): closed (Mood G r) parity true:= closure _ (laplace_cl _)
lemma Y_odd (r:ℝ): closed (Then G r) parity true:= localeX G r ▸ (closure wave (laplace_cl _))
lemma Vrev (r:ℝ): Reverse (Cpu G r) parity:= reverse_one wave (L_rev r) wave_neg
lemma Xrev (r:ℝ): Reverse (Mood G r) parity:= reverse_one wave (X_rev r) wave_neg
lemma f_der (r:ℝ): Jet (Mood G) (Then G r) r:= by rw [localeX]; intro i j q; simp only [LegsX,Mood,LegsY,Landau.choir]; by_cases h:i.2=j.2; simp_rw [if_pos h]; exact lap_der ..; simp_rw [if_neg h]; exact hasDerivAt_const ..
lemma Yrev (r:ℝ): Reverse (Then G r) parity:= by
   intro i j x; have h: (fun t=> Mood G t i j (-x))=fun t=> cross (parity i) (parity j)*Mood G t j i x:= funext fun t=> Xrev G t i j x
   have hv:= f_der G r i j (-x); rw [h] at hv; exact hv.unique ((f_der G r j i x).const_mul _)
-- Smooth all Euclidean Q
private lemma of_real {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (g:E→ℝ)(h:ContDiff ℝ ∞ g): ContDiff ℝ ∞ (fun x=> (g x:ℂ)):= Complex.ofRealCLM.contDiff.comp h
lemma flowSmooth (u v:BH G): ContDiff ℝ ∞ ((Z G).table u v):= by have hv:= criterion (R:=High.meet) (primary_large High.s_gain.le)|>.cost u v; exact hv.lat.smooth (High.meet.start 0)
lemma paintWave : ContDiff ℝ ∞ (fun x:ℝ×QP=> wave x.2):= by unfold wave theta; apply contDiff_pi.mpr; intro; simp only [Function.comp_apply]; fun_prop
lemma brush_flex : ContDiff ℝ ∞ fun x:ℝ×QP=> brush x.1 (wave x.2):= by
    unfold brush Momentum.sq wave theta; simp only [Function.comp_apply]; fun_prop (disch:=assumption) -- `paintWave` hint
lemma norm_flex : ContDiff ℝ ∞ fun x:ℝ×QP=> Momentum.sq (wave x.2):= by
    unfold Momentum.sq wave theta; simp only [Function.comp_apply]; fun_prop (disch:=assumption)
lemma comp_flex (i:Axis): ContDiff ℝ ∞ fun x:ℝ×QP=> wave x.2 i:= contDiff_pi.mp paintWave i
lemma prec_flex (i j:Axis): ContDiff ℝ ∞ fun x:ℝ×QP=>precision i j (wave x.2):= by
    unfold precision delta; split; exact norm_flex.sub ((comp_flex i).mul (comp_flex j)); exact contDiff_const.sub ((comp_flex i).mul (comp_flex j))
lemma main_f : flex (Cpu G):= by
    intro i j; dsimp only [Cpu, LegsK, Landau.choir]; by_cases he:i.2=j.2; swap; · simp_rw [if_neg he]; exact contDiff_const
    simp_rw [if_pos he]; rcases i with ⟨⟨_|i,_|_⟩,t⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,u⟩ <;> first| exact contDiff_const| (simp only [L0]; first| exact of_real _ (brush_flex.mul (prec_flex ..))| exact contDiff_const.mul (of_real _ (brush_flex.mul (norm_flex.mul (comp_flex _)))))
lemma low_f : ContDiff ℝ ∞ fun x:ℝ×QP => low x.1 (wave x.2):= by
    unfold low coat; simp only [pow_zero,one_mul, scaling]; apply ContDiff.mul _ (ContDiff.exp _); exact contDiff_const.add ((contDiff_fst.pow 2).mul norm_flex); exact ((contDiff_fst.pow 2).mul norm_flex).neg
lemma mood_f : flex (Mood G):= by
    intro i j; dsimp only [Mood, LegsX, Landau.choir]; by_cases he:i.2=j.2; swap; · simp_rw [if_neg he]; exact contDiff_const
    simp_rw [if_pos he]; rcases i with ⟨⟨_|i,_|_⟩,t⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,u⟩ <;> first| exact contDiff_const| (simp only [X0,laplace,delta]; first| exact (of_real _ low_f).neg.div_const _ | (split_ifs <;> first | exact (of_real _ low_f).div_const _| exact contDiff_const))
lemma then_f : flex (Then G):= by
    let X i j : ContDiff ℝ ∞ fun x:ℝ×QP=> (Z G).table i j x.2:= (flowSmooth G i j).comp contDiff_snd; let Y i j : ContDiff ℝ ∞ fun x:ℝ×QP=> (Z G).table i j (-x.2):= (flowSmooth G i j).comp contDiff_snd.neg;
    intro i j; unfold Then Charge.change; apply ContDiff.add; exact ContDiff.sum (fun j _=> (main_f G _ _).mul (X ..)); exact ContDiff.sum (fun j _=> contDiff_const.mul ((main_f G _ _).mul (Y ..)))

lemma cour0 : Cour μzone:= by
   letI : ProperSpace QP:= FiniteDimensional.proper ℝ QP
   exact ⟨_,isCompact_closedBall _ _, by exact (ae_restrict_mem measurableSet_closedBall)⟩
lemma run_this (F:Dot G Cover): TouchF (fun _=> run F):= by
    intro E _ _ f w hw h; induction w generalizing F with
    | nil=> exact contDiff_const
    | cons a w ih=>
       obtain ⟨s,hs⟩:=obliges F; simp_rw [show ∀ x:E, walk0 (a::w) x=(a.1,a.2 x)::walk0 w x from fun x=>rfl, grows F hs]; refine ContDiff.sum (fun i _=>ContDiff.mul ?_ (ih _ hw.rest))
       unfold bill pairing; have hv:= hw a (by simp); refine ContDiff.cexp (ContDiff.mul contDiff_const (of_real _ (ContDiff.sum fun j _=> ((contDiff_pi.mp hv) j).mul contDiff_const)))
end YM.MS.City
