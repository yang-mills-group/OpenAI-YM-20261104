import YM.OPE.Compatible.Nut.Oak
import YM.OPE.Compatible.Docks.Sco
/-! # pan book scales before accepting. interior selection -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lass
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*}{j i k m n B:ℕ}{R v t s u r:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Borealis Borealis.Galea Borealis.Lav
variable {K:Sponsor G}{T:Seasons K}
namespace Zest
section
open Source Labels Extra.Multi
variable {n:Side}{k b:ℕ}{X: Labels.Frame G k} (S:SectionData X)(o:Site n) {R:Rep G n}{h:Hol G}{a b' c:ℝ}
open Extra.Histories
variable {S o}(K:KernelChoices)(v:Train i)(hz:4 ≤ i)(P: Spells.Pad G)(U:BudgetPoint) (f:X.Coeff→ Config G n→ℂ)(x:Site n)
variable (h:2*(b+1)<n.val)(t:ℝ){τ:Phase→ℕ}{w:X.Coeff→ℝ}
variable (hp:IsLinearMap ℂ f)(hR:∀ i,Acceptance x U j (f i) b (w i))(H:Aware j τ)
noncomputable abbrev Hon (a:X.Coeff)(bq:ℂ→L[ℝ]ℝ):=Artifact x P h U (f a) bq t
noncomputable abbrev Lark (A:ℂ→L[ℝ]ℝ) (a:X.Coeff):= ChiselV H (Recon x P h U (f a) A K v hz t (hR a))
private lemma milk (a:ℝ) (w z:ℂ)(B:ℂ→L[ℝ]ℝ) : B (a • (w+z))=B (a • w)+B (a • z):=by rw [smul_add,map_add]
local notation "Γ"=> Lark K v hz P U f x h t hR H
local notation "μ"=> Hon P U f x h t
include hp hR
lemma ActorS (B:ℂ→L[ℝ]ℝ) : IsLinearMap ℝ (Γ B):=by
        constructor
        · intro i j; unfold Lark ChiselV; rw[← (crestL G _ 0).map_add]; apply congr_arg; apply Locke; apply Care; have he:f (i+j)=f i+f j:= hp.map_add ..; funext u; unfold Artifact LaunchB HeadU; simp only [he,Function.comp_apply,Pi.add_apply]; exact milk _ _ _ _
        intro a i; unfold Lark ChiselV; rw [← (crestL G _ 0).map_smul]; apply congr_arg; apply LockA; apply CareS; let T:=hp.mk' f; have he:f (a • i)=a • f i:= (T.restrictScalars ℝ).map_smul ..; funext u; unfold Artifact LaunchB HeadU; simp only[he,Function.comp_apply,Pi.smul_apply]; rw[smul_comm,_root_.map_smul]
lemma κbridge (k0:X.Coeff) : Γ Complex.reCLM (Complex.I • k0)= -(Γ Complex.imCLM k0)∧ Γ Complex.imCLM (Complex.I • k0)=Γ Complex.reCLM k0 :=by
       have he:f (Complex.I • k0)=Complex.I • f k0:= hp.map_smul ..; have hp(q:Config G n):f (Complex.I • k0) q=Complex.I*f k0 q:=congr_fun he q
       constructor
       · rw [show -(Γ Complex.imCLM k0)=(-1:ℝ) • Γ Complex.imCLM k0 from (neg_one_smul ..|>.symm)]; unfold Lark ChiselV; rw [← (crestL G _ 0).map_smul]; apply congr_arg; apply LockA; apply CareS; funext u; unfold Artifact LaunchB HeadU; simp only[Function.comp_apply, he,Pi.smul_apply]; simp
       rw [show Γ Complex.reCLM k0=(1:ℝ) • Γ Complex.reCLM k0 from (one_smul ..|>.symm)]; unfold Lark ChiselV; rw [← (crestL G _ 0).map_smul]; apply congr_arg; apply LockA; apply CareS; funext u; unfold Artifact LaunchB HeadU; simp only[Function.comp_apply,he,Pi.smul_apply]; simp
-- tie to complex note
open Yolk
variable (y:X.Coeff)
lemma Θc : (Γ Complex.reCLM y,Γ Complex.imCLM y)= Arco (fun j=> (Γ Complex.reCLM (CastX (X:=X) j),Γ Complex.imCLM (CastX (X:=X) j))) y:=by
       let a:= Γ Complex.reCLM; let b':= Γ Complex.imCLM; let A: X.Coeff→ₗ[ℝ] _:= ((ActorS _ _ _ _ _ _ _ _ _ hp hR H Complex.reCLM).mk' a).prod ((ActorS _ _ _ _ _ _ _ _ _ hp hR H Complex.imCLM).mk' b'); have hv(v:X.Coeff): A v=(a v,b' v):= rfl; have hh(c:ℂ)(x':X.Coeff): A (c • x')= Az (A x') c:=by
             have hΩ:A (Complex.I • x')= (-b' x',a x'):= Prod.ext (κbridge K v hz P U f x h t hp hR H x').1 (κbridge K v hz P U f x h t hp hR H x').2
             rw [show c • x'=c.re • x'+ c.im • (Complex.I • x') from ?_,map_add,_root_.map_smul,map_smul,hΩ];rfl
             nth_rw 1 [← Complex.re_add_im c]; rw [add_smul, mul_smul]; congr 1
       let e:=CastX (X:=X); have hY:y=∑ i:X.Index,y i • e i:= funext fun i=> by simp [Finset.sum_apply,e, CastX,Pi.single_apply]
       rw [bWire,←hv y,show A y= _ from congr_arg (fun y=>A y) hY,map_sum]; exact Finset.sum_congr rfl fun i _=>hh ..
end
end Zest
end YM.OPE.Lass
