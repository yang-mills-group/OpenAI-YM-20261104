import YM.OPE.Compatible.Boral.Tip
/-! # care finite moments all testers. κ via densities -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type} {i k m:ℕ}{t C s u z ℓ v a c e r R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
open Lav
section
-- Pu.V Lease structural.L
variable {X:Type}[MeasurableSpace X] (μ:Measure X) (p q:X→Token)
structure AgeT (μ:Measure X)(p:X→Token):Prop where
       Γ (i:Phase): Pu μ (fun x=>(p x).seq i.val)
lemma AgeT.mul (h:AgeT μ p)(hp:AgeT μ q): AgeT μ (p*q):=by
        have hx:=h.Γ 0; have hy:=h.Γ 1; have hZ:=h.Γ 2; have hr:=hp.Γ 0; have ha:=hp.Γ 1; have hc:=hp.Γ 2; constructor; intro i; fin_cases i; · exact timesP hx hr
        · exact addedP (timesP hx ha) (timesP hy hr)
        exact addedP (addedP (timesP hx hc) (timesP hy ha)) (timesP hZ hr)
lemma AgeT.canon [IsProbabilityMeasure μ] (h:AgeT μ p)(he:AgeT μ q)(hs:∀ x,(p x).s=1)(t:ℝ): Speak μ p q= Speak μ (fun i=>p i+(⟨0,0,t⟩:Token)) q:=by
        let f(i:X):Token:= p i+⟨0,0,t⟩; let Z:=ηAvg μ p; let U:=ηAvg μ f; let V:=ηAvg μ (q*p); let W:=ηAvg μ (q*f); have hz:U.s=Z.s:= congr_arg (a_ μ) (funext (show ∀ i,(f i).s=(p i).s from fun _=>add_zero _)); have hl:U.l=Z.l:= congr_arg (a_ μ) (funext (show ∀ i,(f i).l=(p i).l from fun _=>add_zero _))
        have hv:W.s=V.s:= congr_arg (a_ μ) (funext (show ∀ i,((q*f) i).s=((q*p) i).s from fun i=>by change (q i).s*((p i).s+0)=_; rw [add_zero];rfl)); have hW: W.l= V.l:= congr_arg (a_ μ) (funext (show ∀ i,((q*f) i).l=((q*p) i).l from fun i=>by change (q i).s*((p i).l+0)+(q i).l*((p i).s+0)=_; rw[add_zero,add_zero]; rfl))
        have hS:Z.s=1:=by change (∫ i, (p i).s ∂μ)=1; simp [hs]
        have ht:U.h= Z.h+t:= by change (∫ i,(p i).h+t ∂μ)=_; rw [integral_add (show Integrable (fun i=>(p i).h) μ from Irite (h.Γ 2)) (integrable_const _),integral_const,probReal_univ];simp only[one_smul];rfl
        have he₀:V.s=a_ μ (fun i=>(q i).s):= congr_arg (a_ μ) (funext (show ∀ i,((q*p) i).s=(q i).s from fun i=> by change (q i).s*(p i).s=_; rw[hs,mul_one]))
        have hY: W.h= V.h+ V.s*t:=by let g(i:X):= ((q*p) i).h; let F(i:X):=(q i).s*t; rw [show W.h=a_ μ (g+F) from ?_,he₀,Etick (w:=g) (y:=F) (AgeT.mul μ q p he h|>.Γ 2) (timesP (he.Γ 0) (flipP t))]; exact congr_arg (V.h+·) (integral_mul_const _ _);
                                     refine congr_arg (a_ μ) (funext (show ∀ i,((q*f) i).h=(g+F) i from fun i=>?_)); unfold g F f; simp only [Pi.add_apply, Pi.mul_apply,JetS.ml_h]; change (q i).s*((p i).h+t)+(q i).l*((p i).l+0)+(q i).h*((p i).s+0)=_; ring
        change V/Z=W/U; simp_rw [JetS.dv]; apply JetS.eta <;> simp [JetS.ml_s,JetS.ml_l,JetS.ml_h,hl,hW,hv,hY,ht,hz,hS]; ring
end
end YM.OPE.Borealis
