import YM.OPE.Compatible.Gems.Count
/-! # Finite cluster Leg arrays with color, polynomial. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m:ℕ}{t C s u z ℓ v a c e r R ε:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable (L:Host K T) (Y:Studio L) (J:Finset (Rubric G Y.X))
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
abbrev RodZ (L:Host K T)(k:ℕ):= Fin k→ Drive L
noncomputable def Gale (g:RodZ L k): Y.St→ℝ:=∏ i:Fin k,PulseP L Y (g i)
noncomputable abbrev Βuffs (G:Gauge)(s c C n:ℝ):price:= fun i=> 2*(((n*Real.sqrt (limbC G s c))*C)*ampleP i)
omit J in lemma Bsafe (x:RodZ L k)(h:L.Rich s c e v u C)(ht:0 < s)(hc:0 ≤c)(he:0< e)(hv:Scale Y t) : Cane Y.μφ (Gale L Y x) (hikeP (FWind G s c u C t) k):=by
       have hx:= dotP (Finset.univ:Finset (Fin k)) _ (fun i _=> TinV h ht hc he hv (x i)); rwa [card_univ,Fintype.card_fin] at hx
lemma Broad (x: RodZ L k)(h:∀ i:Fin k,Hst L Y J (x i)): overT L Y J (Gale L Y x):=by
       choose f hf using fun i:Fin k=> Visa L Y J (x i) (h i); refine ⟨∏ i,f i,?_⟩; unfold Gale; simp_rw [hf]; funext y; simp only[Finset.prod_apply, Function.comp_apply]
lemma Fare (p:RodZ L k) (h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0 < e)(hv:Scale Y t)(hp:∀ i,remote L Y J (p i) ℓ)(hh:(J.card:ℝ)≤ z): telemetry Y J (Gale L Y p) (hikeP (FWind G s c u C t) k) (reelP (FWind G s c u C t) (Βuffs G s c C z) k) (Real.exp (-(u*ℓ))):=by
        refine ⟨Bsafe L Y p h ht hc he hv,?_⟩
        let f(i:Fin k):=PulseP L Y (p i); let A:=(Finset.univ:Finset (Fin k)); let μ':= mirror L Y; let V(i:Fin k):= wanY Y (f i); let W(i:Fin k):=tanY Y J (f i); have he'(i):= TinV h ht hc he hv (p i); let b:= FWind G s c u C t; have hx(i:Fin k): Cane μ' (V i) b:=fun j hj=> fst_F _ (νMom L Y) (f i) ((he' i) j hj); have hw(i:Fin k): Cane μ' (W i) b:= fun j hj=> Swear.u_F (Hκ L Y) (νMom L Y) _ _ (scene _ _ (pros L Y J)) (f i) ((he' i) j hj); let D:= ΤΙ G s c C u ℓ z; have X:= craftP A V W (μ:=mirror L Y) (fun i _=>hx i) (fun i _=>hw i) (D:=D) (fun i _=> journey h ht hc he _ (hp i) hh); rw [show wanY Y (Gale L Y p)=∏ i,V i from ?_,show tanY Y J (Gale L Y p)=∏ i,W i from ?_];  have hZ : D=Real.exp (-(u*ℓ)) • Βuffs G s c C z:=by funext i; unfold D ΤΙ; rw[Pi.smul_apply,smul_eq_mul];unfold Βuffs;ring
        rw [← re_s,←hZ ] -- error rewrites types dependent
        · have hv:=X; rw [show A.card=k by simp [A]] at hv; exact hv
        · funext i; unfold W Gale f tanY; simp only [Finset.prod_apply,Function.comp_apply]
        funext i; unfold Gale V f wanY; simp only [Finset.prod_apply,Function.comp_apply]
end
end YM.OPE.Borealis.Galea
