import YM.OPE.Compatible.Fiord.Voss
/-! # Cost transport into orthogonal cube. Projection preserves Hardy plateau. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
set_option maxHeartbeats 200000
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
open Jargon
open Merchant.SiteL
variable {E X:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
variable (R:E→L[ℝ] X)(H:X→ₗ[ℝ] Dual' X)(P:Law E)(B:Law X) (h:SiteL R H P)
-- Completer cochain (may singular H). require supported probes in range. P hull positive.
def Favorable (q:Dual' X):Prop := H (B.inverse q)=q
abbrev ExtL (q:Dual' X): Dual' E:= q.comp R.toLinearMap
lemma envoyX (q:Dual' X)(hp:Favorable H B q): P.inverse (ExtL R q)=pour R H P (B.inverse q):=by
       change _=P.inverse _; apply congr_arg (P.inverse); exact DFunLike.ext _ _ (fun i=>by change q (R i)= H (B.inverse q) (R i); rw [hp])
noncomputable abbrev ashP (q:Dual' X): Dual' X:=(ExtL R q).comp (pour R H P).toLinearMap
include h in lemma colorPX (q:Dual' X): ashP R H P q=H (R (P.inverse (ExtL R q))):=by
        let v:=ExtL R q; ext i; change v (pour _ _ _ _)= _; rw[h.hike (R _) _,loan R H P, P.turns, Law.applies]
lemma moodXP (q:Dual' X)(hp:Favorable H B q)(f:Dual' X):B.wick q (ashP R H P f)= P.wick (ExtL R q) (ExtL R f):=by -- no h needed? envoy didn't need
        unfold Law.wick; let g:= ExtL R f; change g (pour _ _ _ _)=g _; rw [←envoyX R H P B q hp] -- signature
local notation "A0!"=> ashP R H P
include h
lemma aspect (L:∀ x:X,Favorable H B (H x))(p q:Dual' X)(hp:Favorable H B p)(hq:Favorable H B q):
        let F:= (mate R H P).toLinearMap
        B.wick (p.comp F) (q.comp F)+P.wick (ExtL R p) (ExtL R q)= B.wick p q:=by
           intro F; let e:=ExtL R p; let f:= A0! p; let t:=ExtL R q; let g:=A0! q; have he:Favorable H B f:=by unfold f; rw [colorPX R H P h]; apply L
           have ht : ExtL R f=e:=by ext i; change p (R (pour R H P (R i)))=p (R i); rw[SiteL.pillar _ _ _ h]
           have h1 : B.wick p g=P.wick e t:=moodXP R H P B p hp q; have h2:B.wick f q=P.wick e t:= (wickTurn B f q).trans ((moodXP R H P B q hq p).trans (wickTurn P t e)); have h3:B.wick f g=P.wick e t:=by rw [show B.wick f g= P.wick _ _ from moodXP R H P B f he q,ht]
           have hz(u:Dual' X): u.comp F=u-A0! u:=by ext1 x; change u (x-R (pour R H P x))=_; rw [map_sub];rfl
           rw [hz,hz]; change B.wick (p-f) (q-g)+_= _; rw [show B.wick (p-f) (q-g)= B.wick p q-B.wick f q -(B.wick p g-B.wick f g) from ?_,h1,h2,h3]; ring; unfold Law.wick; rw [LinearMap.sub_apply,map_sub,map_sub,map_sub] -- no? rw sub
end YM.OPE.Merchant
