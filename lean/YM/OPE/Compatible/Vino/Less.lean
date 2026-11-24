import YM.OPE.Compatible.Vino.Cut
import YM.OPE.Compatible.Vino.Bliss
/-!
# currencies; energy op as dense frames. cut kinematics
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m:ℕ}
variable {K:Sponsor G}{T:Seasons K}{v b:ℝ}
-- Script lifting p tickets
noncomputable def pointer (G:Gauge)(d:ℕ)(a:Phase)(m:ℕ): Seat (d+a.val) m (Shade G)→ₗ[ℝ] Muse G:= LinearMap.single ℝ (fun _:Phase=> Curtain (Shade G)) a ∘ₗ (lilies m (d+a.val) (Shade G))
lemma pointerX (a:Phase)(x: Seat (d+a.val) m (Shade G)): pointer G d a m x= impulse a (lilies m (d+a.val) _ x):=rfl
lemma pointerFee (a:Phase)(x: Seat (d+a.val) m (Shade G)): Tide (pointer G d a m x) d m ‖x‖:= nip _ _ _ _ _ (sproutV ..)
variable (P:Patch) (C:KernelChoices)(A:Alps K T i v)(U:Boxes G P C)(R:ChartRatio G)(b:ℝ)
variable (h:Era U A) (hs:G.Simple)(ht:LocalRatio R)(hm:45 ≤ m)
include h hs hm ht
lemma karst (w:ℝ)(hw:Paid P C U A R m 1 d w b) (hr:0≤w)(a y:Phase):∃ V: Seat (d+a.val) m (Shade G)→L[ℝ] Seat (d+y.val) m (Shade G), ‖V‖≤w∧∀ x, lilies m (d+y.val) _ (V x)= sculpt P C U A R b (pointer G d a m x) d y:=by
     let B:= pointer G d a m; let z(x):= sculpt P C U A R b (B x) d; have hp(x:Seat _ _ _):Tide (B x) d m ‖x‖ := pointerFee a x; have he(x):Tide (z x) d m (w*‖x‖):= established P C U A R b hs hw h (B x) _ (hp x)
     let g(x):=fundus (z x y) (w*‖x‖) (he x y); have hv (x): lilies m (d+y.val) _ (g x)=z x y:= sproutsX _ _; have hh:= lilies_inj (Shade G) (d+y.val) m
     let K:Seat (d+a.val) m (Shade G) →ₗ[ℝ] Seat (d+y.val) m (Shade G):= { toFun:=g, map_add' x v:=hh (by rw [hv, map_add,hv,hv]; unfold z;rw [map_add,levy P C U A R b h hs ht hm (hp x) (hp v)];rfl), map_smul' v x:=hh (by rw [hv,map_smul,hv]; unfold z; rw [map_smul,levee P C U A R b h hs ht hm v (hp x)]; rfl) }
     have hvv(x):‖K x‖≤w*‖x‖:= sproutsU _ (he x y); let V:=K.mkContinuous w hvv; exact ⟨V,V.opNorm_le_bound hr hvv,hv⟩
noncomputable def sectorOp (hm:45≤m)(d:ℕ)(a y:Phase) (hs:G.Simple) (h:Era U A)(ht:LocalRatio R) : Seat (d+a.val) m (Shade G)→L[ℝ] Seat (d+y.val) m (Shade G) := (karst P C A U R b h hs ht hm _ ((liquidity P C U A R hs ht (m:=m) (j:=1) hm b).choose_spec.2) ((liquidity P C U A R hs ht (m:=m) hm b).choose_spec.1) a y).choose
lemma publicity (d:ℕ)(a y:Phase)(x): lilies m (d+y.val) _ (sectorOp P C A U R b hm d a y hs h ht x)=sculpt P C U A R b (pointer G d a m x) d y:=Exists.choose_spec (karst P C A U R b h hs ht hm _ ((liquidity P C U A R hs ht (m:=m) (j:=1) hm b).choose_spec.2) ((liquidity P C U A R hs ht (m:=m) hm b).choose_spec.1) a y)|>.2 x
lemma publicFee (w:ℝ)(hw:Paid P C U A R m 1 d w b)(hr:0≤w)(a y:Phase): ‖sectorOp P C A U R b hm d a y hs h ht‖≤w:=by
      obtain ⟨V,hV,hx⟩:=karst P C A U R b h hs ht hm w hw hr a y
      have hv: sectorOp P C A U R b hm d a y hs h ht=V:= ContinuousLinearMap.ext fun i=>lilies_inj (Shade G) (d+y.val) m ((publicity P C A U R b h hs ht hm d a y i).trans (hx i).symm)
      rw [hv]; exact hV
lemma shadowZero (d:ℕ)(x y:Phase)(hy:y<x) : sectorOp P C A U R b hm d x y hs h ht=0:=by
       apply ContinuousLinearMap.ext; intro u; let O:=sectorOp P C A U R b hm d x y hs h ht; have hv:= publicity P C A U R b h hs ht hm d x y u; let K:=pointer G d x m u; let X:= O u; let L:= lilies m (d+y.val) (Shade G); let H(d:ℕ):=lilies m d (Shade G); change X=0; apply lilies_inj (Shade G) (d+y.val) m; rw [map_zero]; apply scoreF _ _ (sproutV m _ _) (show Volume _ (d+y.val) m 0 from ⟨fun _ _=>rfl,fun _=>Sack.zero le_rfl _⟩) (fun i=>by rw [hv];exact stir _) (fun _ _=> rfl); intro n v
       obtain ⟨Q⟩:= mach P C U A b h hs n; let t:=(spool G n).symm v; erw [flair0]; apply Eq.trans (b:=(inkM (sculpt P C U A R b K d) d 0 t).seq y.val) _ (tendsto_nhds_unique (Q.earns R t 0 y hs ht hm _ _ (pointerFee x u)) ?_); swap
       · exact tendsto_const_nhds.congr' (Eventually.of_forall fun i=> (helmQ A R (subStud P C (Q.jet i)) P.odd_side (Q.stems i) U _ _ _ (Q.traceX i) _ _ x m d (sproutV m (d+x.val) u) ht |>.1 y hy).symm)
       rw [vein_i,show spool G n t= v from (spool G n).apply_symm_apply _]; rw [← hv]
end YM.OPE.Silt.Float
