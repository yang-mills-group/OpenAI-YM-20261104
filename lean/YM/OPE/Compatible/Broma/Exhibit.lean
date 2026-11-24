import YM.OPE.Compatible.Broma.Fron
/-! # station transfers.Back halos -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
local notation "X!" => TileC T P p R b
local notation "u!" => (upperX:X!→ℝ)
local notation "q!" => (downK:X!→ℝ)
-- universal routes through timber
noncomputable def Fallix (G:Gauge)(h:Aware d τ)(Z:Sponsor G)(f:Train j)(hp:4 ≤ j):Tracts G d τ ≃L[ℝ] solar G d τ:= (ConeZ G f hp Z.K h (-(1/2))).trans (PoseQ G h)
noncomputable def culm (B:Medal P G K.K P.J)(H:LocalRatio R)(hs:G.Simple)(V:Sailing T P p R b)(hp:Aware d τ)(i:ℕ): Tracts G d τ →L[ℝ] Tracts G d τ:= (Fallix _ hp K (V.U (i+1)).gear P.order_cut).symm.toContinuousLinearMap ∘L (season B H hs V hp i ∘L (Fallix _ hp K (V.U i).gear P.order_cut).toContinuousLinearMap)
variable (B:Medal P G K.K P.J)(H:LocalRatio R)(hs:G.Simple)(S:Sailing T P p R b) (hp: Crest G P K.K m)(ht:Aware d τ)
include B H hs hp ht
lemma shines (he:∀ i,τ i ≤ m) : Brim (fun i:X! => culm B H hs i.1.1 ht i.2) (fun i:X! =>culm B H hs i.1.2 ht i.2) u! fareI:=by
     let A:=PoseQ G ht; have hy:1 ≤ u!:= max_cap _ _ _ _ _; have hv: 0 ≤ (fareI:X!→ℝ):= fixedTheta
     have hq:= (checked (b:=b) (p:=p) (T:=T) B H hp hs ht he).up hy (Y:=fareI) thetaL
     have hR:=Brim.after (saucy (b:=b) (p:=p) (R:=R) (T:=T) hp ht (1/2))
     have hx:= Canal (Brim.constant A.symm.toContinuousLinearMap) hR hy hv
     have hk:= Canal (Canal (Canal (saucy hp ht (p:=p) (T:=T) (b:=b) (- (1/2:ℝ))) (Brim.constant A.toContinuousLinearMap) hy hv) hq hy hv) hx hy hv
     convert! hk using 1 -- simp
     all_goals funext i; apply ContinuousLinearMap.ext; intro j; unfold culm; simp only [Fallix,ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.symm_trans_apply]
     all_goals have he(v:Train P.J)(p:Tracts G d τ) :(ConeZ G v P.order_cut K.K ht (-(1/2))).symm p=Larix G v P.order_cut K.K ht (1/2) p:=by change Larix G v _ K.K ht (- -(1/2:ℝ)) _=_;rw [neg_neg]
     all_goals rw [he _ _]; rfl
-- lift rare
omit H B hs hp in
lemma starMark (X:Tracts G d τ)(Y:Train i)(h:4 ≤ i)(u:Phase)(hf:rare u X):
     let F:=(Fallix G ht K Y h X).val
     (∀ j<u,F j=0)∧ F u=boostS (atlasF G Y h K.K) (-(1/2:ℝ)) (τ u) (d+u.val) (X u).val:=by
          intro F; let q:=Larix G Y h K.K ht (-(1/2:ℝ)) X; have hv:F=(relief G ht q).val:=rfl; have hh:rare u q:=by intro j hj; apply Subtype.ext; unfold q; rw [lavaX,hf j hj]; exact map_zero (boostS ..)
          rw [hv]; refine ⟨(scaleFil G ht q u).1 hh,?_⟩; rw [honors G ht q u hh]; exact lavaX ..
omit H B hs hp in
lemma receiving (X:Tracts G d τ)(Y:Train i)(h:4 ≤ i)(u:Phase)(hp:∀ j<u,(Fallix G ht K Y h X).val j=0): rare u X:=by
      let v:= Larix G Y h K.K ht (-(1/2:ℝ)) X; have hh:rare u v:= (scaleFil G ht v u).mpr hp; rw [show X=Larix G Y h K.K ht (1/2) v from (blaze G ht (1/2) Y h X).symm]; intro j hj; apply Subtype.ext; erw [lavaX, hh j hj]; exact map_zero (boostS ..)
end YM.OPE.Drift
