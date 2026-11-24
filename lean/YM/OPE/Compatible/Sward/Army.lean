import YM.OPE.Compatible.Stamen.Wisp
import YM.OPE.Compatible.Broma.Exhibit
/-!
# Suspension; exact beta formal and flags
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l k:ℕ}{x:ℝ}
variable {τ:Phase→ℕ}
local notation "T!"=> Tower (Shade G) d τ
-- section for solar.Step-independent
open Silt.Phere
lemma young0 (G:Gauge)(h:Aware d τ)(x:Phase):∃ a:ℝ,0 ≤ a∧∀ (p:empa G.ColorIndex (d+x.val) (τ x)),∀ i:Phase,Volume (baby (τ:=τ) x p.val i) (d+i.val) (if i=x then τ i else τ i+1) (a*‖p‖):=by
      let v:=d+x.val+1; choose c hc H using burst (G:=G) h x; let z(i:Phase):=∑ j,c j i; have hv(i):0≤z i:=Finset.sum_nonneg fun j _=> hc j i; refine ⟨∑ i,z i,Finset.sum_nonneg fun i _=>hv i,fun p i=>?_⟩
      let f:=baby (τ:=τ) x p.val; let X:= lilies (τ x) _ _ p.val; let q(j:Fin v):= glide (Grid.lance (X j.val)) x i; have hp(j:Fin v):Volume (q j) (d+i.val) (if i=x then τ i else τ i+1) (c j i*‖p‖):= H j i _ _ (p.property.1 j.val) (p.property.2 j.val) ((sproutV _ _ p.val).2 j.val)
      rw [show baby (τ:=τ) x p.val i=∑ j,q j from Finset.sum_apply ..]; apply Volume.raise _ (Volume.sum q (fun j=> c j i*‖p‖) Finset.univ (fun j _=>hp j)) le_rfl; rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=z) (fun i _=>hv i) (Finset.mem_univ _)) (norm_nonneg _)

section
variable (G) (h:Aware d τ)(x:Phase)
local notation "K!"=> empa G.ColorIndex (d+x.val) (τ x)
local notation "Q!"=> solar G d τ
include h
noncomputable def barsB : K! →ₗ[ℝ] Muse G where
     toFun p:=baby (τ:=τ) x p.val
     map_add' a b:=by
          unfold baby; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl ?_; intro i _; let f:=lilies (τ x) (d+x.val) (Shade G); let q:= growAdd x ((sproutV _ _ a.val).2 i.val) ((sproutV _ _ b.val).2 i.val) (by have hh:=h.credit x; have hx:=x.isLt;omega); convert! q using 2; rw [Submodule.coe_add,map_add];rfl
     map_smul' c p:=by unfold baby; rw [Finset.smul_sum]; refine Finset.sum_congr rfl ?_; intro i _; erw [Submodule.coe_smul_of_tower, map_smul, Pi.smul_apply, growS]; rfl
noncomputable def scrollF (G:Gauge)(h:Aware d τ)(x:Phase): (empa G.ColorIndex (d+x.val) (τ x))→L[ℝ] Tower (Shade G) d τ:=
     let K:= (young0 G h x).choose
     have hh:∀ p:empa G.ColorIndex (d+x.val) (τ x),∀ i:Phase,Volume (baby (τ:=τ) x p.val i) (d+i.val) (τ i) (K*‖p‖):=fun p i=> VolumeWe ((young0 G h x).choose_spec.2 p i) (by split; exact le_rfl; exact Nat.le_succ _)
     let F (p:empa G.ColorIndex (d+x.val) (τ x))(i:Phase):=fundus (baby (τ:=τ) x p.val i) (K*‖p‖) (hh p i)
     have he(p):spread G d τ (F p)=barsB G h x p:=funext fun i=> sproutsX _ (hh p i)
     have ht:∀ p:empa G.ColorIndex (d+x.val) (τ x),‖F p‖ ≤ K * ‖p‖:=fun p=> (pi_norm_le_iff_of_nonneg (mul_nonneg (young0 G h x|>.choose_spec|>.1) (norm_nonneg _))).mpr (fun i=>sproutsU _ (hh p i))
     LinearMap.mkContinuous { toFun:=F, map_add' a b:= (bloomP G d τ) (by erw [he, map_add,map_add,he,he]), map_smul' c x:= (bloomP G d τ) (by rw [he,map_smul,map_smul,he]; rfl) } K ht
-- fix notation local binder K!
lemma splitF (p:K!): spread G d τ (scrollF G h x p)=baby (τ:=τ) x p.val:=by funext i; unfold scrollF; exact sproutsX _ (VolumeWe ((young0 G h x).choose_spec.2 p i) (show τ i ≤ _ by split; exact le_rfl; exact Nat.le_succ _))
end
end YM.OPE.Drift
