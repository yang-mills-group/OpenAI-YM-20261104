import YM.OPE.Compatible.Frog.Fall
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
lemma VolumeWe {p:Curtain I}(h: Volume p i k x)(hp:m≤ k): Volume p i m x:=⟨h.1,fun i=>soot_le_k _ x (h.2 i) hp⟩
section
variable (G) (h:Aware d τ)(x:Phase)
local notation "K!"=> bed G (d+x.val) (τ x)
local notation "Q!"=> solar G d τ
include h
noncomputable def paceB : K! →ₗ[ℝ] Muse G where
     toFun p:=baby (τ:=τ) x p.val
     map_add' a b:=by
          unfold baby; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl ?_; intro i _; let f:=lilies (τ x) (d+x.val) (Shade G); let q:= growAdd x ((sproutV _ _ a.val).2 i.val) ((sproutV _ _ b.val).2 i.val) (by have hh:=h.credit x; have hx:=x.isLt;omega); convert! q using 2; rw [Submodule.coe_add,map_add];rfl
     map_smul' c p:=by unfold baby; rw [Finset.smul_sum]; refine Finset.sum_congr rfl ?_; intro i _; erw [Submodule.coe_smul_of_tower, map_smul, Pi.smul_apply, growS]; rfl
noncomputable def ascendF (G:Gauge)(h:Aware d τ)(x:Phase): (bed G (d+x.val) (τ x))→L[ℝ] Tower (Shade G) d τ:=
     let K:= (youthful G h x).choose
     have hh:∀ p:bed G (d+x.val) (τ x),∀ i:Phase,Volume (baby (τ:=τ) x p.val i) (d+i.val) (τ i) (K*‖p‖):=fun p i=> VolumeWe ((youthful G h x).choose_spec.2 p i) (by split; exact le_rfl; exact Nat.le_succ _)
     let F (p:bed G (d+x.val) (τ x))(i:Phase):=fundus (baby (τ:=τ) x p.val i) (K*‖p‖) (hh p i)
     have he(p):spread G d τ (F p)=paceB G h x p:=funext fun i=> sproutsX _ (hh p i)
     have ht:∀ p:bed G (d+x.val) (τ x),‖F p‖ ≤ K * ‖p‖:=fun p=> (pi_norm_le_iff_of_nonneg (mul_nonneg (youthful G h x|>.choose_spec|>.1) (norm_nonneg _))).mpr (fun i=>sproutsU _ (hh p i))
     LinearMap.mkContinuous { toFun:=F, map_add' a b:= (bloomP G d τ) (by erw [he, map_add,map_add,he,he]), map_smul' c x:= (bloomP G d τ) (by rw [he,map_smul,map_smul,he]; rfl) } K ht
-- fix notation local binder K!
lemma pick (p:K!): spread G d τ (ascendF G h x p)=baby (τ:=τ) x p.val:=by funext i; unfold ascendF; exact sproutsX _ (VolumeWe ((youthful G h x).choose_spec.2 p i) (show τ i ≤ _ by split; exact le_rfl; exact Nat.le_succ _))
noncomputable def crestL : K!→L[ℝ] Q!:= (ascendF G h x).codRestrict _ (fun p=>by let v:= (ascendF G h x) p; change Rainbow (spread G d τ v)∧_; have he:= geared G h x p; rw [← pick G h x p] at he;exact he)
lemma crestP (p:K!) : (crestL G h x p).val x=p.val∧ ∀ i<x,(crestL G h x p).val i=0:=by
     have he:= pick G h x p; let q:= ascendF G h x p; refine ⟨lilies_inj _ _ _ ((congr_fun he x).trans (green h x p.property).1),fun i hi=>?_⟩; apply lilies_inj (Shade G) (d+i.val) (τ i); rw [map_zero]; exact (congr_fun he i).trans ((green h x p.property).2 i hi)
end
abbrev Tracts (G:Gauge)(d:ℕ)(τ:Phase→ℕ):= (i:Phase)→ bed G (d+i.val) (τ i)
noncomputable def relief (G:Gauge)(h:Aware d τ): Tracts G d τ →L[ℝ] solar G d τ:=∑ i:Phase, (crestL G h i) ∘L ContinuousLinearMap.proj i
end YM.OPE.Drift
