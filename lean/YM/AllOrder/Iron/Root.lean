import YM.Next.STATIONARY.Spectral.ComplexGap
import YM.AllOrder.Iron.Poise
import YM.Next.STATIONARY.Block.Static
import YM.TraceExtension.Perfect.Stove
import YM.Next.STATIONARY.Joint.FourPoint
import YM.Next.STATIONARY.Joint.HaarJac
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Iron
open Lattice Laurent RG Filter Tree Metric Finset Function Gauge Matrix Module
open Exterior Wilson Precision Tree MeasureTheory Stationary
open scoped Matrix BigOperators Topology Classical ContDiff InnerProductSpace Matrix.Norms.Frobenius ENNReal
variable {G:Gauge}{c f:Side}{S:StepData c f} (F:Forest S.ratio)(t:S.Choices) {p:Clip}{R:PathData G}

variable (i: G.ColorIndex)
open Wilson Precision
-- price envelope. row norm via resulting decay
open Bloch Laurent Audience
open scoped ComplexConjugate
variable {α : Type}[Fintype α][DecidableEq α] {σ A:ℝ}{v:Momentum}
abbrev billT (L:Side)(σ:ℝ) := Real.exp (σ*4)*(inch L)⁻¹+1
variable {L:Side}
lemma spicetab (h : v∈strip σ): vflux ((slabW G L).tile v) ≤ billT L σ:= by
    refine spade_flux (α:= Co L (Loc G 1)) ?_ ?_
    · unfold altarTile contour; let g : Momentum:= v; let C0:=Co L (Loc G 1); let e:=Real.exp (σ*4); let x:=spice L (Loc G 1) v; have hc := inch_pos L; have hx:(‖x‖) ≤ (inch L)⁻¹:= by -- syntax?
         rw [pi_norm_le_iff_of_nonneg (by positivity : 0 ≤(inch L)⁻¹)]; intro i; unfold x spice; rw [norm_inv, Complex.norm_real,Real.norm_of_nonneg (hill_pos ..).le]; exact inv_anti₀ hc (hill_inch ..) -- name
      -- unfold maybe
      let H:= plankTile L (Loc G 1); change vflux ((H v*diagonal x)*(H 0)⁻¹)≤_
      rw [(tile_ice (L:=L) (p:=0) (by simp)).back.slide_v]; exact ((flux_power ..).trans (mul_le_mul (plank_cap v h) (show vflux (diagonal x) ≤ (inch L)⁻¹ from by rw [flux_diagonal]; exact hx) (flux_nonneg _) (Real.exp_pos _).le)).trans (by unfold billT; linarith)
    unfold billT; exact flux_one.trans (le_add_of_nonneg_left (by have hx:=inch_pos L; positivity))
local notation "W"=> slabW G L
variable (F:Momentum→CompM (ParcelG G L) (ParcelG G L))
-- pay linear prescribed slot counts.Patch unity.
abbrev door (A : ℝ) (L:Side)(σ:ℝ):= A*(billT L σ)^2
lemma door_supply {F:Momentum→CompM (ParcelG G L) (ParcelG G L)} (h: Poster σ F) (hp: 0<σ) (hu:0≤ A)(hf : Freezer (W).dual W F σ A) (i j : ParcelG G L): Firm σ (door A L σ) (fun v=>(F v)⁻¹ i j):=by
   have hT : Poster σ (fun v=>(F v)⁻¹):= ?_
   swap
   · exact ((Play.current (ι:=Axis) h).back hf.period).tab -- check
   refine ⟨⟨hp,fun v hv=>hT.shape hv i j, ?_⟩, ?_⟩ -- Vane fields
   · intro p hp' a; have hw := hT.shifts (show rolls p (p+reciprocal a) from ⟨a,rfl⟩) hp'; rw [hw] -- check orientation
   intro p h; let X:=(F p)⁻¹; let B:=W; let S:=carryM B B.dual p p X; let C:= B.tile p; let D:= (B.dual.tile p)⁻¹
   have hx : X=C*S*D:=by unfold C S D carryM; rw [← Matrix.mul_assoc (B.tile p), ← Matrix.mul_assoc (B.tile p),Matrix.mul_nonsing_inv _ (B.whole _),Matrix.one_mul, Matrix.mul_assoc,mul_nonsing_inv _ (B.dual.whole _), Matrix.mul_one] -- check
   have he:= (spicetab (L:=L) (G:=G) h); have hg : vflux D ≤ billT L σ:= by unfold D; rw [Slab.inverse_dual,back_flux]; exact (spicetab (G:=G) (L:=L) (negResident h))
   refine (flux_tilt ..).trans ?_; change vflux X≤ _; rw [hx]; refine (flux_power ..).trans ((mul_le_mul ((flux_power C S).trans (mul_le_mul he (hf.price _ h) (flux_nonneg _) ((flux_nonneg _).trans he))) hg (flux_nonneg _) ?_).trans_eq ?_); · exact mul_nonneg ((flux_nonneg _).trans he) hu
   unfold door; ring
end YM.AllOrder.Iron
