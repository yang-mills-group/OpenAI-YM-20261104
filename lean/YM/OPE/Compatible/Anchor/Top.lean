import YM.OPE.Compatible.Anchor.Lit
/-!
# Candidate carriers.Template
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Labels
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r n l:ℕ}{Z I J M E F:Type}
variable {K:Sponsor G}{S:Seasons K}{u:M→ℝ}{v:ℝ}{τ:Phase→ℕ}
local notation "Ξ"=>solar G d τ
local notation "θ"=> 𝓝[>] (0:ℝ)
-- Ω extraction
variable {R: Alphabet G k→ℝ} (L:M→ Submodule ℝ (solar G d τ))
structure Keeps (X:solar G d τ)(r:ℕ)(h:ℕ)(P:Alphabet G k→ℝ) :Prop where
     cap : CapE r X
     cue (x:Alphabet G k) : BillUp ℝ h (fun t=>Lug (topX X r) x t) (P x)
lemma CapE.add {x y:Ξ}(h:CapE r x)(hv:CapE r y): CapE r (x+y):=by intro j hj; unfold topX; rw [Submodule.coe_add,map_add]; exact (show _ = _ from congr_arg₂ (·+·) (h j hj) (hv j hj))|>.trans (add_zero _)
lemma CapE.smul (c:ℝ){x:Ξ}(h:CapE r x): CapE r (c • x):=by intro j hj; unfold topX; erw [ Submodule.coe_smul_of_tower, map_smul]; change c • topX x _= _; rw [h _ hj,smul_zero]
def RoomN (z:M→ℝ)(L:M→ Submodule ℝ (solar G d τ))(f:M→ fieldX (Shade G)→ ℝ)(r k:ℕ):Prop:= ∃ c:ℝ,0≤c∧∀ i:M,∃ v:Ξ,‖v‖ ≤ c*z i∧v∈ L i ∧ CapE r v ∧ ∀ p,Quiet p k→wholeX (topX v r) (fun _=>p)= f i p
variable {z:M→ℝ}{g f:M→fieldX (Shade G)→ℝ}
lemma Brace (x:Ξ): soot (τ 0) (topX x r) ‖x.val 0‖:= (sproutV _ _ _).2 r
lemma mineral (p:fieldX (Shade G))(h:Quiet p k)(hp:r*k ≤ τ 0)(x y:Ξ): wholeX (topX (x+y) r) (fun _=>p)= wholeX (topX x r) (fun _=>p)+wholeX (topX y r) (fun _=>p):=by
     let k':Fin r→ℕ:=fun _=>k; have hv:topX (x+y)=topX x+topX y:=by unfold topX;rw [Submodule.coe_add,map_add];rfl
     rw [hv,Pi.add_apply,manyX (Brace x) (Brace y) (k:= k') (fun _=>h)]; simpa  [k'] using hp -- arg name?
lemma MineralZ (p:fieldX (Shade G))(x:Ξ)(a:ℝ): wholeX (topX (a • x) r) (fun _=>p)= a * wholeX (topX x r) (fun _=>p):=by
     rw [show topX (a • x) r=a • topX x r from ?_]; exact scaleX ..; unfold topX;erw[Submodule.coe_smul_of_tower,map_smul];rfl
lemma Keeps.add {x y:Ξ}{V U:Alphabet G k→ℝ}(hp: Keeps x r n V)(h:Keeps y r n U)(hv:r*k ≤ τ 0): Keeps (x+y) r n (V+U):=by
     refine ⟨CapE.add hp.cap h.cap,fun v=>?_⟩; apply ((hp.cue v).add (h.cue v)).congr; intro i; unfold Lug;dsimp only;rw [mineral _ (BrushQ ..) hv, smul_add]
lemma Keeps.smul {x:Ξ}(h:Keeps x r n R)(a:ℝ): Keeps (a • x) r n (a • R):=by
     refine ⟨CapE.smul a h.cap,fun i=>?_⟩; apply ((h.cue i).const_smul a).congr; intro t; unfold Lug;dsimp only;rw [MineralZ,smul_eq_mul,smul_eq_mul,smul_eq_mul,mul_left_comm]
lemma RoomN.pack (h:RoomN z L f r k)(hv:RoomN z L g r k)(hx:r*k≤τ 0): RoomN z L (f+g) r k:=by
      obtain ⟨c,hc,H⟩:=h; obtain ⟨d,hD,D⟩:=hv; refine ⟨c+d,add_nonneg hc hD,fun i=>?_⟩; obtain ⟨x,hx',hr,hy,ht⟩:=H i; obtain ⟨y,hz,hρ,hp,H⟩:=D i; refine ⟨x+y, ((norm_add_le x y).trans (add_le_add hx' hz)).trans_eq (add_mul ..).symm, Submodule.add_mem _ hr hρ, CapE.add hy hp,fun p hv=>?_⟩; rw[mineral p hv hx,ht p hv,H p hv];rfl
lemma RoomN.smul (h:RoomN z L f r k)(a:ℝ):RoomN z L (a • f) r k:=by obtain ⟨c,hc,H⟩:=h; refine ⟨‖a‖*c,by positivity,fun i=>?_⟩; obtain ⟨v,hp,hV,ht,H⟩:=H i; refine ⟨a • v,?_,(L i).smul_mem a hV,CapE.smul a ht,fun p hv=>?_⟩; rw [norm_smul]; exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (by ring); rw [MineralZ,H p hv];rfl
lemma top0 : topX (0:Ξ)=0:=by unfold topX; erw[Submodule.coe_zero,map_zero]; rfl
lemma CapE.huh : CapE r (0:Ξ):=fun _ _=> (by rw [top0];rfl)
lemma RoomN.zen : RoomN z L 0 r k := by refine ⟨0,le_rfl,fun i=>⟨0, ?_, (L i).zero_mem, CapE.huh,?_⟩⟩; rw[norm_zero,zero_mul]; intro p _; rw [top0]; exact (show _=0 from by simp [wholeX])
lemma RoomN.sum (s:Finset I)(f:I→M→fieldX (Shade G)→ℝ)(h:∀ i∈s,RoomN z L (f i) r k)(hp:r*k≤τ 0):RoomN z L (∑ i∈s,f i) r k:=by induction s using Finset.induction_on with
     | empty=> rw[sum_empty]; exact RoomN.zen _
     | insert i s hi ih=> rw [sum_insert hi]; exact RoomN.pack L (h _ (mem_insert_self ..)) (ih (fun i hi=> h _ (mem_insert_of_mem hi))) hp
-- actual l=0 etc
structure Obtains (z:M→ℝ)(L:M→ Submodule ℝ (solar G d τ))(r n:ℕ)(P:Alphabet G k→ℝ):Prop where
      stock:∃ c:ℝ,0≤c∧∀ i:M,∃ v:solar G d τ, ‖v‖ ≤ c*z i∧v∈ L i ∧ Keeps v r n P
lemma RoomN.get (h:RoomN z L f r k)(hp:∀ i:M,∀ x:Alphabet G k,BillUp ℝ n (fun s:ℝ=> f i (showerW k s x)) (R x)): Obtains z L r n R:=by
     obtain ⟨c,hc,H⟩:=h; refine ⟨c,hc,fun i=>?_⟩; obtain ⟨v,hv,h,hz,ht⟩:=H i; exact ⟨v,hv,h,hz,fun x=>(hp i x).congr fun j=>by unfold Lug;dsimp only;rw [ht _ (BrushQ ..)]⟩ -- orientation
end YM.OPE.Variance
