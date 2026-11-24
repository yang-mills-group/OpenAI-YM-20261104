import YM.OPE.Compatible.Parch.Hooks
import YM.OPE.Compatible.Parch.Garden
/-!
# Use a finite-cost Mark register
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw
variable {i j d k m r l b:ℕ}{n:Side}{S:Finset Cover}
variable {D V:Type}
variable (G)
noncomputable def dyeL [Fintype D][Fintype V] (j:D↪ V): Libra.Keys G D→L[ℝ]Libra.Keys G V:=ContinuousLinearMap.pi fun i=> if h:i∈Set.range j then ContinuousLinearMap.proj (Classical.choose h) else 0
variable [Fintype D][Fintype V]
lemma dye_e (j:D↪ V)(x:Libra.Keys G D) (y:D):dyeL G j x (j y)=x y:=by unfold dyeL; rw [ContinuousLinearMap.pi_apply]; have he: j y ∈ Set.range j:=Set.mem_range_self ..; rw [dif_pos he,show Classical.choose he=y from j.injective (Classical.choose_spec he)]; rfl
lemma dye_off (j:D↪ V)(x:Libra.Keys G D)(y:V)(he:y∉Set.range j): dyeL G j x y=0:=by unfold dyeL; rw [ContinuousLinearMap.pi_apply,dif_neg he]; rfl
lemma dye_norm (j:D↪ V)(x:Libra.Keys G D): ‖dyeL G j x‖≤ ‖x‖:=by
        refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun i=>?_) ; by_cases he:i∈Set.range j
        · obtain ⟨t,rfl⟩:=he; rw [dye_e G j x t]; exact norm_le_pi_norm x t
        rw [dye_off G j x i he,norm_zero]; exact norm_nonneg _
variable (p:Finset (Edge Cover)) (hp:p⊆bark b) (hb:Board n b)
noncomputable def jetK:Libra.Keys G (↥p) →L[ℝ] Bid.Dir G n:= dyeL G (mote hb hp)
lemma readU (x:Libra.Keys G (↥p)): BlurD G p n (jetK G p hp hb x)=x:=by
       funext i; rw [echoP]; exact dye_e G (mote hb hp) x i
lemma frame_e (x:Libra.Keys G (↥p)): ‖jetK G p hp hb x‖ ≤ ‖x‖:=dye_norm G _ _
lemma buf (x:Bid.Dir G n): ‖BlurD G p n x‖ ≤ ‖x‖:=by
       refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=>?_ ; rw [echoP]; exact norm_le_pi_norm x _
variable {G} {X:Type}
lemma Crisp.pack (f:Bid.Dir G n→X)(h:Crisp p f)(x:Bid.Dir G n):f x=f (jetK G p hp hb (BlurD G p n x)):= h.jury _ _ (readU ..|>.symm) -- inference
lemma toneI {f:Bid.Dir G n→ℝ} (h:Crisp p f)(he:ContDiffAt ℝ ω f 0)(k:ℕ): Crisp p (Claw.rank f k):=⟨fun i j he'=>crossD _ he h.jury (fun _=>i) (fun _:Fin k=>j) (fun _=>he')⟩
end YM.OPE.Merchant
