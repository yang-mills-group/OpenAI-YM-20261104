import YM.RegulatorIR.Oracle.Tectonics

/-! Predictor derivative P,Q. Exact matching. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G: Gauge} {X Y A : Type} {n f c: Side} {α σ δ υ:ℝ} {C:Clip} {L:Side}
lemma matrixQ [Fintype X] (A B:Matrix Y X ℝ)(h:∀ x,A*ᵥ x=B*ᵥ x): A=B:=by ext1 i j;apply Eq.trans _ ((congr_fun (h (Pi.single j 1)) i).trans (dotProduct_single_one ..)); exact (dotProduct_single_one ..).symm

section data
variable (P:Patch)(H:KernelChoices)(n:Side)
-- Sun footprints. No forcing of patch size.
variable {F: StepData n f} (g:Vec G f 1)(u:G.ColorIndex)
lemma revenue (x:Cover)(r:Walk): combo (g ∘ (linksQ G).swrap f) (spineK u x r)= Precision.integralLink (wrap f x) r (component g u) :=by
 rw [spinal]; exact walks_cover (fun z:Edge (Site f)=> component g u (z.1,coord z.2)) x r
lemma heights_t (x:Cover)(r:F.patch.Points):combo (g∘(linksQ G).swrap f) (tauK F x r u)=Precision.tau F (wrap _ x) r (component g u):=by
 unfold Quadratic.tauK Precision.tau;simp only [_root_.map_neg,_root_.map_smul,_root_.map_sum,LinearMap.smul_apply,LinearMap.neg_apply, LinearMap.sum_apply,revenue, Quadratic.tex_wrap]
lemma fees_t (x:Cover)(F:StepData n f): combo (g ∘ (linksQ G).swrap f) (anchorK F x u)= (fixRoot F*ᵥ component g u) (wrap n x,vac):=by
 rw [anchorK,_root_.map_sub,_root_.map_sum]; simp_rw [_root_.map_smul, heights_t]; rw [fixRoot,LinearMap.toMatrix'_mulVec]; simp [Precision.adjusted]
lemma credited (n:Side)(G:Gauge): ledgerRow (linksQ G) (blockQ G P.L) (OrthoQ P H G) n=FreeResolvent.tensor G (Precision.probe (avenue P H n)):=by
 apply matrixQ; intro x; ext1 i; let T:= avenue P H n
 obtain ⟨⟨⟨y,q⟩,j⟩,rfl⟩:=(show Surjective ((linksQ G).swrap n) from fun i=>⟨_,(linksQ G).both ..⟩) i
 let d:=wrap n y;let f:=n*P.L
 rw [Rubric P H G n,cargo_of _ (linksQ G) (blockQ G P.L) _ n (fringe (avenue P H n)) (fringe_inv (avenue P H n) G)]
 rw [show (blockQ G P.L).swrap n=(linksQ G).swrap f from funext (fun i=> v_same ..)]
 let v:= component (G:=G) x j; change combo (x ∘ _) (fringe T _)= component (FreeResolvent.tensor G _*ᵥ x) j (d,coord q)
 rw [FreeResolvent.component_mul,fringe]; dsimp only; simp only [_root_.map_add,_root_.map_sub,_root_.map_sum,_root_.map_smul]; rw [probe,add_mulVec, ← Matrix.mulVec_mulVec,Pi.add_apply, Exterior.d_sites,Precision.mean,LinearMap.toMatrix'_mulVec]; simp only [LinearMap.pi_apply,LinearMap.smul_apply,LinearMap.sum_apply]; simp_rw [show axisEquiv.symm (coord q)=q from axisEquiv.symm_apply_apply _]
 unfold T f d
 simp_rw [revenue, Quadratic.tex_wrap,fees_t,_root_.map_add,wrap_step]
end data
end YM.RegulatorIR.Oracle
