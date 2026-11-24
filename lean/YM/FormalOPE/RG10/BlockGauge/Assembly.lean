import YM.FormalOPE.RG10.BlockGauge.Root
import YM.FormalOPE.RG10.BlockGauge.Scheme
/-!
 # Joint gauge truss measure and smoothness

 A root truss usable across any number of blocking steps (vertex/edge and *single* inversion convention over whole auxiliary graph).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.BlockGauge
open Filter Topology Function Set Finset Metric MeasureTheory PertExtension Measure
open RG InversionWard Push.Loops
open scoped Classical ContDiff Matrix.Norms.Frobenius Topology
variable {V E : Type}
namespace Loom.Truss
variable {D : Loom V E}(T : D.Truss) {K : Type}
 def stitch (b : T.Tree→K) (y:T.Bulk→K) (i:E): K := if h:T.Branch i then b ⟨i,h⟩ else y ⟨i,h⟩
@[simp] lemma stitch_whole (u:E→K) : T.stitch (fun i=> u i.val) (fun i=>u i.val)=u:= by ext1 i; unfold stitch; split<;>rfl
@[simp] lemma stitch_tree (b:T.Tree→K)(y:T.Bulk→K)(i:T.Tree): T.stitch b y i.val=b i:=by simp [stitch,i.property]
@[simp] lemma stitch_bulk (b:T.Tree→K)(y:T.Bulk→K)(i:T.Bulk): T.stitch b y i.val=y i:=by simp [stitch,i.property]
variable [Group K]
 def board (u:T.Bulk→K) : E→K:= T.stitch 1 u
 -- frame normalized group variables. Can send to another truss via secondVisit (`transfer`).
 def bulk (u:E→K) (i:T.Bulk) : K:= T.treeGauge u i.val
lemma board_bulk (u:E→K): T.board (T.bulk u)=T.treeGauge u:= by
 ext1 i; by_cases h:T.Branch i
 · simp [board,stitch,h,T.fixes_tree u i h]
 simp [board,stitch,h,bulk]
lemma board_tree (u:T.Bulk→K) : T.treeGauge (T.board u)=T.board u:= T.already _ (by intro i h; simp [board,stitch,h])
lemma bulk_board (u:T.Bulk→K) : T.bulk (T.board u) = u := funext fun i=> (congr_fun (T.board_tree u) i.val).trans (T.stitch_bulk ..)
variable (R:D.Truss)
 def transfer (u:T.Bulk → K) : R.Bulk→K:= R.bulk (T.board u)
@[simp] lemma board_one : T.board (1:T.Bulk→K)=1:= T.stitch_whole 1
@[simp] lemma treeGauge_one : T.treeGauge (1:E→K)=1:=T.already _ fun _ _=>rfl
@[simp] lemma bulk_one : T.bulk (1:E→K)=1:=funext (fun i=> congr_fun T.treeGauge_one i.val)
@[simp] lemma transfer_one : T.transfer R (1:T.Bulk→K)=1:= by rw [transfer,T.board_one,R.bulk_one]
lemma transfer_spin (u:T.Bulk→K): R.board (T.transfer R u)=R.treeGauge (T.board u):= R.board_bulk _
lemma recover (u:T.Bulk→K) : R.transfer T (T.transfer R u)=u:= by
 rw [transfer, transfer_spin]
 change (fun i:T.Bulk=> T.treeGauge (D.spin _ (T.board u)) i.val)=u
 rw [T.identify _ _ (R.frame_root _)]
 exact T.bulk_board u
-- continuity of truss
variable [TopologicalSpace K] [IsTopologicalGroup K]
omit [Group K] [IsTopologicalGroup K] in
lemma stitch_cont : Continuous (fun a:(T.Tree→K)×(T.Bulk→K)=>T.stitch a.1 a.2):= by apply continuous_pi; intro i; unfold stitch; split<;> fun_prop
omit [IsTopologicalGroup K] in
@[fun_prop] lemma board_cont : Continuous (T.board (K:=K)) := by
 unfold board stitch; apply continuous_pi; intro i; split<;> fun_prop
lemma frame_cont_apply (v:V): Continuous (fun u:E→K=> T.frame u v) := by
 by_cases h:v=D.origin
 · subst v; simp [continuous_const]
 simp_rw [T.frame_parent (v:=v) _ h]; refine (frame_cont_apply (T.parent v h)).mul ?_
 unfold toward; split <;> fun_prop
termination_by T.height v
decreasing_by exact T.descend _ _
@[fun_prop] lemma frame_cont : Continuous (T.frame (K:=K)):= continuous_pi (T.frame_cont_apply)
@[fun_prop] lemma treeGauge_cont : Continuous (T.treeGauge (K:=K)):= by unfold treeGauge spin; fun_prop
@[fun_prop] lemma bulk_cont : Continuous (T.bulk (K:=K)):= continuous_pi fun i=> (continuous_apply i.val).comp (T.treeGauge_cont)
@[fun_prop] lemma transfer_cont : Continuous (T.transfer (K:=K) R):= R.bulk_cont.comp T.board_cont
 def relocation : (T.Bulk→K) ≃ₜ (R.Bulk→K):= { toFun:= T.transfer R, invFun:=R.transfer T, left_inv:=T.recover R, right_inv:=R.recover T, continuous_toFun:=T.transfer_cont _, continuous_invFun:=R.transfer_cont _ } -- parse
-- bulk rotations
 def rotation (g:V→K) (y:T.Bulk → K) (i:T.Bulk):=g (D.fromEdge i.val)*y i*(g (D.toEdge i.val))⁻¹
@[fun_prop] lemma rot_cont (g:V→K) : Continuous (T.rotation g):= by unfold rotation; fun_prop
 def rotHomeo (g:V→K) : (T.Bulk→K)≃ₜ(T.Bulk→K) where
  toFun:=T.rotation g
  invFun:=T.rotation g⁻¹
  left_inv u:= by ext1 i; simp [rotation]; group
  right_inv u:= by ext1 i; simp [rotation]; group
  continuous_toFun:=T.rot_cont _
  continuous_invFun:=T.rot_cont _
-- gauge fixing universal. Need only root preserving gauge.
variable [Fintype E][MeasurableSpace K][SecondCountableTopology K][BorelSpace K]
-- measurable assembly simply mathlib
omit [Group K] [IsTopologicalGroup K] [TopologicalSpace K] [SecondCountableTopology K] [BorelSpace K] in -- omission dependency? lean
lemma preserving_equiv (μ:Measure K) [SigmaFinite μ] : MeasurePreserving (fun a:(T.Tree→K)×(T.Bulk→K)=>T.stitch a.1 a.2) ((Measure.pi fun _:T.Tree=>μ).prod (Measure.pi fun _:T.Bulk=>μ)) (Measure.pi fun _:E=>μ):= by
 convert (measurePreserving_piEquivPiSubtypeProd (fun _:E=>μ) (T.Branch)).symm using 1 -- maybe defin
 ext ⟨u,v⟩ i
 change T.stitch u v i=(Equiv.piEquivPiSubtypeProd T.Branch (fun _=>K)).symm (u,v) i
 rw [Equiv.piEquivPiSubtypeProd_symm_apply]; unfold stitch; split<;>rfl
variable (μ:Measure K) [IsProbabilityMeasure μ][IsMulLeftInvariant μ] [IsMulRightInvariant μ]
local notation "π₀" => (Measure.pi fun _:E=>μ)
local notation "π₁" => (Measure.pi fun _:T.Tree=>μ)
local notation "π₂" => (Measure.pi fun _:T.Bulk=>μ)
lemma preserving_rot (g: V→K) : MeasurePreserving (T.rotHomeo g) π₂ π₂:=
 measurePreserving_pi _ _ (fun _=> (measurePreserving_mul_right _ _).comp (measurePreserving_mul_left _ _))
omit [Fintype E] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [SecondCountableTopology K] [BorelSpace K] μ in
lemma bulk_rot (b:T.Tree→K)(y:T.Bulk→K) : T.bulk (T.stitch b y) = T.rotation (T.frame (T.stitch b 1)) y:= by
 ext1 i; unfold bulk rotation treeGauge spin
 rw [stitch_bulk]; rw [show T.frame (T.stitch b y)= T.frame (T.stitch b 1) from funext (fun v=> T.frame_only _ _ (fun j h=> by simp [stitch,h]) v)] -- hmm simp known
variable {M:Type}[NormedAddCommGroup M][NormedSpace ℝ M][CompleteSpace M]
theorem elimination (f:(E→K)→M)(hi:Integrable f π₀) (hg:∀ (g : V → K), g D.origin=1 → ∀ (u:E→K), f (D.spin g u)=f u):
 (∫ u,f u ∂π₀)=∫ y,f (T.board y) ∂π₂:= by
 let e:(T.Tree→K)×(T.Bulk→K) → (E→K):=fun a=>T.stitch a.1 a.2
 have h₁: Integrable (fun a=> f (e a)) ((π₁).prod π₂) := (T.preserving_equiv _).integrable_comp_of_integrable hi
 calc
 _ = (∫ x, f (e x) ∂((π₁).prod π₂)) := by
   conv_lhs => rw [←(T.preserving_equiv μ).map_eq]
   exact integral_map (T.preserving_equiv μ).measurable.aemeasurable (by rw [(T.preserving_equiv μ).map_eq]; exact hi.aestronglyMeasurable)
 _ = ∫ b,∫ y, f (e (b,y)) ∂π₂ ∂π₁:= integral_prod _ h₁
 _ = ∫ _,∫ y, f (T.board y) ∂π₂ ∂π₁:= by
   refine integral_congr_ae (Filter.Eventually.of_forall fun b=>?_)
   simp_rw [show ∀ y, f (e (b,y)) =f (T.board ((T.rotHomeo (T.frame (T.stitch b 1))) y)) from fun y=> (hg (T.frame _) (T.frame_root _) (e (b,y))).symm.trans (congr_arg f (by rw [show (T.rotHomeo _) y = T.rotation (T.frame (T.stitch b 1)) y from rfl, ← T.bulk_rot,T.board_bulk]; rfl))]
   exact (T.preserving_rot μ _).integral_comp (Homeomorph.measurableEmbedding _) (fun y=> f (T.board y))
 _ = ∫ y,f (T.board y) ∂π₂:=by simp
-- smooth frame on jet variables: needs MatDiffAt
section
omit [Fintype E]
variable {G: Gauge} {U:Type}[NormedAddCommGroup U][NormedSpace ℝ U]{x:U}
lemma stitch_diff {b: U→ T.Tree→ G.El} {u:U→ T.Bulk→G.El} (hb: MatDiffAt b x) (hu:MatDiffAt u x): MatDiffAt (fun i=> T.stitch (b i) (u i)) x:= by
 intro j; unfold stitch; dsimp only; split
 · exact hb _
 exact hu _
lemma board_diff {u: U→ T.Bulk→G.El}(hu:MatDiffAt u x): MatDiffAt (T.board ∘ u) x := T.stitch_diff (fun _=> contDiffAt_const) hu
lemma frame_diff_apply {u:U→E→G.El}(hu:MatDiffAt u x) (v:V): ContDiffAt ℝ ω (fun i=> G.mat (T.frame (u i) v)) x := by
 by_cases h:v=D.origin
 · subst v; simp [contDiffAt_const]
 simp_rw [T.frame_parent _ v h, G.mat_mul]
 refine (frame_diff_apply hu (T.parent v h)).mul ?_
 unfold toward; split
 · exact hu _
 exact mat_inv_diff (hu _)
termination_by T.height v
decreasing_by exact T.descend _ _
lemma frame_diff {u:U→E→G.El}(hu:MatDiffAt u x): MatDiffAt (T.frame ∘ u) x:= T.frame_diff_apply hu
lemma treeGauge_diff {u:U→E→G.El}(hu:MatDiffAt u x): MatDiffAt (T.treeGauge ∘ u) x:= by
 intro i; unfold treeGauge spin; simp_rw [Function.comp_apply,G.mat_mul]; exact ((T.frame_diff_apply hu _).mul (hu i)).mul (mat_inv_diff (T.frame_diff_apply hu _))
lemma bulk_diff {u:U→E→G.El}(hu:MatDiffAt u x): MatDiffAt (T.bulk ∘ u) x:= fun i=> T.treeGauge_diff hu i.val
lemma transfer_diff {u:U→T.Bulk→G.El}(hu:MatDiffAt u x): MatDiffAt (T.transfer R ∘ u) x:= R.bulk_diff (T.board_diff hu)
end
end Loom.Truss
end YM.FormalOPE.RG10.BlockGauge
