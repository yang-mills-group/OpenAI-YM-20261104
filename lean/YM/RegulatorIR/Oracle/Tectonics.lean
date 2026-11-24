import YM.RegulatorIR.Oracle.Lights
import YM.RegulatorIR.Older.Trunk

/-! Stencil supports. Probe from genuine finite forest, exactly. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G: Gauge} {X Y A : Type} {n f: Side} {α σ δ υ:ℝ} {C:Clip} {L:Side}
-- fix plant P and yields geometry Family
variable (P: Patch)(K:KernelChoices)
def avenue (p:Patch)(k:KernelChoices)(n:Side): StepData n (n*p.L):=⟨p,k,rfl⟩
-- fine hull
private lemma frame_trunk (d:Cover)(x:Cover)(a:Lattice.Step) : a.used (d+x) = Geometry.dis d (a.used x):=by unfold Lattice.Step.used Geometry.dis; split <;> simp only [add_sub_assoc]
lemma spinal_move (x:Cover)(i:G.ColorIndex)(d:Cover)(w:Walk)(v:Long G.ColorIndex): spineK i (d+x) w (motionsQ v d)=spineK i x w v:=by
 induction w generalizing x with
 | nil=>rfl
 | cons a l ih=>
   rw [spineK,spineK,Finsupp.add_apply,Finsupp.add_apply,add_assoc, ih]
   let u:Long G.ColorIndex:=(a.used x,i);have hp : Finsupp.single (a.used (d+x),i) (1:ℝ) (motionsQ v d)=Finsupp.single u 1 v:=by rw [frame_trunk];change Finsupp.single (motionsQ u d) _ _ = _;rw [← site_roll,← site_roll]; simp [Finsupp.single_apply]
   dsimp only; split_ifs; apply congr_arg (·+_); exact congr_arg Neg.neg hp
   rw [hp]
lemma texT (T:StepData n f)(x d:Cover)(b:T.patch.Points): tex T (d+x) b=T.patch.L.val • d+tex T x b:=by
 change b.val+ T.patch.L.val • (d+x)=T.patch.L.val • d+(b.val+T.patch.L.val • x);rw [smul_add];abel
lemma tassel (T:StepData n f)(x:Cover)(t:T.patch.Points)(d:Cover)(i:G.ColorIndex)(c:Long G.ColorIndex):
 tauK T (d+x) t i (motionsQ c (T.patch.L.val • d))=tauK T x t i c:=by
 unfold tauK; simp only [Finsupp.neg_apply,Finsupp.smul_apply,Finsupp.finsetSum_apply,texT T x,spinal_move]
lemma anchored (T:StepData n f)(x:Cover)(d:Cover)(i:G.ColorIndex)(c:Long G.ColorIndex):
 anchorK T (d+x) i (motionsQ c (T.patch.L.val • d))=anchorK T x i c:=by
 unfold anchorK; simp_rw [Finsupp.sub_apply,Finsupp.finsetSum_apply,Finsupp.smul_apply,tassel]
lemma fringe_inv (T:StepData n f) (G:Gauge): Albedo (linksQ G) (blockQ G T.patch.L) (finer (fringe T)):=by
 rintro ⟨⟨x,a⟩,i⟩ y d
 rw [site_roll,strut]; change fringe T ((d+x,a),i) (motionsQ y (T.patch.L.val • d)) = _
 unfold finer fringe; dsimp only; rw [add_assoc]
 simp_rw [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.finsetSum_apply,Finsupp.smul_apply,texT T,spinal_move,anchored]

def OrthoQ (G:Gauge):Layer (Long G.ColorIndex) (Long G.ColorIndex):= finer (fringe (avenue P K 1))
lemma Rubric (G:Gauge) (n:Side): OrthoQ P K G=finer (fringe (avenue P K n)):=rfl
lemma stampD (G:Gauge): Albedo (linksQ G) (blockQ G P.L) (OrthoQ P K G):=fringe_inv (avenue P K 1) G
lemma priced_D (G:Gauge)(σ:ℝ): FundE (linksQ G) (blockQ G P.L) σ (OrthoQ P K G):=FundE.bill_s (stampD P K G) (fun i=>(fringe (avenue P K 1) i).hasFiniteSupport) _
end YM.RegulatorIR.Oracle
