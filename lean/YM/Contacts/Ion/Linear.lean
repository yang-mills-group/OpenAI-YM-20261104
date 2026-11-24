import YM.Contacts.Ion.Phase
namespace YM.Contacts.Lyre
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie Harrier Sequent
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y ι κ α β: Type}{m:Side}{n k i r l j M D:ℕ}{ζ σ:ℝ≥0}
open UVNext PricedKernels Next.Free Lattice Tree FreeResolvent
open PertExtension.Orb MeasureTheory
namespace Align
open Spark
variable {f:Side}(S:StepData m f)(h:S.patch.Branches S.kernel G)
local notation "ιX"=>Align.inverse
local notation "Ξ"=>orderTurn ιX
local notation "ΞX"=> Link G m
local notation "Φ" => flax G S
local notation "Θ" => House.Dir (Yard G S)
open PhysicalNext.RankCovariance Spark House
variable {S}{J:Astro G S}{R P:FreeResolvent.FaceRow} (B:Beam S G J P R b)
local notation "Ω"=> Active G (Forestry S)
local notation "ρp"=> plant (G:=G) (Forestry S)
def pall (i:Active G (Forestry S)): Active G (Forestry S):= (⟨reflect i.1.val, mt (trunk S _).1 i.1.property⟩,i.2)
lemma pall_inv : Involutive (pall (S:=S) (G:=G)):= fun _=> Prod.ext (Subtype.ext (reflect_reflect _)) rfl
def spin_active (v:House.Dir Ω): House.Dir Ω:= fun i=> -(v (pall i))
local notation "Yx"=> (spin_active (S:=S) (G:=G))
lemma root_p (i:Ω): shadow (ρp i)=ρp (pall i):= by unfold plant FreeResolvent.ix Align.pall reflect shadow; rw [show axisEquiv.symm (coord _)=i.1.val.2 from axisEquiv.symm_apply_apply _]
lemma pallet (x y:House.Dir Ω): Yx x ⬝ᵥ Yx y=x ⬝ᵥ y:= by simp_rw [dotProduct, spin_active,neg_mul_neg]; exact Equiv.sum_comp (Equiv.ofBijective (pall (S:=S)) pall_inv.bijective) (fun i=> x i*y i)
lemma skew (x y: House.Dir Ω): x ⬝ᵥ Yx y=Yx x ⬝ᵥ y:= by rw [←pallet x (Yx y),show Yx (Yx y)=y from funext fun i=> by simp only [spin_active,neg_neg]; rw [pall_inv]]
local notation "Ψ" => insertion ρp
lemma pivot (x:Link G f): Ψᵀ *ᵥ (Ξ x)= Yx (Ψᵀ *ᵥ x) := by
   change reduce _ _ _*ᵥ _ = Yx (reduce _ _ _ *ᵥ _); rw [reduce_actual,reduce_actual]; exact funext fun i=> (luminosity x (ρp i)).trans (by unfold spin_active; rw [root_p]; rfl)
lemma plunge (x:House.Dir Ω) : Ψ *ᵥ Yx x= Ξ (Ψ *ᵥ x):= morning (fun i=>by rw [←polarity,dotProduct_comm i,dotProduct_comm (Ξ _),insertion.dot_push,insertion.dot_push,pivot,skew])
-- Hessian covariance from atmosphere actual data
variable {Q:House (Lines G f 1)}(A:Chest Q P)(L: sealed Q 3)
include A L
lemma spinner (x:Link G f): let v:= spindle G f P; Ξ x ⬝ᵥ (v *ᵥ Ξ x) = x ⬝ᵥ (v *ᵥ x) := by
   intro v; let g:=wind Q 3 0; have hl:= L 0 (by decide); have he x: jet g 2 x=x ⬝ᵥ (v*ᵥ x)/2:= (wind_jet ..).trans ((if_pos (by decide)).trans (A.glow _)); have hu:= he (Ξ x); have hk: g ∘ Ξ = g:= funext (hl.spins _); rw [← Garf.woven (F:=g) hl.analytic Ξ x 2,hk,he] at hu; linarith only [hu]
include B
lemma spat (x: Link G f): let v:= spindle G f P; v *ᵥ (Ξ x)= Ξ (v *ᵥ x):= by
   intro v; have hh:vᵀ=v := by simp only [v,spindle,tensor_transpose,Precision.K,transpose_mul,B.sym_eq,transpose_transpose,Matrix.mul_assoc]
   have ht x y:x ⬝ᵥ (v *ᵥ y)=y ⬝ᵥ (v*ᵥ x):= by rw (occs:=.pos [1]) [←hh]; rw [dotProduct_transpose_mulVec]; -- dots
   have he (x y:Link G f):Ξ x ⬝ᵥ (v *ᵥ Ξ y)=x ⬝ᵥ (v *ᵥ y):= by have hz:= spinner A L (x+y); change _ ⬝ᵥ (v *ᵥ _) = _ ⬝ᵥ (v *ᵥ _) at hz; rw [map_add] at hz; simp only [Matrix.mulVec_add,dotProduct_add,add_dotProduct] at hz; rw [show Ξ x ⬝ᵥ (v*ᵥ Ξ x)= _ from spinner A L x,show Ξ y ⬝ᵥ (v*ᵥ Ξ y)= _ from spinner A L y, ht (Ξ y) (Ξ x),ht y x] at hz; linarith only [hz]
   exact morning fun i=>by rw [←polarity,←he (Ξ i),invert_spin]
omit A L in
lemma share (x: Link G m): Φᵀ *ᵥ (Ξ x)=Ξ (Φᵀ *ᵥ x):= morning fun i=> by rw [dotProduct_transpose_mulVec,polarity,←polarity i,dotProduct_transpose_mulVec, ← hunger S B.light.1] -- omit A L
lemma sequel (x:Link G f): (fullMatrix G S P)*ᵥ Ξ x=Ξ (fullMatrix G S P*ᵥ x):= by simp_rw [fullMatrix,baseMatrix,promote_sum,promote_coeff, promote_prod,← tensor_transpose,Matrix.add_mulVec,Matrix.smul_mulVec,show tensor G (probe S)=Φ from rfl, ← Matrix.mulVec_mulVec,← hunger S B.light.1,map_add, share B,show tensor G (Precision.K (P.acts f))=spindle G f P from rfl,spat B A L,map_smul]
local notation "κx"=> treeMatrix G S (Forestry S) P
local notation "Ax"=> treeInverse G S (Forestry S) P 0
local notation "Fx"=> fullMatrix G S P
local notation "Σx"=> covariance G S (Forestry S) P
local notation "ιD"=> atr G S J
lemma covenant (v: House.Dir Ω): κx *ᵥ Yx v= Yx (κx *ᵥ v) := by
   rw [show κx=Ψᵀ * Fx * Ψ from (insertion.compress _ _).symm]; simp_rw [← Matrix.mulVec_mulVec, plunge,sequel B A L,pivot]
lemma bellum (v: House.Dir Ω): Ax*ᵥ Yx v= Yx (Ax*ᵥ v):= by rw (occs:=.pos [1]) [←Matrix.one_mulVec (α:=ℝ) v]; rw [← (fence_laws B).2,← Matrix.mulVec_mulVec,← covenant B A L,Matrix.mulVec_mulVec _ Ax,(fence_laws B).1, Matrix.one_mulVec] -- name
lemma coverlet (v : Link G f): Σx *ᵥ Ξ v=Ξ (Σx *ᵥ v):= by simp_rw [FreeResolvent.covariance, FreeResolvent.reduce,← Matrix.mulVec_mulVec,pivot,bellum B A L,plunge]
lemma cork (x:Link G m): ιD *ᵥ Ξ x=Ξ (ιD *ᵥ x):= by
   have he (v:Link G m) : ιD *ᵥ v= Σx *ᵥ (S.kernel.penalty • (Φᵀ *ᵥ v)):= by
      have hx : Fx*ᵥ (ιD *ᵥ v) = S.kernel.penalty • (Φᵀ *ᵥ v):= by rw [Matrix.mulVec_mulVec,(beamθ B).1,Matrix.smul_mulVec]
      let k:= Ψᵀ *ᵥ (ιD *ᵥ v); rw [←hx,← show Ψ *ᵥ k= _ from traceθ B v,FreeResolvent.covariance]; erw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ (reduce _ _ _),Matrix.mulVec_mulVec k (_*_), show reduce G S _*Fx*Ψ=κx from insertion.compress _ _, Matrix.mulVec_mulVec k Ax, (fence_laws B).1,Matrix.one_mulVec]
   rw [he x,he (Ξ x),share B,← map_smul,coverlet B A L]
end Align
end
end YM.Contacts.Lyre
