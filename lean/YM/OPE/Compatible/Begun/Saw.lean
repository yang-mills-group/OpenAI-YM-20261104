import YM.OPE.Compatible.Begun.Vigor
/-!
# Tensor Schur identity
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Paver
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d:ℕ}{K:KernelChoices}
section
variable {S:StepData c f}{V:Forest S.ratio}{v:Train i}{u:Train j} {A:Cross S.ratio.count (TypeFace 1) (TypeFace 1)}
local notation "Q" => S.kernel
local notation "E"=> tensor G (extracted S V (installed S.ratio A))
local notation "P"=> Prog S.kernel v G f
local notation "P'"=> Prog S.kernel u G c
local notation "T"=> probe S
variable (S) (V) (A) (u) (v) (h:Inputs S (installed S.ratio A) ((pink S.kernel.penalty v).acts f) ((pink S.kernel.penalty u).acts c))
include h
lemma basesK (x:Vec G c 1) : P*ᵥ (E*ᵥ x)=(tensor G Tᵀ)*ᵥ( P'*ᵥx):=by
    funext i; obtain ⟨a,b,z⟩:= i; change component (P*ᵥ(E *ᵥx)) z (a,b)=component ((tensor G Tᵀ)*ᵥ(P'*ᵥx)) z (a,b); unfold Prog; simp_rw [component_mul]; rw [mulVec_mulVec (component x z), (stationed V _ _ _ h).2, ← Matrix.mulVec_mulVec]
lemma baseFC (x:Vec G c 1): fullMatrix G S (pink S.kernel.penalty v) *ᵥ (E*ᵥx) = S.kernel.penalty • (tensor G Tᵀ*ᵥ x):=by
     funext i; obtain ⟨a,b,z⟩:= i; let M:=fullMatrix G S (pink S.kernel.penalty v); change component (M*ᵥ(E*ᵥx)) z (a,b)= S.kernel.penalty * component (tensor G Tᵀ*ᵥx) z (a,b); unfold M fullMatrix; simp_rw [component_mul]; rw [mulVec_mulVec (component x z),firesField S V A (pink S.kernel.penalty v) (pink S.kernel.penalty u) h, smul_mulVec]; rfl
omit h in
lemma form9 (x:Vec G f 1): fullMatrix G S (pink S.kernel.penalty v) *ᵥ x= P*ᵥx+ S.kernel.penalty • (tensor G Tᵀ *ᵥ (tensor G T*ᵥ x)):=by
     funext i; obtain ⟨a,b,z⟩:= i; let M:=fullMatrix G S (pink S.kernel.penalty v); change component (M*ᵥx) z (a,b)= component (P*ᵥx) z (a,b)+S.kernel.penalty * component (tensor G Tᵀ*ᵥ (tensor G T*ᵥ x)) z (a,b); unfold M fullMatrix Prog; simp_rw [component_mul,baseMatrix]; rw [Matrix.add_mulVec,smul_mulVec, ← Matrix.mulVec_mulVec]; rfl
lemma course (t:Vec G f 1)(ht:Health P t): Health P' (Eᵀ*ᵥ t):=by
     intro x hx; rw [← entrusted]; apply ht; rw [basesK _ _ _ _ _ h,hx,mulVec_zero]
lemma routeBase (x:Vec G f 1)(hi:4 ≤ i)(hj:4 ≤ j): Eᵀ*ᵥ (P*ᵥx)= P'*ᵥ (tensor G T*ᵥ x):=by
     suffices hh : Eᵀ*P=P'*tensor G T by rw [mulVec_mulVec x Eᵀ,hh, ← mulVec_mulVec]
     have hh: P*E=tensor G Tᵀ* P':=by apply Matrix.ext_of_mulVec_single; intro u; simp_rw [← mulVec_mulVec]; exact basesK _ _ _ _ _ h _ -- name
     have H:= congr_arg (fun (a:Matrix _ _ ℝ)=>aᵀ) hh; rw [transpose_mul,transpose_mul,tensor_transpose G Tᵀ,alignZ _ _ _ hi, alignZ _ _ _ hj, transpose_transpose] at H; exact H
omit h u v in
lemma spunE (x:Vec G c 1): Vanishes V (E*ᵥx):=by intro z; rw [component_mul]; exact Precision.stays V (installed S.ratio A) _ -- against mark
-- κ G pending
set_option maxHeartbeats 200000 in
lemma rollingK (x y:Vec G f 1)(hx:Health P x)(hy:Health P y)(hi:4 ≤ i)(hj:4 ≤ j)(hp:(treeMatrix G S V (pink S.kernel.penalty v)).PosDef):
     let L:= FreeResolvent.insertion (plant V (G:=G)); let C:= treeMatrix G S V (pink S.kernel.penalty v); let M:= E
     x ⬝ᵥ (PhV Q v G f *ᵥy)= (Mᵀ*ᵥx) ⬝ᵥ (PhV Q u G c *ᵥ(Mᵀ*ᵥ y)) + (Lᵀ*ᵥ x) ⬝ᵥ (C⁻¹*ᵥ(Lᵀ*ᵥ y)):=by
          intro L C M
          let t:=PhV Q v G f *ᵥy; let w:= representative S V t; let Y:=tensor G T *ᵥ w; let z:=PhV Q u G c*ᵥ(Mᵀ*ᵥy); let k:= reduce G S V; let x':=w-M*ᵥY; let Z:=k*ᵥ x'
          have hf:P*ᵥw=y:=by unfold w representative; rw [Matrix.mulVec_add,show P*ᵥ t=y from HealthN hi v y hy,raster,add_zero]
          have hw: x ⬝ᵥ t=x ⬝ᵥ w:=by unfold w representative; rw [dotProduct_add,hx (gradient _) (raster _ _),add_zero]
          have hpK:P'*ᵥz=Mᵀ*ᵥy:=HealthN hj u _ (course S V v u A h y hy); have ht:P'*ᵥY=Mᵀ*ᵥy:=by rw [← hf]; exact (routeBase _ _ _ _ _ h w hi hj).symm
          have hc:= course S V v u A h x hx; have he: (Mᵀ*ᵥ x) ⬝ᵥ Y= (Mᵀ*ᵥ x) ⬝ᵥ z:=sub_eq_zero.mp (by rw [← dotProduct_sub]; exact hc _ (by rw [mulVec_sub, ht,hpK,sub_self]))
          let W:= fullMatrix G S (pink S.kernel.penalty v)
          have ha: W*ᵥx'= y:=by unfold x' W M; rw [Matrix.mulVec_sub, form9 S v w,baseFC _ _ _ _ _ h Y,hf]; exact add_sub_cancel_right y _
          have hL : L*ᵥ Z=x':=by unfold Z x'; rw [mulVec_sub,mulVec_sub,show L*ᵥ (k*ᵥ w)= w from projects V _ (onto_slice V t),show L*ᵥ(k*ᵥ( M *ᵥ Y))=M*ᵥ Y from projects V _ (spunE S V A Y)]
          have h₁:C*ᵥ Z=Lᵀ*ᵥy:=by rw [show C=Lᵀ*W*L from (insertion.compress ..).symm,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,hL,ha]
          have h₂:C⁻¹*ᵥ(Lᵀ*ᵥy)=Z:=by rw [← h₁,Matrix.mulVec_mulVec Z C⁻¹,Matrix.nonsing_inv_mul _ (hp.det_pos.ne'.isUnit), Matrix.one_mulVec]
          change x ⬝ᵥ t= _; rw [hw,h₂,show (Mᵀ*ᵥ x) ⬝ᵥ (PhV Q u G c*ᵥ (Mᵀ*ᵥ y))= (Mᵀ*ᵥx) ⬝ᵥY from he.symm, ← entrusted, ← entrusted,hL,← dotProduct_add]; unfold x'; rw [add_comm (M*ᵥY), sub_add_cancel]

end
end YM.OPE.Cascade.Paver
