import YM.OPE.Compatible.Chain.Twit
/-!
# virtual Feynman solution. source on full torus, *raw gauge* x, inverse is finite images not treating them as indpt -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP
local notation "M" => TypeFace 1
variable (H: Even n.val) {C:KernelChoices}{r:ℕ}
omit H in abbrev acrossH (x:form 1 n): form 1 n:= ∑ k:Kv,stem k x
include H
lemma staid (v: form 1 n)(k:Kv): stem k (acrossH v)=acrossH v:=by simp only [acrossH,map_sum]; simp_rw [stemP H]; exact Equiv.sum_comp (Equiv.addRight k) (fun i:Kv=> stem i v) -- infer
omit H in lemma StemClip (u:form 1 n): (∀ k,stem k u=u)↔Ell (loadV u):=by
     constructor
     · intro h k p; exact ((stemR k u p).symm.trans (congr_fun (h k) (addressR p))).symm
     intro h k; funext i; obtain ⟨v,rfl⟩:=addressR.surjective i; rw [stemR]; exact (h k v).symm
omit H in lemma blind (u:form 1 n)(hu:storm u): missing n *ᵥ u=0 := by
      funext i; rcases i with ⟨v,a⟩; obtain ⟨a,rfl⟩:=axisEquiv.surjective a; unfold Matrix.mulVec dotProduct; rw [Fintype.sum_prod_type]; simp_rw [projected]; simp [ite_mul,← Finset.mul_sum,coord_map,hu a]
lemma specter (h:4 ≤ r)(v:Train r)(x u:form 1 n)(ht:∀ k,stem k u=u):
    u ⬝ᵥ (major (ShellRow C v) n *ᵥ acrossH (lineC (ShellRow C v) n *ᵥ x))=4*(u ⬝ᵥ x):=by
       let A:=ShellRow C v; let B:=major A n; let P:=lineC A n*ᵥ x; let X:=missing n; change u ⬝ᵥ (B *ᵥ _) = _; rw [acrossH,Matrix.mulVec_sum,dotProduct_sum]; have he(k:Kv): u ⬝ᵥ (B*ᵥ stem k P)=u ⬝ᵥ x:=by
           have hv:= StemClip u |>.mp ht; have hz: u ᵥ* X=0:= by rw [show X=Xᵀ by ext ⟨u,i⟩ ⟨v,j⟩; simp [X,projected,eq_comm (a:=i)], vecMul_transpose]; exact blind _ (h_storm H u hv)
           rw [show (B*ᵥstem k P)=_ from leadT H v h _ k,← stemPair H, ht]; rw [show B*ᵥ P=(1-X)*ᵥ x by rw [show P=_ from rfl, mulVec_mulVec, (show B*lineC A n=_ from (neutralize n h v).1)],Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub,dotProduct_mulVec u X x, hz,zero_dotProduct,sub_zero]
       change ∑ k:Kv,u ⬝ᵥ (B*ᵥstem k P)= _; simp [he,kvCard]
end YM.OPE.Cascade.Terp
