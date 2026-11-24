import YM.OPE.Compatible.Chain.Mold
/-!
# orthogonal quotient
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP
local notation "M" => TypeFace 1
abbrev addressR : edgeV n≃ Body 1 n:= Equiv.prodCongr (Equiv.refl _) axisEquiv
def stem (k:Kv): form 1 n→ₗ[ℝ] form 1 n where
    toFun f i:= let p:= addressR.symm i; if (axisK k).flip p.2 then -f (addressR (ferry k p)) else f (addressR (ferry k p))
    map_add' p q:=by ext i; simp only [Pi.add_apply];split<;>simp [add_comm]
    map_smul' p q:=by ext i; simp only [Pi.smul_apply, RingHom.id_apply];split<;>simp
lemma stemR (k:Kv)(x: form 1 n)(p:edgeV n) : stem k x (addressR p)= if (axisK k).flip p.2 then -x (addressR (ferry k p)) else x (addressR (ferry k p)) := by
     change (if (axisK k).flip _ then _ else _)=_; rw [Equiv.symm_apply_apply]
@[simp] lemma stem0 (x:form 1 n): stem 0 x=x:= by funext i; obtain ⟨p,rfl⟩:=addressR.surjective i; rw [stemR]; simp
variable (H:Even n.val)
include H
lemma stemP (k h:Kv)(x:form 1 n): stem k (stem h x)=stem (h+k) x:=by
   funext i; obtain ⟨p,rfl⟩:=addressR.surjective i; rw [stemR,stemR (h+k),axisK_plus,Signed.mul_flip,axis_pin,ferry_plus H,stemR,ferry_axis]; cases e:(axisK h).flip p.2 <;> cases t:(axisK k).flip p.2<;>simp
lemma stemSelf (k:Kv)(x:form 1 n):stem k (stem k x)=x:=by rw [stemP H,twinned,stem0]
lemma stemPair (k:Kv)(x y:form 1 n): dotProduct (stem k x) y= dotProduct x (stem k y):=by
     have he(x y:form 1 n): dotProduct (stem k x) (stem k y)=dotProduct x y:=by
        unfold dotProduct; rw [← Equiv.sum_comp addressR (fun u=>stem k x u*stem k y u),← Equiv.sum_comp addressR (fun u=> x u*y u)]; let V(p:edgeV n):= x (addressR p)*y (addressR p); change _=∑ i:edgeV n,V i; rw [← Equiv.sum_comp (swoop H k) V]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [stemR,stemR]; unfold V; split; next hk=>rw [neg_mul_neg];rfl
        next hk=> rfl
     conv_lhs=>rhs;rw [← stemSelf H k y]
     exact he ..
def stud (k:Kv): form 0 n→form 0 n :=fun x p=> x (decks k p.1,p.2)
lemma studSelf (k:Kv)(x:form 0 n): stud k (stud k x)=x:=by ext i; unfold stud; rw [← decks_plus H,twinned,flats]
lemma studPair (k:Kv)(x y:form 0 n):dotProduct (stud k x) y=dotProduct x (stud k y):=by
      have he(p q:form 0 n): dotProduct (stud k p) (stud k q)=dotProduct p q:= Equiv.sum_comp (Equiv.prodCongr (roam H k) (Equiv.refl (TypeFace 0))) (fun i=>p i*q i) -- infer
      conv_lhs=>rhs;rw [← studSelf H k y]
      exact he ..
omit H in lemma stemG (k:Kv)(x:form 0 n) : stem k (grad n*ᵥx)=grad n*ᵥ stud k x :=by
     ext i; obtain ⟨⟨p,j⟩,rfl⟩:=addressR.surjective i -- name conflicts
     rw [stemR]; unfold grad; rw [show addressR (p,j)=(p,coord j) from rfl,d_sites]; unfold stud; dsimp only; rw [← Step.vec_pos, decks_walk]; unfold ferry; simp only [Step.rotate,posDir,Bool.false_xor,axis_pin,Step.vec,Step.used]; cases h:(axisK k).flip j
     · exact d_sites ..
     simp only [↓reduceIte]; rw [show addressR (decks k p-step j,j)=(decks k p-step j,coord j) from rfl,d_sites]; simp [sub_eq_add_neg]
omit H in lemma speck {I:Type*}[Fintype I]{x y:I→ ℝ}(h:∀ z,z ⬝ᵥ x=z ⬝ᵥ y):x=y:=by funext i; simpa using h (Pi.single i 1)
lemma adjG (k:Kv)(x:form 1 n): (grad n)ᵀ *ᵥ (stem k x)=stud k ((grad n)ᵀ*ᵥ x):=by
     apply speck; intro i; rw [dotProduct_mulVec,vecMul_transpose, ←stemPair H,stemG,← studPair H, dotProduct_mulVec (stud k i),vecMul_transpose]
omit H
variable {C:KernelChoices}{r:ℕ}
def loan (z:Site n)(x:form 1 n) : form 1 n:=fun p=>x (p.1+z,p.2)
lemma lender (k:Kv)(x:form 1 n): stem k x=reorient (axisK k) (loan (offset k n) x):=by
     ext i; obtain ⟨⟨x,j⟩,rfl⟩:= addressR.surjective i; rw [stemR]; rcases hk:(axisK k).flip j; all_goals simp [reorient,loan,ferry,decks, addressR,Step.used, Step.rotate, posDir,affine, hk,sub_add_eq_add_sub,← coord_map]
-- translations
lemma loanT (P:Row M M)(x y:form 1 n)(z:Site n): loan z x ⬝ᵥ P.acts n *ᵥ loan z y=x ⬝ᵥ P.acts n*ᵥ y:=by
      let V:= Equiv.prodCongr (Equiv.addRight z) (Equiv.refl (TypeFace 1)); conv_rhs=> rw [dotProduct, ← Equiv.sum_comp V (fun i=>x i*(P.acts n*ᵥy) i)]
      refine Finset.sum_congr rfl fun i _=>congr_arg₂ _ rfl ?_; rw [mulVec]; unfold mulVec dotProduct; rw [← Equiv.sum_comp V (fun j=> P.acts n (V i) j*y j)]; refine Finset.sum_congr rfl fun j _=> congr_arg₂ _ ?_ rfl; change (∑' k,ite (j.1=i.1+wrap n k) _ (_:ℝ))=∑' k,ite (j.1+z=i.1+z+wrap n k) _ _; simp only [add_right_comm i.1 z, add_left_inj]; rfl
include H
lemma leadT (v:Train r)(h:4 ≤ r)(x:form 1 n)(k:Kv): major (ShellRow C v) n*ᵥ stem k x= stem k (major (ShellRow C v) n*ᵥ x):=by
     apply speck; intro y; rw [← stemPair H]; -- H
     have he:= apply_bill (axisK k) C.penalty C.penalty_pos h v n
     unfold major; simp_rw [add_mulVec,dotProduct_add]; congr 1
     · have hk(a b: form 1 n): dotProduct (stem k a) ((ShellRow C v).acts n*ᵥ stem k b)= dotProduct a ((ShellRow C v).acts n*ᵥ b):= by rw [lender,lender,show (ShellRow C v).acts n=_ from Woody.Op_stays h v n, he, ← show (ShellRow C v).acts n=_ from Woody.Op_stays h v n, loanT]
       simpa [stemSelf H] using hk (stem k y) x
     · rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,adjG H k, ← stemG,← stemPair H]
end YM.OPE.Cascade.Terp
