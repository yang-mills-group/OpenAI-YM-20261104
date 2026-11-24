import YM.OPE.Compatible.Words.Hat
/-!
# Matrix stockings. natural transformations on Laplacians
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt
open MeasureTheory Function Finset Filter Module Matrix Cascade Cascade.Paver
open scoped Topology BigOperators Classical ContDiff
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial
variable {I J K:Type}[Fintype I][Fintype J]{n k d:ℕ}
local notation "Λ"=> PAD I
local notation "Γ"=> PAD J
-- geometric argument. not use symmetry of X
lemma sandstone (P X Y:Mat I) (Z: Matrix I I ℝ) (V:Mat I)(hz: ∀ x:Λ,Health P (Z*ᵥ x))(ht:∀ x:Λ,Health P x→Z*ᵥ x=x)(hp:∀ x y:Λ, Health P x→ Health P y→x ⬝ᵥ( X*ᵥ y)=x ⬝ᵥ(Y *ᵥ y))
   (hv:∀ j,Health P (V j))(hr:∀ j, Health P (Vᵀ j)):
     ∑ i,∑ j,X i j* V i j= ∑ i,∑ j,Y i j*V i j:=by
         have he:V=Z*V* Zᵀ:=by
              have hh : Z* V=V:=by ext i j; exact congr_fun (ht (Vᵀ j) (hr j)) i
              rw [hh]; ext i j; have h:= congr_fun (ht (V i) (hv i)) j; rw [mul_apply]; exact h.symm.trans (sum_congr rfl fun k _=> mul_comm ..)
         have hR(T:Mat I): (∑ i:I,∑ j:I, T i j*V i j)=∑ a:I, ∑ b:I, V a b*((Zᵀ a) ⬝ᵥ (T*ᵥ (Zᵀ b))):=by
              conv_lhs=> rw [he]
              simp_rw [Matrix.mul_apply,Finset.sum_mul,Finset.mul_sum]; unfold dotProduct Matrix.mulVec; -- note mulVec uses dotProduct again
              -- order L i,j,y,a. move front with grouping
              rw [send]; unfold dotProduct; simp_rw [Finset.mul_sum]; refine sum_congr rfl fun a _=> sum_congr rfl fun b _=> sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; simp only [Matrix.transpose_apply]; ring
         rw [hR X,hR Y]; have hx(i:I):Health P (Zᵀ i):= by have h:=hz (Pi.single i 1); rw [Matrix.mulVec_single_one] at h; exact h -- theorem returns fun?
         exact sum_congr rfl fun i _=> sum_congr rfl fun j _=> congr_arg (V i j* ·) (hp _ _ (hx _) (hx _))
where send (f : I→I→I→I→ℝ): (∑ i,∑ j,∑ k,∑ l,f i j k l)=∑ l,∑ k,∑ i,∑ j,f i j k l:=by
            let g(a b:I×I):= f a.1 a.2 b.1 b.2; rw [show (∑ i,∑ j,∑ k,∑ l,f i j k l)=∑ i:I×I,∑ j:I×I,g i j from ?_,Finset.sum_comm]; swap; · simp_rw [Fintype.sum_prod_type];rfl
            rw (occs:=.pos [2]) [sum_comm]; simp_rw [Fintype.sum_prod_type];rfl
-- any covariance Tlat
abbrev climbs {X Y:Type}[Fintype X][Fintype Y](M:Matrix X Y ℝ): PAD Y→L[ℝ] PAD X:= LinearMap.toContinuousLinearMap M.mulVecLin
def pulling (M:Matrix I J ℝ): Song Λ→ₗ[ℝ] Song Γ where
    toFun p i:=(p i).compContinuousLinearMap fun _=>climbs M
    map_add' a b:=by ext i v; rfl
    map_smul' a b:=by ext i v; rfl
lemma columnAlong (X:Mat I)(Y:Mat J)(M:Matrix I J ℝ)(hh:X=M*Y*Mᵀ)(p:Pole Λ (n+2)):
     Semester Y (p.compContinuousLinearMap (fun _=>climbs M))=(Semester X p).compContinuousLinearMap (fun _=>climbs M):=by
          ext1 u; rw [stanzaR]; change _=Semester X p _; rw [stanzaR,hh]; simp_rw [Matrix.mul_apply,sum_mul]; let f:=climbs M; let v:=f ∘ u; let z(i j:I):= p (Fin.cons (Pi.single i 1) (Fin.cons (Pi.single j 1) v)); let y(i:J):=Pi.single (M:=fun _=>ℝ) i 1; let Z(i j:I)(a b:J):=Y a b*M i a*M j b*z i j
          have ht (k:ℕ) (i:J)(T:Pole Λ (k+1)) : T.curryLeft (f (y i))=∑ j,M j i • T.curryLeft (Pi.single j 1):=by rw [brewC]; apply sum_congr rfl; intro j _; rw [show f _ j=M j i from (by change (M*ᵥ(Pi.single _ 1)) j=_; simp)]
          have he(i j:J): (p.compContinuousLinearMap (fun _=>f)) (Fin.cons (y i) (Fin.cons (y j) u))=(p.curryLeft (f (y i))).curryLeft (f (y j)) v:=by change p _=p _; congr 1; funext k; exact Fin.cases rfl (fun i=>Fin.cases rfl (fun j=>rfl) i) k -- dependent
          have hb(i j:J):(p.curryLeft (f (y i))).curryLeft (f (y j)) v= ∑ a, ∑ b,M a i*M b j*z a b:=by
               rw [ht (k:=n+1) i p]; -- curry linear Continuous API
               rw [ContinuousMultilinearMap.curryLeft_apply,_root_.sum_apply]; apply sum_congr rfl; intro a _; change M a i*((p.curryLeft (Pi.single a 1)).curryLeft (f (y j)) v)= _; rw [ht n j, _root_.sum_apply, Finset.mul_sum]; apply sum_congr rfl; intro b _; change M a i*(M b j*z a b)=_; rw [mul_assoc]
          change (∑ i:J,∑ j:J,Y i j*(p.compContinuousLinearMap (fun _=>f)) (Fin.cons (y i) (Fin.cons (y j) u)))= _; simp_rw [he,hb,mul_sum]; rw [moves]

          refine sum_congr rfl (fun i _=>sum_congr rfl fun j _=>sum_congr rfl fun k _=>sum_congr rfl fun l _=>?_); change Y l k*( M i l * M j k * z i j)= M i l*Y l k*M j k * z i j; ring
where moves (f:J→J→I→I→ℝ): (∑ i,∑ j,∑ k,∑ l,f i j k l)=∑ k,∑ l,∑ j,∑ i,f i j k l:=by
            let g(a:J×J)(b:I×I):= f a.2 a.1 b.1 b.2; rw [Finset.sum_comm,show (∑ j,∑ i,∑ k,∑ l,f i j k l)=∑ i:J×J,∑ j:I×I,g i j from ?_,Finset.sum_comm]; swap; · simp_rw [Fintype.sum_prod_type];rfl
            simp_rw [Fintype.sum_prod_type];rfl
