import YM.WilsonCoeffUV.Wick.Horizontal
import YM.WilsonCoeffUV.Step.Source
/-!
# Conditional Wick inheritance in native lattice units
Exact at periods on NullTop. In the limit at leading degree, order-independent.
-/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Carp
open Set Function Filter Lattice RG Laurent Exterior Bloch Metric Next.Free Precision Tree
open Matrix FreeResolvent Blue MvPolynomial
open scoped Topology ContDiff BigOperators ComplexConjugate
variable {U V:Type*}[Fintype U] [Fintype V]
variable {G:Gauge}{j k m N:ℕ}{n:Side} {s:ℝ} (k':ℝ)(v:Train j)
section
lemma glaze_thaw (K G:Matrix U U ℝ) (hg:G.transpose=G)(hk:K.transpose=K)(P:POL U): glaze G (glaze K P)=glaze (K+G) P:=by
   have ht : (K+G).transpose=K+G:=by rw [transpose_add,hg,hk]
   induction P using MvPolynomial.induction_on with
   | C a=> rw [glaze_constant,glaze_constant,glaze_constant]
   | add p q h t=> rw [map_add,map_add,map_add,h,t]
   | mul_X p i h =>
     rw [wick_poly K hk, map_add, wick_poly G hg, h, wick_poly _ ht]; simp_rw [map_sum,map_smul, glaze_deriv]; simp_rw [h]; simp_rw [Matrix.add_apply,add_smul,Finset.sum_add_distrib]; rw [add_right_comm, add_assoc]
omit [Fintype U] in
lemma cord_X (K:Matrix U V ℝ)(i:U) : cord K (X i)=∑ j, K i j • X j := by simp_rw [cord_var,Algebra.smul_def,MvPolynomial.algebraMap_eq]
lemma cord_D (K:Matrix U V ℝ)(P:POL U)(v: V) : pderiv v (cord K P)=∑ j:U,K j v • cord K (pderiv j P):=by
   induction P using MvPolynomial.induction_on with
   | C a=> simp [cord]
   | add p q h i=> simp [h,i,smul_add, Finset.sum_add_distrib]
   | mul_X p i h=>
      simp_rw [pderiv_mul,map_mul,pderiv_mul,map_add,map_mul]; rw [h]; simp_rw [smul_add, Finset.sum_add_distrib]; apply congr_arg₂ (· + ·); rw [Finset.sum_mul]; simp_rw [smul_mul_assoc]
      rw [Finset.sum_eq_single i]
      · rw [cord_X, map_sum, Finset.sum_eq_single v]<;> simp +contextual
      · intro x _ hx; simp [Ne.symm hx]
      simp
private lemma breathed (H:Matrix V V ℝ)(Q:Matrix U V ℝ)(b:U)(W:POL U): let M:= Q*H*Qᵀ
    ∑ j:V,Q b j • ∑ a:V,H j a • pderiv a (cord Q W) = ∑ i:U,M b i • cord Q (pderiv i W) := by
      intro M; simp_rw [cord_D, Finset.smul_sum, smul_smul]
      conv_lhs=> enter [2,j]; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro y _
      unfold M; simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_smul, Matrix.transpose_apply, mul_assoc]
      rw [Finset.sum_comm]
lemma daystar (Q:Matrix U V ℝ)(H:Matrix V V ℝ)(h:H.transpose=H)(P:POL U): glaze H (cord Q P)=cord Q (glaze (Q*H*Q.transpose) P):= by
   set K:=Q*H*Q.transpose; have hp:K.transpose=K:=by simp only [K,Matrix.transpose_mul,Matrix.transpose_transpose,h,Matrix.mul_assoc]
   induction P using MvPolynomial.induction_on with
   | C a=> rw [glaze_constant]; simp only [cord,aeval_C,MvPolynomial.algebraMap_eq,glaze_constant]
   | add p q hx hy=> rw [map_add,map_add,map_add,map_add,hx,hy]
   | mul_X p x ht=>
     rw [map_mul (cord Q),wick_poly K hp,map_add,map_sum,map_mul (cord Q)]
     simp_rw [cord_X, Finset.mul_sum,mul_smul_comm, map_sum,map_smul,wick_poly H h,smul_add,Finset.sum_add_distrib,glaze_deriv,ht]

     exact congr_arg (_ + ·) (breathed H Q x _)
omit [Fintype U] in
lemma composeC {A:Type*}[Fintype A](u:Matrix U V ℝ)(v:Matrix V A ℝ)(p:POL U):cord v (cord u p)=cord (u*v) p := by
   apply MvPolynomial.funext
   intro x; rw [cord_apply,cord_apply,cord_apply,Matrix.mulVec_mulVec]
end
section embed
variable [DecidableEq U][DecidableEq V]
omit [Fintype V] in
lemma clock_fill (G:Matrix U U ℝ) : fillSlots V G=(leftFlag U V)ᵀ * G * leftFlag U V :=by
   ext i j; simp_rw [Matrix.mul_apply, Matrix.transpose_apply, leftFlag, Matrix.of_apply, ite_mul,one_mul,zero_mul,mul_ite,mul_zero,mul_one]; cases i <;> cases j <;> simp [fillSlots]
lemma flag_left : leftFlag U V * (leftFlag U V).transpose=1:=by ext i j; simp_rw [leftFlag, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply,Matrix.of_apply,ite_mul]; simp [Matrix.one_apply]
lemma flag_right : rightFlag U V * (rightFlag U V).transpose=1:=by ext i j; simp_rw [rightFlag, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply,Matrix.of_apply,ite_mul]; simp [Matrix.one_apply]
lemma flag_other : leftFlag U V * (rightFlag U V).transpose=0:=by ext i j; simp_rw [leftFlag,rightFlag,Matrix.mul_apply,Matrix.of_apply,Matrix.transpose_apply,Matrix.of_apply,ite_mul]; simp
lemma flag_others : rightFlag U V * (leftFlag U V).transpose=0:=by have hv :=congr_arg Matrix.transpose (flag_other (U:=U) (V:=V)); simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] using hv
lemma gleams {X:Type*}[Fintype X](G:Matrix U U ℝ)(H: Matrix X U ℝ)(F: Matrix X V ℝ)(p:POL X) (h:G.transpose=G): let C:= H * leftFlag U V + F * rightFlag U V
    cord (plug:Matrix (U⊕V) V ℝ) (glaze (fillSlots V G) (cord C p))=cord F (glaze (H*G*H.transpose) p):=by
   intro C; rw [clock_fill]; let L:= leftFlag U V; let R:=rightFlag U V; let I:=Lᵀ*G*L; have hp : I.transpose= I:= by unfold I; simp [h, Matrix.mul_assoc]
   have he : C * L.transpose = H := by unfold C L; rw [Matrix.add_mul, Matrix.mul_assoc,Matrix.mul_assoc,flag_left,flag_others, Matrix.mul_one, Matrix.mul_zero,add_zero]
   have hh:L*C.transpose=H.transpose:=by rw [← he,Matrix.transpose_mul,Matrix.transpose_transpose]
   have hu: C*plug=F:=by unfold plug C; rw [Matrix.add_mul,Matrix.mul_assoc,Matrix.mul_assoc,flag_other,flag_right,Matrix.mul_one,Matrix.mul_zero,zero_add]
   rw [daystar _ _ hp,show C*I*C.transpose=H*G*H.transpose from (by unfold I; rw [← Matrix.mul_assoc C _ L,← Matrix.mul_assoc C, he, Matrix.mul_assoc _ L C.transpose,hh]
    ),composeC,hu]
end embed
section raw
variable {f c:Side}(S:StepData c f)(F:Forest S.ratio)(K Y:FaceRow)(Q:Matrix (Body 1 f) (Body 1 c) ℝ)
open PowerSeries
lemma jam (Ñ:ChartRatio G)(P:PChart G f)(h:shellK 2 P)(hp:LocalRatio Ñ)(T:PChart G f)(k:ℕ)(hx:shellK k T)(he:S.patch.Branches S.kernel G)(hu:(K.acts f).transpose=K.acts f)(hr:∀ i,Pure (P i))(hh:∀ i,Pure (T i)):
    totalR (reed S F K Q Ñ P k T 0)=cord (extractV G S F Q) (glaze (covariance G S F K) (totalR (T 0))):=by
    classical
    let H:=treeInverse G S F K 0
    let M:=extractV G S F Q
    let V:= inside S F K Q Ñ P
    have ht:H.transpose=H:=by unfold H treeInverse resolve; rw [zero_smul,add_zero,transpose_nonsing_inv,treeMatrix,transpose_submatrix,full_symmetric _ hu]
    have hK:= inside_reed S F K Q k h hp hx he hu hr hh
    have hR: constantCoeff (shot S F Q Ñ P)=0:= floor_pres (T:=loom (overM G S F)) (by simp [loom]) (flash_blank (pack_zero S hp))
    apply Eq.symm
    calc
     _ = PowerSeries.constantCoeff (insideMark S F K Q Ñ P T) := ?_
     _ = _ := by rw [hK,map_mul, inside_mass S F K Q hp,one_mul,← PowerSeries.coeff_zero_eq_constantCoeff_apply, flash,PowerSeries.coeff_mk]
    unfold insideMark Wick; rw [plug_project, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp_rw [loom,PowerSeries.coeff_map]; rw [overlay_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply,map_mul,raise_one hR, one_mul,← PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_map,flash,PowerSeries.coeff_mk, camber_tree]
    exact (gleams H (reveal G S F) M (totalR (T 0)) ht).symm
lemma curl_estuary (K G:Matrix U U ℝ)(P:POL U)(W Q: Matrix U U ℝ)(hg:K.transpose=K)(hp:W.transpose=W)(hq:Q.transpose=Q)(ht: cord (G*K) P=P)(hK:K*W*K=K*Q*K) : glaze W P=glaze Q P:= by
   have hh : (G*K) * W * (G*K).transpose = (G*K)*Q*(G*K).transpose := by simp only [Matrix.transpose_mul,hg,Matrix.mul_assoc]; congr 1; simp only [← Matrix.mul_assoc]; rw [hK]
   calc
     _ = glaze W (cord (G*K) P):=by rw [ht]
     _ = glaze Q (cord (G*K) P):=by rw [daystar _ _ hp,daystar _ _ hq,hh]
     _ = _ := by rw [ht]
end raw
section
variable (A:Levels G) (Ñ:ChartRatio G)(F:Forest (mStep A n m).ratio) (h:m<N)
local notation "C" => A.clock.kernel.penalty
local notation "S" => mStep A n m
local notation "H" => freeForms A N (m+1)
local notation "Y" => freeForms A N m
include h
lemma inheritedG (hp:LocalRatio Ñ)(P:PChart G (n*(loose A m).L))(q:shellK 2 P)(hh:∀ i,Pure (P i))(T:PChart G (n*(loose A m).L))(b:shellK k T)(hu:∀ i,Pure (T i))(p:NullTop (T 0))(hx:Bid.Larger (G:=G) S):
   let X:=roam A N m n; totalR (reed S F H X Ñ P k T 0)=cord (extractV G S F X) (glaze (covariance G S F H) (totalR (T 0))) ∧
    glaze (ColorStar C (location A N m) G n) (totalR (reed S F H X Ñ P k T 0))=cord (extractV G S F X) (glaze (ColorStar C (location A N (m+1)) G (n*(loose A m).L)) (totalR (T 0))):=by
    intro X; let Q:= ColorStar C (location A N m) G n; let W:=ColorStar C (location A N (m+1)) G (n*(loose A m).L); let E:=extractV G S F X; let I:= covariance G S F H
    have ht:(mStep A n m).patch.Branches A.clock.kernel G:= (A.blocks m 0).branches
    obtain ⟨a,ha,hA⟩:= vacuum_positive _ A.clock.kernel.penalty_pos (A.clock.adm (m+1)); obtain ⟨z,w⟩:=hA (location A N (m+1)) (n*(loose A m).L)
    have he := jam S F H X Ñ P q hp T k b ht z hh hu
    refine ⟨he,?_⟩; rw [he]
    let D:=precisionC G (n*(loose A m).L) H
    have hm:Q.transpose=Q:=colorS_sym _ _ A.clock.kernel.penalty_pos _
    have hv:I.transpose=I:= by
       unfold I covariance; have Hx:(treeInverse G S F H 0).transpose=treeInverse G S F H 0:=by rw [treeInverse,resolve,zero_smul,add_zero,transpose_nonsing_inv,treeMatrix,transpose_submatrix,show (fullMatrix G S H).transpose=fullMatrix G S H from full_symmetric (G:=G) H z]
       rw [Matrix.transpose_mul,Matrix.transpose_mul,Hx,FreeResolvent.reduce,Matrix.transpose_transpose,Matrix.mul_assoc]
    have hg:(E*Q*E.transpose).transpose=E*Q*E.transpose:=by simp only [Matrix.transpose_mul,Matrix.transpose_transpose,hm,Matrix.mul_assoc]
    rw [daystar _ _ hm,glaze_thaw _ _ hg hv]
    change cord E (glaze (I+E*Q*E.transpose) (totalR (T 0)))=cord E (glaze W (totalR (T 0)))
    apply congr_arg (cord E)
    refine curl_estuary D W (totalR (T 0)) _ W (kinetic_sym z) (by rw [transpose_add,hg,hv]) (colorS_sym _ _ A.clock.kernel.penalty_pos _) (canopied _ _ A.clock.kernel.penalty_pos (A.clock.adm _) (T 0) p) ?_
    exact midLinks S F H Y X z (age_sym A N m n) (horizon_step A m N h n (n*(loose A m).L) rfl) a ha w hx W Q (colorFold _ _ A.clock.kernel.penalty_pos (A.clock.adm _) _) (colorFold _ _ A.clock.kernel.penalty_pos (A.clock.adm _) _)
end
end YM.WilsonCoeffUV.Bank.Carp
