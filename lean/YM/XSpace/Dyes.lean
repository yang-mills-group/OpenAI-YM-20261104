import YM.XSpace.Spheres
/-!
# Color orthogonal action (not just Ad). Gram and Gaussian Jets
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal Matrix MvPolynomial
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff Classical
variable {D J:Type*}[Fintype D][Fintype J][DecidableEq J]
abbrev OJoint (J:Type*) [Fintype J][DecidableEq J] := Matrix.orthogonalGroup J ℝ
instance : CompactSpace (OJoint J):= by
  have hv : ∀ p : Matrix J J ℝ, p∈OJoint J→ ‖p‖^2=(Fintype.card J:ℝ):= by
    intro p h; have ht := (Matrix.mem_orthogonalGroup_iff J ℝ).mp h; rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow, Real.sq_sqrt]; swap
    · simp_rw [Real.rpow_two]; exact Finset.sum_nonneg fun i _=> Finset.sum_nonneg fun j _=> sq_nonneg _
    replace ht:= congr_arg Matrix.trace ht; rw [Matrix.trace_one] at ht
    refine Eq.trans ?_ ht; rw [Matrix.trace]; simp [Matrix.diag_apply,Matrix.mul_apply, sq]
  apply isCompact_iff_compactSpace.mp; let K:= Metric.closedBall (0:Matrix J J ℝ) √(Fintype.card J:ℝ); apply (show IsCompact K from isCompact_closedBall ..).of_isClosed_subset isClosed_unitary; intro p hp
  rw [show K=Metric.closedBall _ _ from rfl,Metric.mem_closedBall,dist_zero_right, ← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), hv p hp, Real.sq_sqrt (Nat.cast_nonneg _)]

namespace OJoint

instance countable' : SecondCountableTopology (OJoint J):= by
  haveI : SecondCountableTopology (Matrix J J ℝ):= inferInstanceAs (SecondCountableTopology (J→J→ℝ))
  exact inferInstanceAs (SecondCountableTopology ↥((OJoint J:Set (Matrix J J ℝ))))
instance measures : MeasurableSpace (OJoint J):= borel _
instance : BorelSpace (OJoint J):= ⟨rfl⟩

def allElements (J:Type*) [Fintype J][DecidableEq J]: TopologicalSpace.PositiveCompacts (OJoint J):=⟨⟨univ,isCompact_univ⟩,by simp⟩
def prob (J:Type*) [Fintype J][DecidableEq J]: Measure (OJoint J):= Measure.haarMeasure (allElements J)
instance : (prob J).IsHaarMeasure := by unfold prob; infer_instance
instance : IsProbabilityMeasure (prob J) where
  measure_univ := @Measure.haarMeasure_self (OJoint J) _ _ _ _ _ (allElements J)
instance : (prob J).IsMulRightInvariant:= ⟨fun t=> Eq.symm ((Measure.haarMeasure_eq_iff (allElements J) _).2 (by
  change (Measure.map _ (prob J)) univ=1; rw [Measure.map_apply (measurable_mul_const t) MeasurableSet.univ]; simp))⟩
lemma portion (A:OJoint J):A.val.transpose*A.val=1:= (Matrix.mem_orthogonalGroup_iff' J ℝ).mp A.property

abbrev Spin (A:OJoint J):Module.End ℝ (VectorA J):= Matrix.toEuclideanLin A.val
lemma spin_act (A:OJoint J)(v:VectorA J)(i:J): Spin A v i=∑ k,A.val i k*v k:= rfl
lemma spin_inner (A:OJoint J)(v w:VectorA J): inner ℝ (Spin A v) (Spin A w)=inner ℝ v w:= by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change (A.val *ᵥ w.ofLp) ⬝ᵥ (A.val *ᵥ v.ofLp) = w.ofLp ⬝ᵥ v.ofLp; rw [← Matrix.dotProduct_transpose_mulVec A.val v.ofLp, Matrix.mulVec_mulVec, portion, Matrix.one_mulVec]; exact dotProduct_comm ..
lemma spin_norm (A:OJoint J)(v: VectorA J): ‖Spin A v‖=‖v‖:= by rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq, spin_inner]
lemma spin_mul (A B:OJoint J)(v: VectorA J): Spin (A*B) v=Spin A (Spin B v):= WithLp.ofLp_injective _ ((Matrix.mulVec_mulVec v.ofLp A.val B.val).symm)
lemma spin_one (v:VectorA J):Spin (1:OJoint J) v=v:= WithLp.ofLp_injective _ (Matrix.one_mulVec _)
lemma available (A: VectorA J ≃ₗᵢ[ℝ] VectorA J): ∃ B:OJoint J, Spin B=A.toLinearEquiv.toLinearMap:= by
  let C:=EuclideanSpace.basisFun J ℝ
  let F:= Matrix.of fun i j : J => A (C j) i
  have hf : F.transpose*F=1:= by
    ext i j; rw [Matrix.one_apply]; simp only [Matrix.mul_apply,Matrix.transpose_apply,F,Matrix.of_apply]; rw [show ∑ x,(A (C i) x)*(A (C j) x)= _ from (show _=inner ℝ (A (C i)) (A (C j)) from ?_), A.inner_map_map]
    · by_cases h:i=j
      · subst i; simp [C]
      rw [(C.orthonormal.2 h),if_neg h]
    rw [real_inner_comm]; rfl
  let B: OJoint J:=⟨F,(Matrix.mem_orthogonalGroup_iff' J ℝ).mpr hf⟩
  refine ⟨B,C.toBasis.ext fun i=>?_⟩; ext j; rw [spin_act]; change (∑ k,F j k*C i k)= _; simp [C, mul_ite,PiLp.single_apply]; simp [F,C]
lemma reflective (u v:VectorA J)(hu:inner ℝ u u=inner ℝ v v): ∃ B:OJoint J,Spin B u=v ∧ ∀ z, inner ℝ u z=inner ℝ v z→Spin B z=z:= by
  let K:= (Submodule.span ℝ {u-v})ᗮ
  let L:= K.reflection
  obtain ⟨B,h⟩:=available L
  have he (z:VectorA J):Spin B z=L z:= LinearMap.congr_fun h z
  have ht z (hp:inner ℝ u z=inner ℝ v z): Spin B z=z := (he z).trans (Submodule.reflection_mem_subspace_eq_self (K:=K) (by unfold K; rw [Submodule.mem_orthogonal_singleton_iff_inner_right]; exact inner_sub_left ..|>.trans (sub_eq_zero.mpr hp))) -- rw K
  have hp:Spin B (u+v)=u+v:= ht _ (by simp only [inner_add_right,hu]; rw [real_inner_comm v u,add_comm])
  have hh: Spin B (u-v)= -(u-v):= (he _).trans (Submodule.reflection_orthogonalComplement_singleton_eq_neg ..)
  refine ⟨B,?_,ht⟩
  rw [map_add] at hp; rw [map_sub] at hh
  apply smul_right_injective (VectorA J) (show (2:ℝ)≠0 by norm_num); change (2:ℝ) • _=(2:ℝ) • v; rw [two_smul,two_smul]; calc
   _= Spin B u+Spin B v+(Spin B u-Spin B v) := by abel
   _=_ := by rw [hp,hh]; abel
lemma reconciles (x y:D→ VectorA J)(hp:∀ i j, inner ℝ (x i) (x j)=inner ℝ (y i) (y j)):
    ∃ B:OJoint J,∀ i, Spin B (x i)=y i:= by
  have he (S:Finset D): ∃ B:OJoint J,∀ i∈S, Spin B (x i)=y i:= by
    induction S using Finset.induction_on with
    | empty=> exact ⟨1, by simp⟩
    | @insert a s h ih=>
      obtain ⟨A,H⟩:=ih; obtain ⟨B,hB,hB'⟩:= reflective (Spin A (x a)) (y a) ((spin_inner ..).trans (hp a a)); refine ⟨B*A, fun i hi=>?_⟩
      rw [spin_mul]; rcases Finset.mem_insert.mp hi with rfl|he; · exact hB
      rw [H _ he,hB']; rw [← H i he,spin_inner, H i he]; exact hp a i
  obtain ⟨B,hB⟩:=he Finset.univ; exact ⟨B,fun i=> hB i (Finset.mem_univ _)⟩
end OJoint

def typed (x:VectorA (D×J))(i:D): VectorA J:= WithLp.toLp 2 fun j=> x (i,j)

def swept (s:OJoint J)(x:VectorA (D×J)): VectorA (D×J):= WithLp.toLp 2 fun i=> OJoint.Spin s (typed x i.1) i.2
lemma fan (x:VectorA (D×J))(s:OJoint J)(i:D): typed (swept s x) i=OJoint.Spin s (typed x i):=by ext;rfl
lemma rotor_mul (x: VectorA (D×J))(s t:OJoint J): swept (s*t) x=swept s (swept t x):=by apply PiLp.ext; intro i; unfold swept; simp only [WithLp.ofLp_toLp]; rw [OJoint.spin_mul]; exact congr_arg (fun p: VectorA J=> OJoint.Spin s p i.2) (fan x t i.1).symm

def changeRow (A : Matrix J J ℝ) (i : D× J) := ∑ j:J,Finsupp.single (i.1,j) (↑(A i.2 j):ℂ)
def changing (s:OJoint J) : Channel D J →ₐ[ℂ] Channel D J:= Normal.exchange (changeRow s.val)
lemma changing_value (s:OJoint J)(p:Channel D J)(x:VectorA (D×J)): watches (changing s p) x=watches p (swept s x):= by
  apply DFunLike.congr_fun (f:=(aeval _).comp (changing s)); ext1 i; simp only [AlgHom.comp_apply,aeval_X,changing,Normal.exchange_x, changeRow,Normal.glyph,map_sum,Finsupp.linearCombination_single,map_smul,swept,WithLp.ofLp_toLp, OJoint.spin_act,Complex.ofReal_sum,Complex.ofReal_mul,smul_eq_mul];rfl

section
variable {p:Channel D J}
private lemma tune_before (s:OJoint J)(a:D→ℝ)(i:J):Normal.reads (changeRow s.val) (electron a i)= (∑ j:J, (↑(s.val j i):ℂ) • electron a j):= by
  ext1 j; simp only [Normal.reads,changeRow,map_sum,Finsupp.linearCombination_single,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,electron]; simp [mul_ite]
private lemma summedSlit (f:J→ D×J→ℂ)(t :J→ℂ)(p:Channel D J) (S:Finset J): slit (∑ i∈S,t i • f i) p=∑ i∈S,t i • slit (f i) p:= by induction S using Finset.induction_on with | empty=> simp [slit_zero]| @insert i S h ih=> rw [Finset.sum_insert h,Finset.sum_insert h,slit_linear,slit_smul,ih]
lemma ionic_tints (s:OJoint J)(p:Channel D J)(a b:D→ℝ): ionic a b (changing s p)=changing s (ionic a b p):= by
  simp_rw [ionic_val,nex, changing,exchange_slit, tune_before, summedSlit, map_sum]
  -- move sum
  let R(u v:J):= slit (electron b v) (slit (electron a u) p)
  let f (i j:J):ℂ:= ↑(s.val j i); let X:= changing (D:=D) s -- fix namespace
  simp only [(slit _).map_smul,map_smul,Finset.smul_sum,map_sum]; simp_rw [smul_smul]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm];
  change ∑ w:J,∑ j:J, (f j i * f j w) • X (R w i) = _
  simp_rw [← Finset.sum_smul]; rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _),show ∑ j,f j i*f j i=1 from ?_,one_smul]; try rfl
  · have he:= congr_fun (congr_fun ((Matrix.mem_orthogonalGroup_iff J ℝ).mp s.property) i) i
    simp only [one_apply_eq,Matrix.mul_apply, Matrix.transpose_apply] at he
    unfold f; rw [← Complex.ofReal_one,← he]; simp
  intro w _ hw
  have he:= congr_fun (congr_fun ((Matrix.mem_orthogonalGroup_iff J ℝ).mp s.property) i) w
  simp only [Matrix.one_apply_ne hw.symm, Matrix.mul_apply,Matrix.transpose_apply] at he
  simp only [f,← Complex.ofReal_mul, ← Complex.ofReal_sum,he,Complex.ofReal_zero,zero_smul]
lemma tuned (s:OJoint J)(p:Channel D J)(l): tune l (changing s p)=changing s (tune l p):= by induction l generalizing p with | nil=>rfl| cons a l ih=> obtain ⟨a,b⟩:=a; rw [tune_feed,tune_feed, ionic_tints,ih]
lemma shade (h:Hide p)(s:OJoint J): Hide (changing s p):=by
  intro l; rw [tuned, changing, reads_val, show Normal.reads _ 0=0 from _root_.funext fun i=>Finsupp.linearCombination_zero_apply ..]; exact h l
end
end YM.XSpace.Stab
