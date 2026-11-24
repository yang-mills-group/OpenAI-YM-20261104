import YM.RegulatorIR.Diagram.Ease

/-! Heat conjugation of a single elementary ambient field. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Diagram.Interval
open Function Budget Budget.Layer Formal Finset PowerSeries Polynomial
open scoped BigOperators Topology Classical Polynomial PowerSeries
variable {I:Type}

lemma commute_partials (F:Jet I)(i j:I): MvPolynomial.pderiv i (MvPolynomial.pderiv j F)=MvPolynomial.pderiv j (MvPolynomial.pderiv i F):=by
 by_cases he:i=j
 · subst j;rfl
 ext m
 simp_rw [MvPolynomial.coeff_pderiv,add_right_comm m (Finsupp.single i 1)]
 simp [he, Ne.symm he]; ring
lemma blade_cross (i j:I) (F:CurveT I): blade i (blade j F)=blade j (blade i F):= by
 ext1 p; unfold blade; simp_rw [remaining_v]; exact commute_partials ..
lemma split_time (i:I) (F:CurveT I): clock (Jet I) (blade i F)=blade i (clock (Jet I) F):=by
 ext1 p; unfold blade; simp_rw [clock_v,remaining_v,clock_v]; rw [show (p:Jet I)+1= MvPolynomial.C (p+1:ℝ) by simp]
 rw [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_C,mul_zero, add_zero]

def axis (i:I):CurveT I:= Polynomial.C (MvPolynomial.X i)
abbrev varT : CurveT I:= Polynomial.X
lemma blade_C (i:I)(x:Jet I): blade i (Polynomial.C x)=Polynomial.C (MvPolynomial.pderiv i x):=by ext1 n; unfold blade; simp_rw [remaining_v]; by_cases h:n=0 <;> simp [Polynomial.coeff_C,h]
@[simp] lemma blade_axis (i j:I) : blade i (axis j)=if i=j then 1 else 0:=by
 rw [axis,blade_C]; by_cases h:i=j
 · subst j; simp
 rw [MvPolynomial.pderiv_X_of_ne (Ne.symm h),map_zero,if_neg h]
@[simp] lemma blade_X (i:I): blade i varT=0:=by
 ext1 n; unfold blade; simp_rw [remaining_v]; simp [Polynomial.coeff_X,apply_ite]
lemma clock_axis (i:I): clock (Jet I) (axis i)=0:= Polynomial.derivative_C ..
lemma clock_tick : clock (Jet I) varT=1:= Polynomial.derivative_X

variable [Fintype I]
lemma thermal_const (K:Layer I I)(p:ℝ): Pursues K (Polynomial.C (MvPolynomial.C p)):=by
 unfold Pursues; rw [show clock (Jet I) (Polynomial.C _) =0 from Polynomial.derivative_C ..];simp [sweepN,blade_C]
lemma thermal_add {K:Layer I I}{p q:CurveT I}(h:Pursues K p)(hh:Pursues K q):Pursues K (p+q):=by
 unfold Pursues at *; rw [map_add,h,hh]; simp_rw [sweepN, map_add,smul_add,sum_add_distrib,smul_add]
lemma thermal_scale {K:Layer I I}{p:CurveT I}(h:Pursues K p)(c:ℝ):Pursues K (c • p):=by
 unfold Pursues at *;rw [Derivation.map_smul,h]; simp_rw [sweepN,Derivation.map_smul,smul_comm c (2:ℝ)⁻¹]; simp_rw [Finset.smul_sum,smul_comm c]
lemma thermal_sum {X:Type*}(s:Finset X)(K:Layer I I)(f:X→CurveT I)(h:∀ i∈s, Pursues K (f i)): Pursues K (∑ i∈s,f i) := by
 induction s using Finset.induction_on with
 | empty=> simp only [sum_empty]; unfold Pursues;simp [sweepN]
 | insert x s he ih=>rw [sum_insert he]; exact thermal_add (h x (mem_insert_self ..)) (ih fun i h' =>h i (mem_insert_of_mem h'))
lemma thermal_partial {K:Layer I I}{P:CurveT I}(h:Pursues K P)(i:I):Pursues K (blade i P):= by
 unfold Pursues at *; rw [split_time,h,Dmap]; unfold sweepN; simp_rw [map_sum,Derivation.map_smul,blade_cross i]
where Dmap (x:CurveT I): blade i ((2:ℝ)⁻¹ • x)= (2:ℝ)⁻¹ • blade i x:= Derivation.map_smul ..

def react (K:Layer I I)(i:I)(Q:CurveT I):CurveT I:= ∑ j:I,K i j • blade j Q

def augment (K:Layer I I)(i:I)(Q:CurveT I):= Q* axis i+ varT* react K i Q

lemma reaction (i:I)(Q:CurveT I){K:Layer I I}(hh:∀ i j,K i j=K j i):
 sweepN K (Q * axis i) = axis i* sweepN K Q + (2:ℝ) • react K i Q := by
 have H (j k:I): blade j (blade k (Q * axis i))= (if k=i then blade j Q else 0) + (if j=i then blade k Q else 0)+ axis i*blade j (blade k Q):= by
   rw [Derivation.leibniz];change blade j (Q* _+axis i*_) = _; rw [map_add,blade_axis]
   rw [Derivation.leibniz (blade j) (axis i),blade_axis]; simp only [smul_eq_mul]
   split_ifs <;> simp <;> ring
 simp_rw [sweepN,H,smul_add,sum_add_distrib]; unfold react; rw [two_smul]
 let W:= axis i; let f j k:= blade j (blade k Q)
 have he : (∑ j:I,∑ k:I,K j k • (W*f j k))= W * ∑ j:I,∑ k:I,K j k • f j k := by simp_rw [Finset.mul_sum,mul_smul_comm];
 have ha : (∑ j:I,∑ k:I,K j k • (if k=i then blade j Q else 0))=react K i Q:=by simp_rw [smul_ite,smul_zero,sum_ite_eq',mem_univ,ite_true, show ∀ j,K j i=K i j from fun j=>hh ..];rfl
 have hb : (∑ j:I,∑ k:I,K j k • (if j=i then blade k Q else 0))=react K i Q:= by rw [Finset.sum_comm];simp [react,smul_ite]
 rw [ha,hb,he]
 exact add_comm ..
lemma wind_beh (Q:CurveT I)(K:Layer I I): sweepN K (varT * Q)=varT*sweepN K Q:=by
 have H (i:I)(v:CurveT I): blade i (varT*v)=varT*blade i v:=by rw [Derivation.leibniz,blade_X,smul_zero,add_zero]; rfl
 simp_rw [sweepN,H, ← mul_smul_comm, Finset.mul_sum]
lemma sweepN_add (K:Layer I I)(P Q : CurveT I): sweepN K (P+Q)=sweepN K P+sweepN K Q:=by simp_rw [sweepN,map_add,smul_add, Finset.sum_add_distrib]
lemma reaction_chart (K:Layer I I)(i j:I)(Q:CurveT I): blade i (react K j Q) = react K j (blade i Q):= by unfold react; simp_rw [map_sum,Derivation.map_smul]; refine Finset.sum_congr rfl (fun v _=>by rw [blade_cross i v])
lemma push_chart (K:Layer I I)(i j:I)(Q:CurveT I): blade i (augment K j Q) = augment K j (blade i Q)+(if i=j then Q else 0):= by rw [augment,map_add,Derivation.leibniz,Derivation.leibniz,blade_axis,blade_X,reaction_chart,augment]; split <;> simp [smul_eq_mul] <;> ring
lemma thermal_augment {K:Layer I I}{P:CurveT I}(h:Pursues K P)(hh:∀ i j,K i j=K j i)(i:I):Pursues K (augment K i P):=by
 have ht:Pursues K (react K i P):= thermal_sum _ _ _ (fun j _=> thermal_scale (thermal_partial h j) _)
 unfold Pursues at *; rw [augment,map_add,sweepN_add,reaction _ _ hh, wind_beh, Derivation.leibniz,Derivation.leibniz,h,ht,clock_axis,clock_tick]
 simp only [smul_add,smul_eq_mul,mul_one,mul_zero]; rw [smul_smul,inv_mul_cancel₀ (by norm_num : (2:ℝ)≠0),one_smul, mul_smul_comm,mul_smul_comm]; ring
end YM.RegulatorIR.Diagram.Interval
