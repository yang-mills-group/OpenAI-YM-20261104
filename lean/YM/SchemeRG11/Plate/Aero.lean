import YM.SchemeRG11.Plate.Ink
/-! Homogeneous power bookkeeping and first-order stencil Hessian Ward equation. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Pile
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular Full Atoll
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology
variable {G : Gauge}
variable (h:ℝ)(p : pLabel G)
def scaleStem(i:Key G) : Stem (Key G) ℝ:= h^(-(i.1+2:ℤ)) • Finsupp.single i 1
abbrev pad (i:Key G) := h⁻¹^(generation i)
def etude: pLabel G := vary (scaleStem h) p
lemma pad_eq (i:Key G): h^(-(i.1+2:ℤ))= pad h i:=by rw [pad,generation,zpow_neg, ← Nat.cast_ofNat (R:=ℤ) (n:=2), ← Nat.cast_add,zpow_natCast,inv_pow]
lemma uniformX (i:Key G): etude h (X i) = pad h i • X i:=by rw [etude,vary_X, leaf,scaleStem,map_smul,Finsupp.linearCombination_single,one_smul,pad_eq]
lemma programDeg {d:ℕ}(hp:IsWeightedHomogeneous Labels.generation p d): etude h p=h⁻¹^d • p:=by
 conv_lhs=> rw [← p.support_sum_monomial_coeff]
 rw [etude,_root_.map_sum]; conv_rhs=> rw [←p.support_sum_monomial_coeff]
 rw [Finset.smul_sum]
 apply Finset.sum_congr rfl; intro i hi
 rw [monomial_eq,map_mul, vary_C]; have He k: vary (scaleStem h) (X k)= pad (G:=G) h k • X k := uniformX ..
 simp_rw [Finsupp.prod,map_prod,map_pow,He,smul_pow,C_mul',MvPolynomial.smul_eq_C_mul,Finset.prod_mul_distrib,← map_prod]
 have hh:d=∑ j∈i.support,i j * generation j:=(hp (MvPolynomial.mem_support_iff.mp hi)).symm
 rw [hh,← Finset.prod_pow_eq_pow_sum]; unfold pad; simp_rw [← pow_mul, mul_comm (generation _) (i _)]; ring
lemma expand_s(c:ℝ): expandW h (c • p)=c • expandW h p:=by rw [MvPolynomial.smul_eq_C_mul,expand_mul,expand_C,vary_C,zero_mul,add_zero,MvPolynomial.smul_eq_C_mul]
lemma colour_thin(i j: Touch G)(c d:ℝ): (land G).bed (c • i) (d • j)=c*d*(land G).bed i j:=by
 rw [Dose.bed_comm,Dose.bed,map_smul]; change _ * (land G).bed _ _=_
 rw [Dose.bed_comm,Dose.bed,map_smul]; change _*(_*(land G).bed _ _)=_; ring
lemma sloped : ((Atoll.unmarked G 1).pull (scaleStem h))=Atoll.unmarked G h:=by
 apply Dose.strict; intro i j
 unfold Dose.pull Atoll.unmarked; change (Atoll.unmarked G 1).bed (scaleStem h i) (scaleStem h j) = (land G).bed _ _
 rw [scaleStem,Dose.bed_comm, Dose.bed,map_smul]; change h^(-(i.1+2:ℤ)) * (Atoll.unmarked G 1).bed (scaleStem h j) (Finsupp.single i 1)=_
 rw [Dose.bed_comm,scaleStem,Dose.bed,map_smul,sense,Finsupp.linearCombination_single,one_smul,Dose.single_wind]
 unfold Atoll.unmarked Dose.pull; simp only [Atoll.leafProbe,one_zpow,one_smul, colour_thin,smul_eq_mul];ring
lemma expand_sc (q:pLabel G): expandW 1 (etude h q)=expandW h q∧stemZero 1 (etude h q)=stemZero h q:=by
 induction q using MvPolynomial.induction_on with
 | C c=> rw [etude,vary_C,expand_C,expand_C,vary_C,vary_C]; exact ⟨rfl,rfl⟩
 | add a b ha hb=> rw [show etude h (a+b)=_ from (show _ = etude h a+etude h b from map_add ..)]; simp only [expand_add,map_add,ha,hb,and_self]
 | mul_X a i ih=>
   rw [show etude h (a*X i)= etude h a * etude h (X i) from map_mul ..,expand_mul,expand_mul, ih.1,ih.2,map_mul (stemZero 1),map_mul (stemZero h),ih.2]; simp only [uniformX,expand_s,expand_x,stemZero, bud,Atoll.leafProbe,vary_X,map_smul,one_zpow,one_smul,pad_eq,and_self] -- fix
lemma dominion {d:ℕ}(hp:IsWeightedHomogeneous Labels.generation p d) : castZero h p=h⁻¹^d • castZero 1 p∧castFirst h p=h⁻¹^d • castFirst 1 p:=by
 unfold castZero castFirst
 rw [← expand_sc h ((Atoll.unmarked G h).neg.heat p)|>.1, ← expand_sc h ((Atoll.unmarked G h).neg.heat p)|>.2]
 rw [show etude h ((Atoll.unmarked G h).neg.heat p)=(Atoll.unmarked G 1).neg.heat (etude h p) by rw [etude,etude,Dose.night,sloped]]
 rw [programDeg _ _ hp]; simp only [map_smul,expand_s,and_self]

variable (A : trunk G ℤ)(e: Cover→G.Color)
lemma within_leg (i: Key G): sense (cant (ascent e)) (Atoll.leafProbe h i)=0:=by rw [Atoll.leafProbe,map_smul,mute,smul_zero]
lemma lofts : vent (cant (ascent e)) (stemZero h p)=0:=by
 rw [varyVent]; have he:(fun i=> sense (cant (ascent e)) (Atoll.leafProbe h i))=0:= _root_.funext fun i=> within_leg h e i
 rw [he,vent_zero, map_zero]
lemma solitary(he:e 0=0)(i:Key G): aeval (cant A) (vent (cant (ascent e)) (expandW h (X i))) = -(1/2:ℝ)*aeval (cant A) (vent (cant (spur e A)) (stemZero h (X i))):=by
 rw [expand_x, bud, (vent _).map_smul,map_smul,brace _ _ _ A e he,vary_X,taste, aeval_C, leafProbe, map_smul]; simp only [smul_eq_mul, Algebra.algebraMap_self_apply]; ring
lemma shelling(he:e 0=0): aeval (cant A) (vent (cant (ascent e)) (expandW h p))= -(1/2:ℝ)*aeval (cant A) (vent (cant (spur e A)) (stemZero h p)):=by
 induction p using MvPolynomial.induction_on with
 | C c=> rw [expand_C,vary_C,vent_C,map_zero,map_zero,mul_zero]
 | add a b ha hb=> simp only [expand_add,map_add,mul_add,ha,hb]
 | mul_X p i hp=>
   rw [expand_mul,map_add,vent_l,vent_l,lofts,lofts]
   rw [mul_zero,mul_zero,add_zero,zero_add,map_add,map_mul,map_mul,hp,solitary _ _ _ he, map_mul (stemZero h),vent_l,map_add,map_mul,map_mul];ring
lemma sailing (he:e 0=0): vent (cant (ascent e)) (castZero h p)=0∧
 aeval (cant A) (vent (cant (ascent e)) (castFirst h p))= -(1/2:ℝ) * aeval (cant A) (vent (cant (spur e A)) (castZero h p)):=⟨lofts ..,shelling h _ _ e he⟩
end YM.SchemeRG11.Pile
