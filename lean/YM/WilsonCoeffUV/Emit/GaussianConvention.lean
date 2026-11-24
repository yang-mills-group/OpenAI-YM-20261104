import YM.WilsonCoeffUV.Thermo.Context
import YM.PertExtension.GaussianIBP
import Mathlib.Analysis.Matrix.Order

/-!
# Finite Wick vs. ordinary Gaussian (full precision convention)

Coefficientwise, before taking the thermodynamic limit. Use ordinary Euclidean
coordinates/(product) volume in applications. No quotient-mode constraints on
*conditional* fluctuations in the slice. ``Heat then plug noise only''. Test
on untouched coarse slots with arbitrary fixed B, NO covariance assigned to
those test variables.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Convention
open Matrix Function MeasureTheory Lattice FreeResolvent Metric RG Wilson Tree Precision
open PertExtension.GaussianScore PertExtension.Series PowerSeries Blue
open scoped BigOperators Topology MatrixOrder ContDiff
variable {U X Y: Type} [Fintype X] [Fintype Y]

section positive
variable {G:Gauge} {f n:Side}
/-- Tiny ordinary periods may also use the bulk finite Wick sampler
algebraically (many wraps). In fact the UNCHANGED quadratic on that
prescribed tree is strictly positive even there. Use `canonical_gap` with
`treeFare` for a size-independent bound at sufficiently large periods. -/
lemma tree_pos (A:Levels G)(i N : ℕ)(p:f.val=n.val*(loose A i).L.val) :
    let S:StepData n f:= ⟨loose A i,A.clock.kernel,p⟩
    (treeMatrix G S (repeatF S) (freeForms A N (i+1))).PosDef:= by
  intro S
  let F:= repeatF S
  let M:= freeForms A N (i+1)
  let H:= treeMatrix G S F M
  obtain ⟨a,ha,hV⟩:= vacuum_positive _ A.clock.kernel.penalty_pos (A.clock.adm (i+1))
  obtain ⟨ht,he⟩:= hV (Next.Free.location A N (i+1)) f
  have hM : (M.acts f).transpose=M.acts f := ht
  have hh : H.transpose=H:=by unfold H; rw [treeMatrix,transpose_submatrix,full_symmetric _ hM]
  have hz : Matrix.PosSemidef H:= by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨Matrix.isHermitian_iff_isSymm.mpr hh,fun x=>?_⟩
    let y:= profile F x
    have hx:= fiscal_gap S M (Bid.stretch F (0,y)) he
    rw [star_trivial]; refine le_trans ?_ (le_trans hx (tree_qf S F M y y).symm.le)
    apply add_nonneg
    · exact mul_nonneg ha.le (Finset.sum_nonneg fun _ _=>by positivity)
    exact mul_nonneg S.kernel.penalty_pos.le (Finset.sum_nonneg fun _ _=>by positivity)
  exact hz.posDef_iff_isUnit.mpr (H.isUnit_iff_isUnit_det.mpr ((cond_laws A i N).1 n f p))

lemma quadratic_cont (K:Matrix X X ℝ) : Continuous (fun x:Lawn X=> dotProduct x (K*ᵥx)) := by
  unfold Matrix.mulVec dotProduct; fun_prop

/-- Use native sup norms on the proof's coordinate space; independent of
inner product on Color. Positivity -> true Gaussian bill (no uniformity). -/
lemma native_coercive {K:Matrix X X ℝ}(h:K.PosDef) : ∃ c:ℝ,0<c ∧ ∀ x:Lawn X, c*‖x‖^2 ≤ dotProduct x (K*ᵥx)/2:=by
  classical
  let Q (x:Lawn X):=dotProduct x (K*ᵥx)/2
  let S:=sphere (0:Lawn X) 1
  have hx:∃ d>0,∀ x∈S,d≤Q x:=by
    by_cases hs:S.Nonempty
    · obtain ⟨x,hx,p⟩:= (isCompact_sphere (0:Lawn X) 1).exists_isMinOn hs ((quadratic_cont K).div_const _).continuousOn
      refine ⟨Q x, div_pos ?_ (by norm_num), p⟩
      simpa only [star_trivial] using h.dotProduct_mulVec_pos (x:=x) (by rintro rfl; simp at hx)
    exact ⟨1,one_pos,fun x hp=>(hs ⟨x,hp⟩).elim⟩
  obtain ⟨d,hp,hd⟩:=hx
  refine ⟨d,hp,fun x=>?_⟩
  by_cases hx:x=0
  · subst x; simp
  have he:= norm_pos_iff.mpr hx
  let y:= ‖x‖⁻¹ • x
  have hh:= hd y (show y∈S by simp [S,y,norm_smul,he.ne'])
  have hs:x=‖x‖ • y:=by unfold y; rw [smul_smul,mul_inv_cancel₀ he.ne',one_smul]
  rw (occs:=.pos [2,3]) [hs]
  calc
    d*‖x‖^2 ≤ Q y*‖x‖^2 := mul_le_mul_of_nonneg_right hh (sq_nonneg _)
    _= _:=by rw [mulVec_smul,smul_dotProduct,dotProduct_smul]; unfold Q; simp only [smul_eq_mul]; ring
end positive

variable {K H:Matrix X X ℝ}[DecidableEq X] (μ : Measure (Lawn X)) [μ.HasTemperateGrowth] (p:K.PosDef)

/-- No provider hypothesis. Inverse for ANY real positive definite precision.-/
def law : Law (Lawn X):=
  { P:=
     { toFun:= fun x=>
          { toFun:= fun y=>dotProduct x (K*ᵥ y)
            map_add':=fun x y=>by rw [Matrix.mulVec_add,dotProduct_add]
            map_smul':=fun c y=>by rw [mulVec_smul,dotProduct_smul]; rfl }
       map_add':=fun x y=> by ext v; exact add_dotProduct x y _
       map_smul':=fun r y=> by ext v; exact smul_dotProduct .. }
    turns:=fun x y=> by
      have ht:= Matrix.isHermitian_iff_isSymm.mp p.isHermitian
      change dotProduct x (K*ᵥy)=dotProduct y (K*ᵥx);
      conv_lhs=> arg 2;rw [←ht.eq]
      rw [dotProduct_transpose_mulVec]
    slope:= native_coercive p
    smooth:= quadratic_cont _ }

@[simp] lemma law_price (x y:Lawn X) : (law p).P x y=dotProduct x (K*ᵥy):= rfl

@[simp] lemma law_kernel (x:Lawn X): (law p).kern x=Real.exp (-dotProduct x (K*ᵥx)/2):= rfl

def tooth (i:X): Module.Dual ℝ (Lawn X):= LinearMap.proj i

lemma inverse_tooth (h:K*H=1)(i j:X): (law p).wick (tooth i) (tooth j)= H j i:= by
  classical
  let v k:= H k i
  have hx: (law p).P v=tooth i:= by
    apply LinearMap.ext; intro x
    have hu: K*ᵥ v=Pi.single i 1:=by
      funext k; change (K*H) k i= _; simp [h,Matrix.one_apply,Pi.single_apply]
    rw [law_price, show dotProduct v (K*ᵥx)=dotProduct x (K*ᵥv) from (law p).turns v x,hu,dotProduct_single,mul_one]; rfl
  unfold Law.wick; rw [← hx,Law.solves]; rfl

section evaluation

variable (B:Y→ℝ) (q:POL (X⊕Y))

omit [DecidableEq X] [Fintype X] [Fintype Y] in
def sectionPoly (x:Lawn X): ℝ := MvPolynomial.eval (Sum.elim x B) q

omit [DecidableEq X] [Fintype Y] [Fintype X] in
lemma section_cont : Continuous (sectionPoly B q) := by
  induction q using MvPolynomial.induction_on with
  | C c=> rw [show sectionPoly (X:=X) B (MvPolynomial.C c)=(fun _=>c) from funext fun _=> by simp [sectionPoly]]; exact continuous_const
  | add p q a b=> rw [show sectionPoly B (p+q)=sectionPoly B p+sectionPoly B q from funext fun _=>by simp [sectionPoly]]; exact a.add b
  | mul_X p i a=> rw [show sectionPoly B (p* MvPolynomial.X i)=sectionPoly B p*fun x=>Sum.elim x B i from funext fun _=> by simp [sectionPoly]]
                  cases i <;> first | exact a.mul continuous_const | exact a.mul (continuous_apply _)

omit [DecidableEq X] [Fintype Y] in
lemma section_bill : Zone.Invoice Radial.zone (sectionPoly B q):= by
  classical
  induction q using MvPolynomial.induction_on with
  | C c=> exact Zone.Invoice.bounded |c| (fun x=>by unfold sectionPoly; rw [MvPolynomial.eval_C,Real.norm_eq_abs])
  | add y z a b=> rw [show sectionPoly B (y+z)=sectionPoly B y+sectionPoly B z from funext fun _=> by simp [sectionPoly]]; exact a.add b
  | mul_X p i a=> rw [show sectionPoly B (p*MvPolynomial.X i)=sectionPoly B p*fun x=>Sum.elim x B i from funext fun _=> by simp [sectionPoly]]
                  cases i with
                  | inl i=> exact a.mul (Law.linearInvoice (tooth i))
                  | inr i=> exact a.mul (Zone.Invoice.const (B i))

omit [Fintype Y] in
lemma section_integrable : Integrable (sectionPoly B q * (law p).kern) μ:= (law p).integrable_entry _ (section_bill B q) (section_cont B q)

omit [Fintype Y] in
lemma avg_add (F:POL (X⊕Y)) : (law p).average μ (sectionPoly B (q+F)) = (law p).average μ (sectionPoly B q)+(law p).average μ (sectionPoly B F):= by
  unfold Law.average; rw [show sectionPoly B (q+F)=sectionPoly B q+sectionPoly B F from funext fun _=>by simp [sectionPoly],add_mul]; exact (congrArg (fun x:ℝ=>x/ _) (integral_add (section_integrable μ p B q) (section_integrable μ p B F))).trans (add_div ..)

omit [Fintype Y] [μ.HasTemperateGrowth] in
lemma avg_mul_X (i:Y): (law p).average μ (sectionPoly B (q* MvPolynomial.X (.inr i)))=(law p).average μ (sectionPoly B q)*B i:=by
  unfold Law.average
  rw [show (sectionPoly B (q*MvPolynomial.X (.inr i))) * (law p).kern =fun x=>(sectionPoly B q*(law p).kern) x * B i from funext fun _=>by simp [sectionPoly]; ring, MeasureTheory.integral_mul_const]; ring
end evaluation
section Wick_eval

variable (X Y) in
private def sprigPoly {n : ℕ}(F : Fin n→ X) (b : POL Y): POL (X⊕Y):=
  holdUpPoly X Y b * ∏ i, MvPolynomial.X (Sum.inl (F i))

omit [Fintype X] [Fintype Y] [DecidableEq X] in
private lemma sprout_exists (m : X ⊕ Y →₀ ℕ) (c : ℝ):
    ∃ (n:ℕ)(F:Fin n→X)(b:POL Y), (MvPolynomial.monomial m) c=sprigPoly X Y F b := by
  classical
  apply MvPolynomial.induction_on_monomial (motive:=fun p:POL (X⊕Y)=>∃ (n:ℕ)(F:Fin n→X)(b:POL Y),p=sprigPoly X Y F b)
  · intro a; exact ⟨0,Fin.elim0,MvPolynomial.C a,by simp [sprigPoly,holdUpPoly]⟩
  intro p i hp; obtain ⟨n,F,b,rfl⟩:= hp
  cases i with
  | inl i=> refine ⟨n+1, Fin.cons i F,b,?_⟩; unfold sprigPoly; rw [Fin.prod_univ_succ]; simp only [Fin.cons_zero,Fin.cons_succ]; ring
  | inr i=> refine ⟨n,F,b*MvPolynomial.X i,?_⟩; simp [sprigPoly,holdUpPoly,mul_right_comm]

variable {J:Type*}(B:Y → ℝ)

omit [μ.HasTemperateGrowth] [Fintype Y] in
lemma avg_aux (a:POL (X⊕Y))(b:POL Y) : (law p).average μ (sectionPoly B (a*holdUpPoly X Y b))=(law p).average μ (sectionPoly B a)* MvPolynomial.eval B b:= by
  have h (x:Lawn X) : sectionPoly B (a*holdUpPoly X Y b) x=sectionPoly B a x * MvPolynomial.eval B b := by simp only [sectionPoly,holdUpPoly,map_mul,MvPolynomial.eval_rename]; rfl
  have hp : sectionPoly B (a*holdUpPoly X Y b)*(law p).kern = fun x=> (sectionPoly B a * (law p).kern) x * MvPolynomial.eval B b:= by funext x; simp only [Pi.mul_apply,h,mul_right_comm]
  rw [Law.average,hp,integral_mul_const]; unfold Law.average; ring

omit [DecidableEq X] in
lemma W_eval_aux (a:POL (X⊕Y))(b:POL Y):
    MvPolynomial.eval B (PowerSeries.constantCoeff (Wick Y H (C (a*holdUpPoly X Y b))))=MvPolynomial.eval B (PowerSeries.constantCoeff (Wick Y H (C a))) * MvPolynomial.eval B b:=by
  rw [map_mul, show C (holdUpPoly X Y b)=holdUp X (C b) from ?_, W_param,map_mul,constantCoeff_C,map_mul]; exact (by rw [holdUp,map_C]; rfl)

omit [μ.HasTemperateGrowth] [Fintype Y] in
lemma avg_X_prod (F:J→X) (T:Finset J) : (law p).average μ (sectionPoly B (∏ i∈T,MvPolynomial.X (Sum.inl (F i)))) = (law p).average μ (Law.product (tooth ∘ F) T):= congrArg _ (funext (fun x=>by simp [sectionPoly,Law.product,tooth]))

variable [μ.IsAddRightInvariant] [NeZero μ]

omit [Fintype X] [Fintype Y] [DecidableEq X] in
private lemma dx_prod [DecidableEq J](f:J→ Ink (X⊕Y)) (S:Finset J)(i:X⊕Y):
    brush i (∏ j∈S,f j)= ∑ j∈S, brush i (f j) *∏ k∈ S.erase j,f k := by
  classical
  -- universes of J not used in differentiation
  induction S using Finset.induction_on with
  | empty=> simp
  | insert j T hj ih=>
    rw [Finset.prod_insert hj,Derivation.leibniz, Finset.sum_insert hj, Finset.erase_insert hj, ih]
    rw [smul_eq_mul,smul_eq_mul,mul_comm _ (brush i (f j)),add_comm,add_right_inj,Finset.mul_sum]; refine Finset.sum_congr rfl fun k hk=>?_
    have hg:= (ne_of_mem_of_not_mem hk hj).symm
    rw [Finset.erase_insert_of_ne hg,Finset.prod_insert (Finset.notMem_mono (Finset.erase_subset ..) hj)]; ring

lemma poly_X_reads (h:K*H=1)(g:H.transpose=H)(F:J→X)(T:Finset J):
    MvPolynomial.eval B (PowerSeries.constantCoeff (Wick Y H (∏ i∈T,path (Sum.inl (F i))))) = (law p).average μ (Law.product (tooth ∘ F) T):=by
  classical
  induction T using Finset.strongInductionOn
  case _ T ih=>
    by_cases he:T.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.mp he]; rw [show Law.product (tooth ∘ F) ∅= 1 from rfl, Law.empty]; simp [W_one]
    obtain ⟨j,hj⟩:= he; let S:=T.erase j; have hs:S⊂ T:= Finset.erase_ssubset hj
    have ht: T= insert j S:= (Finset.insert_erase hj).symm
    let a:= F j; let U: J→ Module.Dual ℝ (Lawn X):=tooth ∘ F
    have he: Law.product (tooth ∘ F) T = fun x=> Law.product U S x * (tooth a) x:= by
      funext x; rw [Law.product,ht,Finset.prod_insert]; exact mul_comm ..; exact Finset.notMem_erase _ _
    rw [he,(law p).recursion μ (tooth a) U]
    conv_lhs=> rw [ht]
    rw [Finset.prod_insert (show j∉S from Finset.notMem_erase _ _),mul_comm,W_var H g]
    have eval_sc c v : MvPolynomial.eval B (c • v)=(c:ℝ)* MvPolynomial.eval B v:=by rw [Algebra.smul_def,map_mul,MvPolynomial.algebraMap_eq,MvPolynomial.eval_C]
    simp_rw [dx_prod,brush_path,W_sum,map_sum, constantCoeff_smul, eval_sc]
    simp only [map_sum,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i ht
    rw [Finset.sum_eq_single (F i)]
    · simp only [↓reduceIte,one_mul,ih (S.erase i) (lt_of_le_of_lt (Finset.erase_subset ..) hs)]
      change H _ _ * _= _ * (law p).wick (tooth a) (tooth _); rw [inverse_tooth p h]; change H a (F i) * _= _ * H (F i) a
      rw [show H (F i) a= H a (F i) from congr_fun (congrArg (fun M:Matrix X X ℝ=>M a) g) (F i)]
      exact mul_comm _ _
    · intro b _ hb; rw [if_neg (by simpa [eq_comm] using hb)]; simp [Wick]
    simp

lemma W_C_reads (h:K*H=1)(g:H.transpose=H)(a:POL (X⊕Y)):
    MvPolynomial.eval B (PowerSeries.constantCoeff (Wick Y H (C a))) = (law p).average μ (sectionPoly B a):=by
  induction a using MvPolynomial.induction_on' with
  | monomial f c=>
    obtain ⟨n,F,b,Hb⟩:= sprout_exists f c
    rw [Hb,sprigPoly,mul_comm (holdUpPoly X Y b),avg_aux,W_eval_aux,avg_X_prod]
    congr 1; rw [map_prod]; exact poly_X_reads μ p B h g F Finset.univ
  | add u v a b=> rw [map_add,W_add,avg_add,map_add,map_add,a,b]

include p in
/-- Exact Wick integration identity. Same integral value for any nonzero
translation-invariant temperate μ on the finite space (can be pushed Color
volume etc). Numeric constants here do NOT purport to price remainder. -/
theorem gaussian_polynomial_coeff (h:K*H=1)(g:H.transpose=H)(f:Ink (X⊕Y))(i:ℕ):
    MvPolynomial.eval B (PowerSeries.coeff i (Wick Y H f)) =
      (∫ z:Lawn X, MvPolynomial.eval (Sum.elim z B) (PowerSeries.coeff i f) * Real.exp (-dotProduct z (K*ᵥz)/2) ∂μ) /
        (∫ z:Lawn X, Real.exp (-dotProduct z (K*ᵥz)/2) ∂μ):=by
  let a:=PowerSeries.coeff i f
  have he : PowerSeries.coeff i (Wick Y H f)= PowerSeries.constantCoeff (Wick Y H (C a)):=by
    simp only [Wick,projectZero,coeff_map,overlay_apply,←coeff_zero_eq_constantCoeff]
    simp [a]
  rw [he]; exact W_C_reads μ p B h g a
end Wick_eval
end YM.WilsonCoeffUV.Convention
namespace YM.WilsonCoeffUV.Convention
open Matrix Function MeasureTheory Lattice FreeResolvent Metric RG Wilson Tree Precision
open PertExtension.GaussianScore PertExtension.Series PowerSeries Blue
open scoped BigOperators Topology MatrixOrder ContDiff
variable {X Y:Type} [Fintype X][Fintype Y]
variable {K H:Matrix X X ℝ}[DecidableEq X]

omit [DecidableEq X] in
lemma glaze_inl (Y:Type)[Fintype Y](q:POL X) :
    glaze (fillSlots Y H) (MvPolynomial.rename Sum.inl q)=MvPolynomial.rename Sum.inl (glaze H q):= by
  induction q using MvPolynomial.induction_on with
  | C a=> simp only [MvPolynomial.rename_C,glaze_constant]
  | add p q a b=> simp_rw [map_add,a,b]
  | mul_X p i hp=>
    rw [map_mul,MvPolynomial.rename_X, glaze_pin,glaze_pin,map_add,hp,map_mul,MvPolynomial.rename_X]; congr 1
    rw [Fintype.sum_sum_type,map_sum]
    simp_rw [blend,fillSlots]; simp only [fromBlocks_apply₁₁,fromBlocks_apply₁₂,fromBlocks_apply₂₁, Matrix.zero_apply,zero_div,zero_smul,Finset.sum_const_zero,add_zero]
    refine Finset.sum_congr rfl fun j _=>?_
    rw [map_smul]; congr 1
    change glaze (fillSlots Y H) _=_
    rw [glaze_deriv,glaze_deriv,hp]
    exact MvPolynomial.pderiv_rename Sum.inl_injective _ _

/-- no-spectator version of gaussian_polynomial_coeff, in bare product volume. -/
theorem gaussian_centered (p:K.PosDef)(h:K*H=1)(e:H.transpose=H) (f:Ink X) (i:ℕ):
    coeff i (seedH (blur H f))=
      (∫ z:Lawn X, MvPolynomial.eval z ((PowerSeries.coeff i) f) * Real.exp (-dotProduct z (K*ᵥz)/2)) /
        (∫ z:Lawn X, Real.exp (-dotProduct z (K*ᵥz)/2)) := by
  let B : Unit→ℝ := 0
  let F:= PowerSeries.map (MvPolynomial.rename (R:=ℝ) (Sum.inl (β:=Unit))).toRingHom f
  have hv:= gaussian_polynomial_coeff volume p B h e F i
  have hp z: MvPolynomial.eval (Sum.elim z B) (coeff i F) = MvPolynomial.eval z (coeff i f):=by
    unfold F; rw [coeff_map]; exact MvPolynomial.eval_rename Sum.inl (Sum.elim z B) (coeff _ _)
  simp_rw [hp] at hv
  rw [←hv]
  rw [seedH,coeff_map,Wick,projectZero,coeff_map,overlay_apply,overlay_apply]; unfold F; rw [coeff_map]
  change MvPolynomial.eval _ (glaze _ _)= MvPolynomial.eval _ (projectZeroPoly X Unit (glaze _ (MvPolynomial.rename Sum.inl _)))
  rw [glaze_inl]; symm
  have hV (q:POL X): MvPolynomial.eval B ((projectZeroPoly X Unit) (MvPolynomial.rename Sum.inl q))=MvPolynomial.eval 0 q:=by
    induction q using MvPolynomial.induction_on with
    | C a=> simp [projectZeroPoly]
    | add p q a b=> simp only [map_add,a,b]
    | mul_X p i h=> rw [map_mul,map_mul,map_mul,h]; simp [projectZeroPoly]
  exact hV _
end YM.WilsonCoeffUV.Convention
