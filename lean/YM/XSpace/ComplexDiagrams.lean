import YM.XSpace.Jets
import YM.XSpace.Image
import YM.FiniteVolumeClosure.A0bOriginals.Parity
import YM.Next.RANK.GaussSubst

/-!
# Complexifying external coefficients. Wick notation bridge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter MeasureTheory Next.Rank Gauss Formal MvPolynomial
open scoped Topology InnerProductSpace BigOperators ContDiff Matrix

section algebra
variable {ι : Type*} [Fintype ι]
def extendP (ι : Type*) := MvPolynomial.map Complex.ofRealHom (σ:=ι)

def complexK (K : Matrix ι ι ℝ) (hk : K.IsSymm) : Normal.Symmetric ι :=
  ⟨fun i j=> ↑(K i j),fun i j=> congr_arg Complex.ofReal (hk.apply j i)⟩

lemma slit_map (K : Matrix ι ι ℝ) (hk : K.IsSymm) (i : ι) (p : P ι) :
    Normal.slit ((complexK K hk).cov i) (extendP ι p)= extendP ι (neighbor K i p) := by
  classical
  have hp (j) (p : P ι): neighbor K i (X j*p)= X j*neighbor K i p+C (K i j)*p:= by
    simp only [neighbor,LinearMap.sum_apply,LinearMap.smul_apply,Partial,Derivation.coeFn_coe,
      pderiv_mul,pderiv_X,Pi.single_apply,apply_ite,ite_mul,smul_add,one_mul,zero_mul,smul_zero,
      Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    simp only [mul_smul_comm,Finset.mul_sum]; rw [C_mul',add_comm] -- inspect
  induction p using MvPolynomial.induction_on with
  | C c=> simp [neighbor,extendP]
  | add p q h g=>simp only [map_add,h,g]
  | mul_X p j h=> rw [mul_comm p,_root_.map_mul, show extendP ι (X j)=X j from MvPolynomial.map_X .., Normal.slit_prod, h,hp]; simp [extendP,complexK]

theorem milk_heat (K : Matrix ι ι ℝ) (hk : K.IsSymm) (p : P ι) :
    Normal.milk (complexK K hk) (extendP ι p)=extendP ι (heat K hk p) := by
  induction p using MvPolynomial.induction_on with
  | C c=> simp [heat_const,extendP]
  | add p q h g=> simp only [map_add,h,g]
  | mul_X p i h=>
    rw [_root_.map_mul,show extendP ι (X i)=X i from MvPolynomial.map_X ..,mul_comm (extendP ι p),Normal.feeds,h,heat_mul_X, slit_map]; simp [extendP,mul_comm]

lemma blend_real (K : Matrix ι ι ℝ) (hk : K.IsSymm) (p : P ι) : Normal.blend (complexK K hk) 0 (extendP ι p) = ↑(wick K hk p) := by
  have he (p : P ι) : aeval (0:ι → ℂ) (extendP ι p)= (↑(aeval (0:ι→ℝ) p):ℂ) := by
    induction p using MvPolynomial.induction_on with
    | C c=> simp [extendP]
    | add p q h g=> simp only [map_add,h,g,Complex.ofReal_add]
    | mul_X p i h=> simp [extendP]
  rw [Normal.blend_components,milk_heat, he]; rfl
end algebra

namespace Regulator.Tree
variable {R : Regulator} (T : R.Tree) (G : Gauge)
abbrev PolyC := Normal.poly (T.Idx G)
abbrev SeriesC := PowerSeries (T.PolyC G)

def extendD (p : T.Bare G) : T.SeriesC G := PowerSeries.map (extendP _) p

def formalLaw := Normal.blend (complexK (T.covariance G) (T.covariance_symm G)) 0

def sumC (p : T.SeriesC G) : PowerSeries ℂ := PowerSeries.mk fun k=> T.formalLaw G (PowerSeries.coeff k p)

def readPT (p : T.SeriesC G) := T.sumC G (p * T.extendD G (T.weight G)) * (PowerSeries.map Complex.ofRealHom (T.vacuum G))⁻¹

lemma sumC_real (p : T.Bare G) : T.sumC G (T.extendD G p)=PowerSeries.map Complex.ofRealHom (T.terms G p) := by
  ext1 k; simp only [sumC,terms,PowerSeries.coeff_map,extendD,PowerSeries.coeff_mk]; exact blend_real ..

lemma sumC_zero (p : T.SeriesC G) : PowerSeries.constantCoeff (T.sumC G p) = T.formalLaw G (PowerSeries.constantCoeff p) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,sumC,PowerSeries.coeff_mk,PowerSeries.coeff_zero_eq_constantCoeff_apply]

lemma extendD_zero (p : T.Bare G) : PowerSeries.constantCoeff (T.extendD G p)=extendP _ (PowerSeries.constantCoeff p) := by simp only [extendD,← PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_map]

lemma extend_vac : PowerSeries.constantCoeff (PowerSeries.map Complex.ofRealHom (T.vacuum G)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,PowerSeries.coeff_zero_eq_constantCoeff_apply,vacuum_zero,map_one]

lemma readPT_real (p : T.Bare G) : T.readPT G (T.extendD G p)=PowerSeries.map Complex.ofRealHom (T.diagrams G p) := by
  rw [readPT, diagrams,show T.extendD G p*T.extendD G (T.weight G)=T.extendD G (p*T.weight G) from (map_mul ..).symm,sumC_real,map_mul]
  congr 1
  symm
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by rw [T.extend_vac]; exact one_ne_zero)).mpr
  rw [← map_mul,PowerSeries.inv_mul_cancel _ (by simp),map_one]

lemma readPT_C_add (p q : T.SeriesC G) : T.readPT G (p+q)=T.readPT G p+T.readPT G q := by
  have he (p q : T.SeriesC G) : T.sumC G (p+q)=T.sumC G p+T.sumC G q := by ext1 k; simp [sumC]
  unfold readPT; rw [add_mul,he,add_mul]

lemma readPT_C_smul (p : T.SeriesC G) (c : ℂ) : T.readPT G (PowerSeries.C (C c)*p)= PowerSeries.C c * T.readPT G p := by
  have he (q : T.SeriesC G) : T.sumC G (PowerSeries.C (C c)*q)=PowerSeries.C c * T.sumC G q := by
    ext1 k; unfold sumC; rw [PowerSeries.coeff_C_mul,PowerSeries.coeff_mk,PowerSeries.coeff_mk,PowerSeries.coeff_C_mul,C_mul',map_smul]; rfl
  unfold readPT; rw [mul_assoc (PowerSeries.C _),he,mul_assoc]

@[simp] lemma readPT_one : T.readPT G 1=1 := by simpa [extendD] using T.readPT_real G 1
lemma readPT_zero (p : T.SeriesC G) : PowerSeries.constantCoeff (T.readPT G p) = T.formalLaw G (PowerSeries.constantCoeff p) := by
  rw [readPT,map_mul,sumC_zero,map_mul,extendD_zero,weight_zero,map_one,mul_one,PowerSeries.constantCoeff_inv,extend_vac,inv_one,mul_one]

def Fcov := complexK (T.treeCov G) (by
  change (T.treeCov G)ᵀ=T.treeCov G; rw [treeCov,Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,T.covariance_symm G,Matrix.mul_assoc])

def pointKey (i : FKey G R.side) := ∑ j:T.Idx G, Finsupp.single j (↑(T.rows G i j):ℂ)

def evaluateF := Normal.exchange (T.pointKey G)

lemma substitute (p : Normal.poly (FKey G R.side)) : T.formalLaw G (T.evaluateF G p) = Normal.blend (T.Fcov G) 0 p := by
  let K:= complexK (T.covariance G) (T.covariance_symm G)
  let P:= Normal.scope (T.pointKey G) K
  have hp : P=T.Fcov G := by
    apply Normal.Symmetric.ext; funext i j
    change Normal.treats K (T.pointKey G i) (T.pointKey G j)= (↑(T.treeCov G i j):ℂ)
    unfold pointKey Normal.treats treeCov
    simp only [map_sum, Finsupp.linearCombination_single,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Matrix.mul_apply,Complex.ofReal_sum,Complex.ofReal_mul,Matrix.transpose_apply,K,complexK]
    simp_rw [mul_comm (↑(T.rows G j _):ℂ)]
  unfold formalLaw evaluateF; rw [Normal.wets]; change Normal.blend P _ _=_; rw [hp]
  rw [show Normal.reads (T.pointKey G) 0=0 from _root_.funext fun i => Finsupp.linearCombination_zero_apply ..]

lemma substitute_apply (p : Normal.poly (FKey G R.side)) (A : T.Array G) : Formal.test (T.basisT G) A (T.evaluateF G p)=
    aeval (fun i => (↑(fields G R.side (T.periodic G A) i):ℂ)) p := by
  refine DFunLike.congr_fun (f:= (Formal.test (T.basisT G) A).comp (T.evaluateF G)) ?_ p
  ext1 i
  simp only [AlgHom.comp_apply,evaluateF,test,Normal.exchange_x, aeval_X, pointKey,map_sum, Normal.glyph,Finsupp.linearCombination_single,map_smul, smul_eq_mul]
  have he := congr_fun (T.rows_read G ((T.basisT G).equivFun A)) i
  rw [LinearEquiv.symm_apply_apply] at he
  rw [← he,Matrix.mulVec,dotProduct,Complex.ofReal_sum]
  simp
end Regulator.Tree
end YM.XSpace
