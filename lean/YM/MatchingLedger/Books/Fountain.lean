import YM.MatchingLedger.Books.Stencil
import YM.PertExtension.GaussianIBP

/-!
# Gaussian (Wick) integration at a tilted saddle

`pour` is an independent ingredient of our formal Wilson coefficients. Precision form,
compatible with counting basis (`shaft`) and with the actual Wick conventions on local integration
(GaussianScore from PertExtension); constant may be chosen by vacuum scalar, does not enter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Books
open Function Filter Set MeasureTheory
open Matrix MvPolynomial PertExtension.GaussianScore PertExtension.Series
open scoped Topology Classical BigOperators ContDiff
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

-- extensive quadratic, finite volume. Square precision POSITIVE for the formal prescriptions here.
-- Elements in sup space (`Law.slope` for integrability), canonical dot formulas (no weights) use
-- their actual coefficient inner product.
def shaft (T : Law (Field ι)) : Matrix ι ι ℝ := Matrix.of fun i j=> T.P (axis i) (axis j)

theorem applied (T : Law (Field ι)) (i : ι) (v : Field ι) : (T.P (axis i)) v=(shaft T *ᵥ v) i := by
  nth_rw 1 [← sum_basis v]
  rw [_root_.map_sum]; simp only [_root_.map_smul]; change ∑ j,v j * _= _; exact Finset.sum_congr rfl fun j _=>mul_comm ..

structure Fountain (A : Poly ι) where
  law : Law (Field ι)
  mean : Field ι
  leads (i : ι) (x : Field ι) : read (x+mean) (pderiv i A) = law.P (axis i) x

namespace Fountain
variable {A : Poly ι} (T : Fountain A)

abbrev rank : Matrix ι ι ℝ:= shaft T.law
def subsidy (i : ι) := -(T.rank *ᵥ T.mean) i
lemma basis_test (i : ι) : pderiv i A = C (T.subsidy i)+ ∑ j:ι, C (T.rank i j)*X j := by
  apply MvPolynomial.funext; intro x
  let D:= T.rank; let b:=T.mean; let y:=x-b; have hx:y+b=x:=sub_add_cancel x b
  rw [← read_apply]; conv_lhs => rw [← hx, T.leads, applied]
  have hr : (shaft T.law *ᵥ y) i=(D*ᵥx) i- (D*ᵥ b) i := congr_fun (D.mulVec_sub _ _) i
  rw [hr, ← read_apply,_root_.map_add,read_C,_root_.map_sum (read x)] -- order
  simp_rw [read_mul,read_C,read_X]; change (D*ᵥx) i- (D*ᵥ b) i=-(D*ᵥ b) i+(D*ᵥ x) i; ring

private def lift (p : Poly ι) (x : Field ι): ℝ:= read (x+T.mean) p
private lemma cont (p : Poly ι) : Continuous (T.lift p):=(smooth_read p).continuous.comp (continuous_id.add continuous_const)
private lemma funded (p : Poly ι) : Zone.Invoice (Radial.zone (E:=Field ι)) (T.lift p) := by
  induction p using MvPolynomial.induction_on with
  | C a=> unfold lift; simp_rw [read_C]; exact Zone.Invoice.const _
  | add p q hp hq=> unfold lift; simp only [_root_.map_add]; exact hp.add hq
  | mul_X p i hp=>
    let L:= (ContinuousLinearMap.proj i : Field ι →L[ℝ] ℝ).toLinearMap
    have ht := (Law.linearInvoice L).add (Zone.Invoice.const (T.mean i))
    unfold lift; simp only [read_mul,read_X]; exact hp.mul ht
private lemma drawing (p : Poly ι) : Integrable (T.lift p * T.law.kern) := T.law.integrable_entry volume (T.funded p) (T.cont p)

-- gaussian integration as in `PertExtension.GaussianScore.Law` (`average`, equivalent to
-- Wick operations there). Lebesgue measure convention, x+mean argument. 
def pour : Prediction ι where
  toFun p:= T.law.average volume (T.lift p)
  map_add' p q:= by
    have hm : T.lift (p+q)=T.lift p+T.lift q:= _root_.funext fun i=>map_add ..
    rw [hm]; unfold Law.average; rw [add_mul]; simp_rw [Pi.add_apply]; rw [integral_add (T.drawing _) (T.drawing _),add_div]
  map_smul' c p:= by
    unfold Law.average; simp only [Pi.mul_apply,lift,_root_.map_smul, smul_eq_mul]; simp_rw [mul_assoc]; rw [integral_const_mul,mul_div_assoc]; rfl

lemma pour_one : T.pour 1=1 := by
  have hm : T.lift 1 = 1:= _root_.funext fun i=>by rw [lift, read_apply, _root_.map_one]; rfl
  change T.law.average _ _ =_; rw [hm,T.law.empty]

lemma works (p : Poly ι)(i : ι) : T.pour (pderiv i A * p)=T.pour (pderiv i p) := by
  let T':= T.law; let m:=T.mean; let A' := fun x:Field ι=> read (x+m) p; let u:= axis i; let G := pderiv i p
  have hv : T.lift ((pderiv i A)*p)=(T.lift p)*(T'.P u):=by funext x; change read (x+m) _= A' x * (T'.P u x); rw [read_mul,T.leads]; exact mul_comm ..
  have hx : ∀ (x:Field ι)(t:ℝ), HasDerivAt (fun r : ℝ=> A' (x+r•u)) (T.lift G (x+t•u)) t:= by
    intro x t; change HasDerivAt (fun r=> read (x+r• u+m) p) (read (x+t•u+m) G) t; simp_rw [add_right_comm _ (_ • u) m]; exact read_has p (x+m) i t
  have he := T'.translation_lemma u (T.funded p) (T.cont p) (T.funded G) (T.cont G) hx volume
  change T.law.average _ (T.lift _) = T.law.average _ _; unfold Law.average; congr 1
  apply Eq.symm; apply sub_eq_zero.mp; rw [← integral_sub (T.drawing G) (T.drawing ((pderiv i A)*p)), hv]; exact (show _=0 from (by rw [sub_mul] at he; exact he))

end Fountain
end YM.MatchingLedger.Books
