import YM.Comparison.RG02.Assembly.Radial
import YM.Comparison.RG02.Cumulants.Cloud

/-!
# Vertices as explicit kernel polynomials for Wick

U x & Z combined *affinely*; every coefficient can start with rank and grade distinct.
Full log Taylor jet (no direction permutations until charging symmetric tensors). Prescribe
vertices on the full space of fine keys -- **no desideratum on connected estimates assumed**.
The prescription is exactly Gaussian polynomial occupation & marked quotient, not cumulants
read off of the solution. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Assembly
open Function Finset Filter MeasureTheory MvPolynomial
open YM.Marker YM.Multi Order
open YM.PertExtension.Series
open YM.Comparison.RG02.Cumulants Cumulants.Cloud
open scoped Topology BigOperators Classical ContDiff

variable {V I : Type} [Fintype I] [DecidableEq I] [DecidableEq V] [Fintype V] {R : Census V}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (y : E) (L : (I→ℝ)→ₗ[ℝ] E)

abbrev translate (x : I→ℝ) : E := y+L x
private def withRoot : Option I→ E := fun i=> i.elim y fun j=> L (Pi.single j 1)
private def ind (z : I→ℝ) (i : Option I) : ℝ := i.elim 1 z
private def coordinate (i : Option I) : MvPolynomial I ℂ := i.elim 1 X
private lemma appended (x : I→ℝ) : translate y L x=∑ i,ind x i • withRoot y L i := by
  rw [Fintype.sum_option]; simp_rw [ind,withRoot]; simp only [Option.elim_none, one_smul, Option.elim_some]
  have hu : (∑ i, x i • Pi.single i 1)=x := by
    ext i; rw [Finset.sum_apply]; simp [Pi.single_apply]
  unfold translate; simp_rw [← map_smul L]; rw [← map_sum,hu]

variable (l : Hot R→ℕ) (F : Hot R→ E→ℂ) (f : E→ℝ) (x : I→ℝ)
omit [DecidableEq I] [Fintype I] in
private lemma paint_coordinate (i : Option I) : paint x (coordinate i)= Complex.ofReal (ind x i) := by cases i <;> simp [paint,coordinate,ind]

def wordL {n : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin n=>E) ℂ) :=
    ∑ i:Fin n→Option I,MvPolynomial.C (T (withRoot y L ∘ i)) * ∏ k, coordinate (i k)
lemma reading_word {n : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin n=>E) ℂ) :
    paint x (wordL y L T)= T (fun _=>translate y L x) := by
  simp_rw [wordL, _root_.map_sum, _root_.map_mul, _root_.map_prod, show ∀ z : ℂ, paint x (C z) = z from fun z=> aeval_C .., paint_coordinate, appended y L x]
  rw [T.map_sum_finset (fun _ i=>_) (fun _=> Finset.univ), Fintype.piFinset_univ]
  apply Finset.sum_congr rfl; intro i _
  rw [T.map_smul_univ, Complex.real_smul, Complex.ofReal_prod,mul_comm]
  rfl

def kernelJet (g : E→ℂ) (i : ℕ) : MvPolynomial I ℂ :=
    wordL y L ((i.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ i g 0)
lemma reading (g : E→ℂ) (i : ℕ) : paint x (kernelJet y L g i)=jet g i (translate y L x) :=
    reading_word y L x _

/-- Polarized vacuum vertex. Subtracted order 2 goes into quadratic and common normalization.
    Signs/amplitudes from the negative exponent; here use `f` as positive-cost convention. -/
def naked (j : ℕ) : MvPolynomial I ℂ := if j=0 then 0 else
    -wordL y L (Complex.ofRealCLM.compContinuousMultilinearMap (((↑(j+2).factorial:ℝ))⁻¹ • iteratedFDeriv ℝ (j+2) f 0))
lemma readingVacuum (j : ℕ) : paint x (naked y L f j) = Complex.ofReal (vacuumLetter f (translate y L x) j) := by
  unfold naked vacuumLetter; split_ifs
  · simp
  rw [_root_.map_neg, reading_word, Complex.ofReal_neg]; rfl

def generator (r : ℕ) (s : Hot (Board R r)) : MvPolynomial I ℂ :=
    let n : ℕ := (Join.right s.val).val.card
    let i : R.Mode := Join.left s.val
    (n.factorial:ℂ) • if h : i.val.Nonempty then
         kernelJet y L (F ⟨i,h⟩) (l ⟨i,h⟩+n)
     else naked y L f n

def prescription (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (r : ℕ) : Grade R r :=
    Cloud.prescription Q hQ 0 (generator y L l F f r)

private lemma driver_bud (r : ℕ) (i : Hot (Board R r)) :
    (series R r (affine l F f (translate y L x))).part i.val=paint x (generator y L l F f r i) := by
  let n:=(Join.right i.val).val.card
  let t:= Join.left i.val
  unfold generator
  nth_rw 1 [← Join.pair_reunite i.val]
  rw [polarization, map_smul, affine,_root_.map_add,Poly.part_plus,realCoeff,beads]
  split_ifs with he ht ht
  · exact False.elim (((hot_iff_ne _).1 ht) he)
  · rw [he,mark_curve_quiet, add_zero, readingVacuum]; rfl
  · rw [curve,PowerSeries.coeff_mk, zero_add, reading];
    have h := part_lit (fun i=> markLetter l F i (translate y L x) n) (⟨t,ht⟩:Hot R)
    exact congrArg ( (n.factorial:ℂ)*·) h
  exact False.elim (ht ((hot_iff_ne t).2 he))
lemma colors (r : ℕ) : lit (Board R r) (fun i=> paint x (generator y L l F f r i)) =
    series R r (affine l F f (translate y L x)) := by
  simp_rw [← driver_bud]; exact lit_identity _ (driver_quiet ..)

section Gaussian
variable (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (hv : Q.PosDef) -- maybe PSD for proof
local notation "Y" => (I→ℝ)
open YM.Next.SectorChange
open MeasureTheory
include hv
variable [FiniteDimensional ℝ E]
/-- The core coefficient identity used under the true chart integral. Includes
 absolute convergence at this step (L¹ in the fixed tangent-field full Gaussian computation).
 Doesn't require analytic remainder claims. -/
lemma contracted (r : ℕ) (s : (Board R r).Mode) :
    let g := fun z : I→ℝ=> (series R r (expansions l F f (translate y L z))).part s
    Integrable g (Gaussian.cloud Q) ∧ (prescription y L l F f Q hQ r).part s = ∫ z, g z ∂Gaussian.cloud Q := by
   intro g; have hx:= Cloud.gaussian Q hQ hv.posSemidef 0 (generator y L l F f r) s
   simp_rw [Cloud.shift_zero,zero_add, colors, ← exponent_identity] at hx
   exact ⟨hx.1,hx.2.symm⟩
end Gaussian
end YM.Comparison.RG02.Assembly
