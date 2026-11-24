import YM.AllOrder.Fire.Stage
import YM.AllOrder.Ink.Snug
import YM.AllOrder.Ink.Origin
/-!
# Moving through the counted post K

$T D W - pole$, including zero mode, on full period plant. Variables P n
with no premature analytic continuation/wishes. Coherences assembled later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Kinetic
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method GaussianScore Module
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
variable {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y] [FiniteDimensional ℝ X][FiniteDimensional ℝ Y]
variable (e:rule α n≃L[ℝ]X)(v:rule β n≃L[ℝ]Y)
local notation "L"=> (α⊕β)
local notation "I"=> Leaf n L
local notation "E"=> X×Y
local notation "I'"=> Leaf n β
-- portraits
abbrev posture : rule (α⊕β) n ≃L[ℝ] X × Y:= (desks α β n).trans (e.prodCongr v)
def faces := (Pi.basisFun ℝ (Leaf n β)).map (v.toLinearEquiv)
abbrev childL (i:I') := Primitives.TwoWave.peg α i -- possible conflict Method.child not childL
lemma axial (i : I') : faces v i=v (spot i):= by simp [faces,Pi.basisFun_apply,spot]; ext1 x; simp [Pi.single_apply]
lemma song (i:I'): posture e v (spot (childL (α:=α) i)) = vec («X»:=X) (faces v) i:= by
 rw [posture,ContinuousLinearEquiv.trans_apply,desks_peg]; simp [axial,Fire.vec]
lemma suite (x:rule α n)(y:rule β n): posture e v (mingle x y)= (e x,v y):= rfl

variable (A:X × Y→ℝ)(ρ:X→Y) (h:Steered A ρ)
def village : Mat n (α⊕β) (α⊕β) 1:= extractF (iteratedFDeriv ℝ 2 (A ∘ posture e v) 0)
def mail := headMatrix (village e v A)
def pulse : Matrix (Leaf n β) (Leaf n β) ℝ := (mail e v A).submatrix (Primitives.TwoWave.peg _) (Primitives.TwoWave.peg _)
local notation "A₀"=> mail e v A
local notation "B"=> pulse e v A
local notation "J"=> posture e v
local notation "F"=> faces v
local notation "V'"=> fderiv ℝ (fderiv ℝ A) 0
variable [DecidableEq β] -- needed until pulse det; Eq affects Pi.basisFun?
set_option quotPrecheck false
local notation "U"=> castle A ρ h
include h
omit [DecidableEq β] in
lemma post (i j:I): A₀ i j= V' (posture e v (spot i)) (posture e v (spot j)) := by
 rw [mail,headMatrix_at,village]; let L':= (J).toContinuousLinearMap; unfold extractF; change iteratedFDeriv ℝ 2 (A∘ L') _ _=_; rw [Next.Foundations.jets_linear L' (h.hard.of_le le_top),ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_two_apply]; rfl
omit [DecidableEq β] in
lemma post_both (i j:I') : B i j= (U).P ((F) i) ((F) j):= by
 unfold pulse; rw [Matrix.submatrix_apply,post e v A ρ h,song e v i,song e v j]; rfl

lemma spring_inv : let P:=Matrix.of fun i:I'=>fun j:I'=> rowM (U) F j i; B * P=1:= by
 intro P; ext i j; let x:= Inv (U) F j
 change ∑ k:I', B i k * (F).coord k x= _; -- replace
 calc ∑ k:I', B i k * (F).coord k x = ∑ k:I', (U).P (F i) ((F).coord k x • F k) := Finset.sum_congr rfl fun k _=> by rw [post_both e v A ρ h,map_smul]; exact mul_comm ..
      _ = (U).P (F i) x:= by rw [← map_sum]; exact congr_arg _ ((F).sum_repr x)
      _ = (U).P x (F i):= (U).turns ..
      _ = (F).coord j (F i):= congr_arg (fun A : Y →ₗ[ℝ] ℝ => A (F i)) ((U).applies ((F).coord j))
      _ = _ := by classical simp [Matrix.one_apply, Finsupp.single_apply, Finsupp.single_eq_same]
lemma spring (i j:I') : (B)⁻¹ i j= rowM (U) F i j:= by rw [Matrix.inv_eq_right_inv (spring_inv e v A ρ h)]; exact invert_c (U) (faces v) j i

-- charge linear quiet lift
omit [DecidableEq β]
lemma steady (x:X)(y:Y): V' (x,fderiv ℝ ρ 0 x) (0,y)=0:= by
 let a := (x,fderiv ℝ ρ 0 x); let b:= ((0:X),y); let P:=V'
 have he:= h.gauge x y; unfold Laplace.curvature at he; simp_rw [jet_two_H] at he; rw [show (x,fderiv ℝ ρ 0 x+y)= a+b from (by unfold a b; simp) ] at he; simp only [map_add,_root_.add_apply] at he; have hb : V' b a= P a b:= h.hard.isSymmSndFDerivAt le_top |>.eq ..
 change P a b=0; change (2:ℝ)⁻¹ * _ = (2:ℝ)⁻¹ * (P a a)+ (2:ℝ)⁻¹* (P b b) at he; rw [hb] at he
 linarith only [show (2:ℝ)⁻¹ * ((P a a + P a b)+(P a b + P b b))=_ from he]
lemma jets_turn (x:rule L n)(i:Leaf n L): (A₀*ᵥ x) i= V' (J (spot i)) (J x):= by
  let P:= (V' ((J) (spot i))).comp (J).toContinuousLinearMap; conv_rhs => arg 2; rhs; rw [← Push.Uniform.combine x];
  -- changes x only
  simp_rw [map_sum,map_smul]; unfold Matrix.mulVec dotProduct; refine Finset.sum_congr rfl fun j _=>?_ ; change A₀ i j*x j=_; rw [post e v A ρ h,mul_comm]; rfl
lemma joints_turn (x:rule α n)(i : Leaf n β): let w:rule β n:= v.symm (fderiv ℝ ρ 0 (e x)); (B*ᵥ w) i= - Method.wagon x A₀ i:= by
 let x':=mingle x (0:rule β n); intro w; let Y':=mingle (0:rule α n) w; let i':= childL (α:=α) i; have ht(Y : rule β n) : (B *ᵥ Y) i=(A₀ *ᵥ mingle (0:rule α n) Y) i' := (Ink.Method.bulbs (mail e v A) Y i').symm
 change (B*ᵥ w) i= -(A₀*ᵥ x') i'; apply eq_neg_of_add_eq_zero_left; have hx : x'+Y'= mingle x w:= by ext1 j; rcases j with ⟨u,v|v⟩; exact add_zero ..; exact zero_add ..
 rw [ht,add_comm,← Pi.add_apply,← Matrix.mulVec_add,hx, jets_turn e v A ρ h, song,suite]; unfold w; rw [ContinuousLinearEquiv.apply_symm_apply]
 exact (h.hard.isSymmSndFDerivAt le_top|>.eq ..).trans (steady A ρ h ..)
end YM.AllOrder.Kinetic
