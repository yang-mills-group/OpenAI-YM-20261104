import YM.PertExtension.GaussianIBP
import YM.PertExtension.BareSlot
import YM.PertExtension.OrbHessian

/-! Matrix-free and matrix covariance of the Wilson Hessian with the half-volume
counting, no quotient assumption beyond even period. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.PertExtension.Orb
open Wilson Lattice Gauge Precision Function Filter Set Metric MeasureTheory Module Matrix
open scoped ContDiff Topology Classical BigOperators ENNReal
open Chart Series Series.Radial GaussianScore
variable {G : Gauge}{n : Side}

abbrev FaceReading (n : Side) := Face (Per n)
abbrev Source (G : Gauge)(n : Side):= Module.Dual ℝ (Dir G n)
/-- Linear curl on the non-tree fluctuation data. -/
def letterPolar (p : FaceReading n) : Dir G n →ₗ[ℝ] G.Color where
  toFun x:=letter x p
  map_add' x y := by simp_rw [letter,Curl,map_add,Pi.add_apply]; abel
  map_smul' c x := by simp only [letter,Curl,map_smul,Pi.smul_apply, smul_add,smul_sub, RingHom.id_apply]

def score (x y : Dir G n) : ℝ := (∑ p : FaceReading n, Inner.inner ℝ (letterPolar (G:=G) p x) (letterPolar p y))/2
@[fun_prop] lemma letter_continuous (p : Face (Per n)) : Continuous (fun x : Dir G n=>letter x p) := (letterPolar p).continuous_of_finiteDimensional
@[fun_prop] lemma score_self_cont : Continuous (fun x : Dir G n=>score x x) := (continuous_finsetSum _ (fun p _=>(letter_continuous p).inner (letter_continuous p))).div_const _

def scoreDual : Dir G n →ₗ[ℝ] Source G n where
 toFun x := {
   toFun:=score x
   map_add' u v := by simp_rw [score,map_add,inner_add_right,Finset.sum_add_distrib,add_div]
   map_smul' c u := by simp_rw [score,map_smul,inner_smul_right,← Finset.mul_sum,mul_div_assoc];rfl }
 map_add' u v:=by apply LinearMap.ext; intro x; change score (u+v) x=score u x+score v x; simp [score,map_add,inner_add_left,Finset.sum_add_distrib,add_div] -- adjust
 map_smul' c u:=by apply LinearMap.ext; intro x;change score (c • u) x=c*score u x; unfold score;simp_rw [map_smul,real_inner_smul_left,←Finset.mul_sum,mul_div_assoc]

lemma second_jet (u : Dir G n): score u u=2 * jet (fiscal (G:=G)) 2 u := by
  rw [homogeneous_derivative _ _ _ (fiscal_smooth.of_le le_top).contDiffAt,(fiscal_grades u).1]; norm_num [score,Q,Nat.factorial, real_inner_self_eq_norm_sq,letterPolar];ring

def saddle (even : Even n.val) : Law (Dir G n) where
  P:=scoreDual
  turns x y:= by
      unfold scoreDual;change score x y=score y x
      unfold score; exact congr_arg (fun z:ℝ=>z/2) (Finset.sum_congr rfl fun _ _=>_root_.real_inner_comm ..)
  slope := by change ∃ c : ℝ, c > 0 ∧ ∀ x : Dir G n,_ ≤ score x x/2; simp only [second_jet];convert (coercion even (G:=G)) using 5 <;> ring
  smooth := score_self_cont
-- note recursive imports coercion is from OrbExpansion through BareSlot.
lemma saddleLaw (even : Even n.val) : kernel (fiscal (G:=G))=(saddle even (G:=G)).kern := by ext x; unfold kernel saddle; change _=Real.exp (-(score x x)/2);rw [second_jet];congr 1;ring

variable {J : Type*}[Fintype J] [DecidableEq J](b : Module.Basis J ℝ (Dir G n))
def covariance (even : Even n.val) : Matrix J J ℝ := Matrix.of fun i j => (saddle even).wick (b.coord j) (b.coord i)
def coefficientMatrix: Matrix J J ℝ:= Matrix.of fun i j=>score (b i) (b j)

private lemma matrix_inverse (even : Even n.val) : coefficientMatrix b * covariance b even=1:= by
  ext i j
  let x := (saddle even).inverse (b.coord j)
  change (∑ k, score (b i) (b k) * b.coord k x) = _
  calc
    _ = ∑ k, scoreDual (b i) (b.coord k x • b k):= Finset.sum_congr rfl fun k _=> by rw [map_smul];change _=b.coord k x*score (b i) (b k);ring
    _ = scoreDual (b i) (∑ k, b.coord k x • b k) := by rw [map_sum]
    _ = score (b i) x := by rw [show (∑ k, b.coord k x • b k)=x from b.sum_repr x];rfl
    _ = scoreDual x (b i) := (saddle even).turns ..
    _ = b.coord j (b i) := congr_arg (fun l : Source G n=>l (b i)) (saddle even |>.applies (b.coord j)) -- coercion
    _ = _ := by classical simp [Matrix.one_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne, Finsupp.single_apply]

lemma covariance_eq (even : Even n.val) : covariance b even=(coefficientMatrix b)⁻¹:= by exact (Matrix.inv_eq_right_inv (matrix_inverse b even)).symm

def gaussian (even : Even n.val)(f : Dir G n→ℝ) := (saddle even).average (tangent G (Cotree n)) f

theorem gaussian_recursion (even : Even n.val) (ℓ : J → Source G n) (s : Finset J){j₀ : J}(h : j₀∈s) :
  gaussian even (fun x=> ∏ i∈s,ℓ i x) = ∑ i∈s.erase j₀, gaussian even (fun x=>∏ r∈(s.erase j₀).erase i, ℓ r x) * (ℓ i ((saddle even).inverse (ℓ j₀))) := by
  have hv : (fun x=> ∏ i∈s,ℓ i x) = fun x=> (Law.product ℓ (s.erase j₀) x * ℓ j₀ x):=by funext x;rw [show ∏ i∈s, ℓ i x = (ℓ j₀ x)*∏ r∈s.erase j₀,ℓ r x by exact (Finset.prod_erase_mul _ _ h).symm.trans (mul_comm ..),mul_comm];rfl
  rw [hv];exact (saddle even).recursion _ _ _ _

lemma rows_gaussian (P : ChartRatio G)(O : Observable G n)(i:ℕ)(even : Even n.val) :
   (∫ x:Dir G n,kernel fiscal x ∂tangent G (Cotree n))*gaussian even (integrandSeries (fiscal (G:=G)) (accountingWith P O) i) = rowsWith P O i :=
  by unfold rowsWith Radial.moment normTerm gaussian Law.average;rw [saddleLaw even,mul_div_cancel₀ ..]
     · rfl
     rw [← saddleLaw even];exact (integral_exp_pos (ker_integrable (G:=G) even)).ne'

end YM.PertExtension.Orb
