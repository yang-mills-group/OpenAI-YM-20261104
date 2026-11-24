import YM.Integration.WilsonGraphCenteredFarReverseBudget
import YM.GradedFar.G1.Cone
import YM.MS.Book.Triang
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The original #220 finite reverse tariff, on the #309 publication. The two editions
assign their complete response to different modules. This file uses the original
rectangular crop and the K-series field on which the reverse tariff is proved. -/

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.FVA2.GradedFar.Appointed220
open Finset PowerSeries
open scoped BigOperators Classical
variable {p : ℕ}
/-- Rectangle of indices of two separate through-p crops. -/
def rectangle (p : ℕ) : Finset (ℕ × ℕ) := (range (p+1)) ×ˢ (range (p+1))

lemma in_rectangle {i : ℕ × ℕ} : i ∈ rectangle p ↔ i.1 ≤ p ∧ i.2 ≤ p := by
  simp [rectangle]

/-- All the excess degrees, even from positive orders of replacement fields.
Denumerated with their actual coupling power (here after removing a common
factor `z^(p+1)`). -/
def excess (p : ℕ) : Finset (ℕ × ℕ) := {ij ∈ rectangle p | ¬ ij.1+ij.2 ≤ p}

open Function XSpace XSpace.Normalize XSpace.Structure1 PowerSeries
open Scale O.Score MS.Book.Program Dframe
open scoped Classical BigOperators

variable {G : Gauge} {n m H d e h : ℕ}

/-- Length factor `exp(-η)`, Far conversion `K_η(t)` (formal series in the position
coupling; we'll pass η equal to -log T, and `B` is `GroupS.gaugeN`). -/
def transfer (B : ℝ → Frames G) (η : ℝ) (d : ℕ) : Guard G d :=
  C (Level.Dial d η) * B η d


end YM.FVA2.GradedFar.Appointed220

namespace YM.FVA2.GradedFar.Appointed220.Eval
open Function Filter Set PowerSeries Finset
open scoped Topology Classical BigOperators Polynomial
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]
-- norm ONE not always one. include where needed not generally!

def sumTo (q : ℕ) (a : ℕ → R) (z : ℂ) := ∑ i∈range (q+1), z^i • a i
abbrev value (q : ℕ) (A : PowerSeries R) (z : ℂ) := sumTo q (fun i => coeff i A) z
/-- Rectangular tariff. -/
def mass (q : ℕ) (A : PowerSeries R) : ℝ := ∑ i∈range (q+1), ‖coeff i A‖

variable (A B : PowerSeries R) (g : PowerSeries ℂ) (q : ℕ) (z w : ℂ)
omit [NormedAlgebra ℂ R] in
lemma mass_nonneg : 0 ≤ mass q A := sum_nonneg (fun _ _ => norm_nonneg _)
omit [NormedAlgebra ℂ R] in
lemma access {i : ℕ} (h : i ≤ q) : ‖coeff i A‖ ≤ mass q A := single_le_sum
  (f:=fun i:ℕ => ‖coeff i A‖) (fun _ _ => norm_nonneg _) (mem_range.mpr (Nat.lt_succ_of_le h))
lemma reserve (hz : ‖z‖ ≤ 1) : ‖value q A z‖ ≤ mass q A := by
  apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _; rw [norm_smul,norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)
lemma reserve_rooted (h : coeff 0 g=0) (hz: ‖z‖ ≤ 1) : ‖value q g z‖ ≤ mass q g*‖z‖ := by
  rw [mass,sum_mul]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _
  cases i with
  | zero => simp [h]
  | succ i =>
    rw [norm_smul,norm_pow,mul_comm (‖z‖^_)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [pow_succ]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)
lemma value_one : value q (1:PowerSeries R) z=1 := by
  simp only [value,sumTo,coeff_one]; simp
lemma value_add : value q (A+B) z=value q A z+value q B z := by simp only [value,sumTo,map_add,smul_add,sum_add_distrib]
lemma value_C (a:R) : value q (C a) z=a := by
  simp only [value,sumTo,coeff_C]; simp
lemma mulC (a:R) : value q (C a*A) z=a*value q A z := by
  unfold value sumTo; rw [mul_sum]; simp_rw [coeff_C_mul,mul_smul_comm]
lemma Cmul (a:R) : value q (A*C a) z=value q A z*a := by
  unfold value sumTo; rw [sum_mul]; simp_rw [coeff_mul_C,smul_mul_assoc]
lemma value_X (hq : 0 < q) : value q X z=z := by
  simp only [value,sumTo,coeff_X]; simp [hq]
  -- cast m
lemma stars (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (k : ℕ) : ‖z^k-w^k‖ ≤ k*‖z-w‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,pow_succ,Nat.cast_add_one]
    rw [show z^k*z-w^k*w=(z^k-w^k)*z+w^k*(z-w) by ring]
    apply (norm_add_le ..).trans; rw [norm_mul,norm_mul,norm_pow,add_mul,one_mul]
    exact add_le_add ((mul_le_of_le_one_right (norm_nonneg _) hz).trans ih)
      (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hw))
lemma lipschitz (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖value q A z-value q A w‖ ≤ mass q A * (q*‖z-w‖) := by
  rw [value,value,sumTo,sumTo,← sum_sub_distrib,mass,sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum fun i hi => ?_)
  rw [←sub_smul,norm_smul,mul_comm]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (stars _ _ hz hw i).trans; gcongr; exact Nat.lt_succ_iff.mp (mem_range.mp hi)

private lemma lowProduct : value q (A*B) z=
    ∑ j∈{j∈rectangle q|j.1+j.2≤q}, z^(j.1+j.2) • (coeff j.1 A*coeff j.2 B) := by
  have low : {j∈rectangle q|j.1+j.2≤q}=(range (q+1)).biUnion antidiagonal := by
    ext x
    simp only [mem_filter,in_rectangle,Finset.mem_biUnion,Finset.mem_range,HasAntidiagonal.mem_antidiagonal]
    exact ⟨fun h => ⟨x.1+x.2,by omega,rfl⟩,fun ⟨j,h⟩ => by omega⟩
  have apart : (↑(range (q+1)) : Set ℕ).PairwiseDisjoint antidiagonal := by
    intro i _ k _ h; exact disjoint_left.mpr fun s hi hk => h ((mem_antidiagonal.mp hi).symm.trans (mem_antidiagonal.mp hk))
  rw [low,sum_biUnion apart,value,sumTo]
  apply sum_congr rfl; intro i _; rw [coeff_mul,smul_sum]
  exact sum_congr rfl fun j hj => by rw [mem_antidiagonal.mp hj]

lemma overflow : value q A z*value q B z-value q (A*B) z=
    ∑ j∈excess q, z^(j.1+j.2) • (coeff j.1 A*coeff j.2 B) := by
  have e:value q A z*value q B z=∑ j∈rectangle q, z^(j.1+j.2) • (coeff j.1 A*coeff j.2 B) := by
    rw [rectangle,sum_product,value,value,sumTo,sumTo,sum_mul_sum]
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [smul_mul_assoc,mul_smul_comm,smul_smul]; congr 1; exact (pow_add ..).symm
  apply sub_eq_iff_eq_add.mpr
  rw [e,lowProduct,add_comm]; exact (sum_filter_add_sum_filter_not ..).symm
lemma pay_product (hz : ‖z‖ ≤ 1) :
    ‖value q A z*value q B z-value q (A*B) z‖ ≤ mass q A*mass q B *‖z‖^(q+1) := by
  rw [overflow]; apply (norm_sum_le ..).trans
  let t (j : ℕ×ℕ) := ‖coeff j.1 A‖ * ‖coeff j.2 B‖ * ‖z‖^(q+1)
  calc
    _ ≤ ∑ j∈excess q, t j := sum_le_sum fun i hi => by
      rw [norm_smul,norm_pow,mul_comm]
      have h : q+1 ≤ i.1+i.2 := Nat.succ_le_of_lt (lt_of_not_ge (mem_filter.mp hi).2)
      exact mul_le_mul (norm_mul_le ..) (pow_le_pow_of_le_one (norm_nonneg _) hz h) (by positivity) (by positivity)
    _ ≤ ∑ j∈rectangle q, t j := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun j _ _ => by unfold t; positivity)
    _ = _ := by rw [mass,mass,sum_mul_sum,rectangle,sum_product]; simp [sum_mul,t]
omit [NormedAlgebra ℂ R] in
lemma mass_product : mass q (A*B) ≤ mass q A*mass q B := by
  let a (j : ℕ×ℕ) := ‖coeff j.1 A‖*‖coeff j.2 B‖
  calc
    _ ≤ ∑ i∈range (q+1), ∑ j∈antidiagonal i, a j := by
      apply sum_le_sum; intro i hi; rw [coeff_mul]
      exact (norm_sum_le ..).trans (sum_le_sum fun j _ => norm_mul_le ..)
    _ ≤ ∑ j∈rectangle q, a j := by
      rw [← sum_biUnion]
      · apply sum_le_sum_of_subset_of_nonneg
        · rintro u hu; obtain ⟨i,hi,h⟩ := mem_biUnion.mp hu
          replace hi := mem_range.mp hi; replace h := mem_antidiagonal.mp h; rw [in_rectangle]; omega
        exact fun _ _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
      intro i _ j _ h; exact disjoint_left.mpr fun s hi hj => h ((mem_antidiagonal.mp hi).symm.trans (mem_antidiagonal.mp hj))
    _ = _ := by rw [mass,mass,sum_mul_sum,rectangle,sum_product]


end YM.FVA2.GradedFar.Appointed220.Eval

namespace YM.FVA2.GradedFar.Appointed220.Eval
open MS.Book.Program
open Function Filter Set PowerSeries Finset
open scoped Topology Classical BigOperators Polynomial
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]
variable (A B C : PowerSeries R) (g : PowerSeries ℂ) (q : ℕ) (z : ℂ) {P Q F : ℝ}

def recompose (Q : PowerSeries R) (g : PowerSeries ℂ) := PowerSeries.mk (substitute g fun i => coeff i Q)

lemma exchange (h : Rooted g) : value q (recompose A g) z=∑ i∈range (q+1), value q (g^i) z • coeff i A := by
  rw [value,sumTo]; simp_rw [recompose,coeff_mk]; trans ∑ i∈range (q+1), z^i • (∑ j∈range (q+1), coeff i (g^j) • coeff j A)
  · apply sum_congr rfl; intro i hi; rw [larger h (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]; rw [Nat.range_succ_eq_Iic]
  simp_rw [value,sumTo,smul_sum,sum_smul]; rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => mul_smul .. |>.symm

lemma funded_power (k:ℕ) (hF : 1 ≤ F) (pay : mass q g ≤ F) : mass q (g^k) ≤ F^k := by
  induction k with
  | zero=> simp only [pow_zero,mass,coeff_one]; simp [apply_ite norm]
  | succ k ih=>
    rw [pow_succ]; apply (mass_product ..).trans; rw [pow_succ]; exact mul_le_mul ih pay
      (mass_nonneg ..) (pow_nonneg (zero_le_one.trans hF) _)

lemma recompose_mass (h : Rooted g) (hF : 1 ≤ F) (hp : mass q g ≤ F) : mass q (recompose A g) ≤ F^q * mass q A := by
  calc
    _ ≤ ∑ i∈range (q+1), ∑ j∈range (q+1), ‖coeff i (g^j)‖*‖coeff j A‖ := by
      apply sum_le_sum; intro i hi; rw [recompose,coeff_mk,larger h (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)),Nat.range_succ_eq_Iic]
      exact (norm_sum_le ..).trans_eq (sum_congr rfl fun _ _ => norm_smul _ _)
    _ = ∑ i∈range (q+1), mass q (g^i)*‖coeff i A‖ := by rw [sum_comm]; simp only [mass,sum_mul]
    _ ≤ _ := by
      rw [mass,mul_sum]; exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
        ((funded_power g q i hF hp).trans (pow_le_pow_right₀ hF (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))) (norm_nonneg _)

lemma vested_power (k:ℕ) (hz : ‖z‖ ≤ 1) (hF : 1 ≤ F) (hp : mass q g ≤ F) :
    ‖value q g z^k - value q (g^k) z‖ ≤ k*F^k * ‖z‖^(q+1) := by
  induction k with
  | zero=> simp only [pow_zero,value_one,sub_self,norm_zero]; simp
  | succ k ih=>
    have Fp:= zero_le_one.trans hF
    rw [pow_succ,pow_succ]
    let a := value q (g^k) z
    let b := value q g z
    rw [show b^k*b-value q (g^k*g) z=(b^k-a)*b+(a*b-value q (g^k*g) z) by ring]
    calc
      _ ≤ ‖b^k-a‖*‖b‖+mass q (g^k)*mass q g*‖z‖^(q+1) := by
        apply (norm_add_le ..).trans; exact add_le_add (norm_mul_le _ _) (pay_product _ _ q z hz)
      _ ≤ k*F^k*‖z‖^(q+1)*F+F^k*F*‖z‖^(q+1) := add_le_add (mul_le_mul ih ((reserve g q z hz).trans hp) (norm_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_right (mul_le_mul (funded_power _ _ _ hF hp) hp (mass_nonneg g _) (by positivity)) (by positivity))
      _ = _ := by push_cast; ring
lemma payCompose (h : Rooted g) (hz : ‖z‖ ≤ 1) (hF : 1 ≤ F) (hp : mass q g ≤ F) :
    ‖value q A (value q g z)-value q (recompose A g) z‖ ≤ (q*F^q)*mass q A*‖z‖^(q+1) := by
  rw [exchange A g _ _ h]; unfold value sumTo at *; rw [← sum_sub_distrib]
  let a := q*F^q*‖z‖^(q+1); have Fp := zero_le_one.trans hF
  apply (norm_sum_le ..).trans
  calc _ ≤ ∑ i∈range (q+1),a*‖coeff i A‖ := sum_le_sum fun i hi=> by
          rw [← sub_smul,norm_smul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply (vested_power g q z i hz hF hp).trans
          have hg : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi); dsimp only [a]; gcongr
       _ = _ := by rw [← mul_sum]; unfold a mass; ring

end YM.FVA2.GradedFar.Appointed220.Eval

namespace YM.FVA2.GradedFar.Appointed220.Zones
open Function Set Filter FVA2.Scale O O.Enh O.Score PowerSeries XSpace XSpace.Normalize
open MS MS.Land MS.Book.Program Dframe
open scoped Topology Classical BigOperators Polynomial
variable {G:Gauge}{d:ℕ} {V:Arenas G}{ψ:ℝ→ Cn}{B:ℝ→Frames G}(law:Scale.Law V ψ B)
    {R:Type*}[NormedRing R][NormedAlgebra ℂ R](f:FieldEnd G d →ₐ[ℂ] R)
variable (s t:ℝ)
lemma pulled (p: Guard G d)(u: Cn) : PowerSeries.map f.toRingHom (Reg.Point.stepV u p)=
    Appointed220.Eval.recompose (PowerSeries.map f.toRingHom p) u := by
  ext1 i; simp [PowerSeries.coeff_map,Eval.recompose, Reg.Point.stepV, rules, map_sum, map_smul]

abbrev liftSeries (p: Guard G d) := PowerSeries.map f.toRingHom p
abbrev carry (B:ℝ→Frames G) (a:ℝ) := liftSeries f (transfer B a d)
abbrev backStory (B:ℝ→Frames G) (a:ℝ) := liftSeries f (Scale.mirror (B a d)* C (Level.Dial d (-a)))
include law
lemma aft : carry f B t*backStory f B t=1 := by
  rw [carry,backStory,liftSeries,liftSeries,←map_mul,transfer]
  refine Eq.trans (congrArg (PowerSeries.map f.toRingHom) ?_) (map_one _); rw [mul_assoc,←mul_assoc (B t d),
    (law.paid t d).turn',one_mul,← map_mul,Level.autumn,map_one]
lemma fore : backStory f B t*carry f B t=1 := by
  rw [carry,backStory,liftSeries,liftSeries,← map_mul,transfer]; refine Eq.trans (congrArg (PowerSeries.map f.toRingHom) ?_) (map_one _)
  rw [mul_assoc,←mul_assoc (C _),←map_mul,Level.spring,map_one,one_mul,(law.paid t d).turn]

end YM.FVA2.GradedFar.Appointed220.Zones

namespace YM.FVA2.GradedFar.Appointed220.Zones
open Function Set Filter FVA2.Scale O O.Enh O.Score PowerSeries XSpace XSpace.Normalize
open MS MS.Land MS.Book.Program Dframe Finset
open scoped Topology Classical BigOperators Polynomial
variable {G:Gauge}{d:ℕ} {V:Arenas G}{ψ:ℝ→Cn}{B:ℝ→Frames G}(law:Scale.Law V ψ B)
    {R:Type*}[NormedRing R][NormedAlgebra ℂ R](f:FieldEnd G d →ₐ[ℂ] R)

private def length (s:ℝ):=1+|s|
private lemma basic (s:ℝ):1≤length s:=le_add_of_nonneg_right (abs_nonneg _)
private lemma lengthP (s:ℝ): 0≤length s:=(zero_lt_one.trans_le (basic s)).le
private lemma scope {h:ℝ→ℂ}(s:Rhythm h) : ∃ L:ℝ,0≤L ∧ ∃ a:ℕ, ∀ t, ‖h t‖≤L*(length t)^a:=by
  obtain ⟨p,rfl⟩:=Rhythm.from_poly.mp s
  refine ⟨∑k∈p.support,‖p.coeff k‖,sum_nonneg fun _ _=>norm_nonneg _,p.natDegree,?_⟩
  intro t
  change ‖p.eval (t:ℂ)‖≤ _; rw [Polynomial.eval_eq_sum,sum_mul]
  refine le_trans (norm_sum_le p.support _) (sum_le_sum fun i hi =>?_)
  change ‖p.coeff i*(t:ℂ)^i‖≤ _; rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc _ ≤ length t ^ i := by gcongr; exact le_add_of_nonneg_left zero_le_one
       _ ≤ length t ^ p.natDegree := pow_le_pow_right₀ (basic t) (Polynomial.le_natDegree_of_mem_supp _ hi)
private lemma joint {I:Type*} (s:Finset I) (u : I → ℝ → ℝ) (price:∀ i, ∃ L:ℝ,0≤L ∧ ∃ a:ℕ, ∀ t,u i t≤L*length t^a) :
    ∃ L:ℝ,0≤L ∧ ∃ a:ℕ,∀ t, ∑ i∈s,u i t≤L*(length t)^a := by
  choose L h a p using price
  refine ⟨∑ i∈s,L i,sum_nonneg fun i _ =>h i,∑i∈s,a i,fun t=>?_⟩
  rw [sum_mul]
  exact sum_le_sum fun i hi=> (p i t).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (basic t)
     (single_le_sum (f:=a) (fun _ _=>Nat.zero_le _) hi)) (h i))

include law in
lemma clock_log (q:ℕ) : ∃ L:ℝ,0≤L ∧ ∃ a:ℕ, ∀ t, Eval.mass q (ψ t)≤L*(1+|t|)^a :=
  joint (range (q+1)) _ fun k=> scope (Rhythm.unit.mpr (law.smooth k))

local notation "U" => Sec G d
local notation "F" => FieldEnd G d
private lemma each_end (x:ℝ→F)(h:∀ p:U,∀ v:U→ₗ[ℂ]ℂ,Rhythm (fun t=>v (x t p))):
    ∃ L:ℝ,0≤L ∧ ∃ a:ℕ, ∀ t:ℝ, ‖f (x t)‖≤ L*length t^a := by
  let b := Module.finBasis ℂ U; let P:=b.end
  let I := Fin (Module.finrank ℂ U)
  let lp (i:I×I): U→ₗ[ℂ]ℂ := b.coord i.1
  let read (i:I×I)(t:ℝ) := lp i (x t (b i.2))
  have eq_eval(i:I×I)(u:F):P.coord i u=lp i (u (b i.2)) := by
    let L:= (lp i) ∘ₗ (LinearMap.applyₗ (R:=ℂ) (b i.2))
    have hx:P.coord i=L := by
      apply P.ext; intro j
      by_cases h : j.2=i.2 <;> simp [P,L,lp,Module.Basis.end_apply_apply, h,Finsupp.single_apply, Prod.ext_iff]
    rw [hx]; rfl
  have price(i:I×I):∃ L:ℝ,0≤L ∧∃ a:ℕ, ∀s, ‖read i s • f (P i)‖ ≤ L*length s^a:=by
    obtain ⟨L,p,k,H⟩:=scope (h (b i.2) (lp i)); refine ⟨L*‖f (P i)‖,by positivity,k,?_⟩
    intro s; rw [norm_smul,mul_right_comm L]; exact mul_le_mul_of_nonneg_right (H s) (norm_nonneg _)
  obtain ⟨L,hP,a,eq⟩ := joint (Finset.univ : Finset (I×I)) _ price
  refine ⟨L,hP,a,fun t=>?_⟩
  have hx (i: I×I): P.repr (x t) i=read i t := eq_eval i (x t)
  conv_lhs => rw [← P.sum_repr (x t),map_sum]; simp only [hx,map_smul]
  exact (norm_sum_le ..).trans (eq t)

lemma pulse_log (D:ℝ→Guard G d)(q:ℕ) (h:∀ k, Meter.Tracks D k) :
    ∃ L:ℝ,0≤L ∧ ∃ a:ℕ, ∀ t:ℝ, Eval.mass q (liftSeries f (D t))≤ L* (1+|t|)^a := by
  simp_rw [Eval.mass,liftSeries, PowerSeries.coeff_map]
  exact joint (range (q+1)) _ (fun i=>each_end f (fun s=>coeff i (D s)) (h i))

lemma speed_D : ∃ L:ℝ,0≤L ∧ ∀ t:ℝ, ‖f (Level.Dial d t)‖≤ L*(max 1 (Real.exp (-t)))^d := by
  let P := ∑ i:Level.E d, ‖f (Level.proj i)‖
  refine ⟨P,Finset.sum_nonneg (fun _ _=>norm_nonneg _), fun t=>?_⟩; unfold Level.Dial;
  rw [map_sum]; unfold P; rw [sum_mul]
  refine (norm_sum_le ..).trans (sum_le_sum fun i hi=>?_)
  rw [map_smul, norm_smul,Extent.token,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_comm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact le_trans (pow_le_pow_left₀ (Real.exp_pos _).le (le_max_right ..) i.val)
    (pow_le_pow_right₀ (le_max_left ..) (Nat.le_of_lt_succ i.isLt))

omit [NormedAlgebra ℂ R] in
lemma CM (q:ℕ) (P:R) : Eval.mass q (PowerSeries.C P)=‖P‖ := by
  simp only [Eval.mass,coeff_C]; simp [apply_ite norm]

/- No subsumption of T^d loss at logarithmic size. -/
include law
lemma pricePrint (q : ℕ) : ∃ L:ℝ, 0≤L ∧ ∃ a:ℕ, ∀t,
    Eval.mass q (carry f B t)≤ L*(max 1 (Real.exp (-t)))^d*(1+|t|)^a := by
  obtain ⟨X,hX,u⟩ := speed_D f; obtain ⟨P,hP,i,h⟩:= pulse_log f _ q (law.proper d)
  refine ⟨X*P,by positivity,i,fun t=>?_⟩
  rw [carry,liftSeries,transfer,map_mul,PowerSeries.map_C]; apply (Eval.mass_product ..).trans;
  refine le_trans ?_ (le_of_eq (show X* (max 1 (Real.exp (-t)))^d*(P*(1+|t|)^i)=_ by ring));
  rw [CM]; apply mul_le_mul (u t) (h t) (Eval.mass_nonneg ..) (by positivity)
lemma priceBack (q : ℕ) : ∃ L:ℝ, 0≤L ∧ ∃ a:ℕ, ∀t,
    Eval.mass q (backStory f B t)≤ L*(max 1 (Real.exp t))^d*(1+|t|)^a := by
  obtain ⟨X,hX,u⟩ := speed_D f; obtain ⟨P,hP,i,h⟩:= pulse_log f _ q (law.invert d)
  refine ⟨P*X,by positivity,i,fun t=>?_⟩; rw [backStory,liftSeries,map_mul,PowerSeries.map_C]
  apply (Eval.mass_product ..).trans; refine le_trans ?_ (le_of_eq (show P*(1+|t|)^i*(X*(max 1 (Real.exp (- -t)))^d)=_ by rw [neg_neg];ring))
  rw [CM]; apply mul_le_mul (h t) (u (-t)) (norm_nonneg _) (by positivity)

end YM.FVA2.GradedFar.Appointed220.Zones

namespace YM.FVA2.GradedFar.Appointed220.Zones.Budget
open Function Set Filter Real FVA2.Scale O O.Enh O.Score PowerSeries XSpace XSpace.Normalize
open MS MS.Land MS.Book.Program Dframe
open YM.FVA2.GradedFar.G1.Wire
open scoped Topology Classical BigOperators Polynomial
variable {G:Gauge}{d:ℕ} {V:Arenas G}{ψ:ℝ→Cn}{B:ℝ→Frames G}(law:Scale.Law V ψ B)
    {R:Type*}[NormedRing R][NormedAlgebra ℂ R](f:FieldEnd G d →ₐ[ℂ] R)
variable (K q:ℕ)
abbrev eta (T:ℝ):ℝ := -(Real.log T)
local notation "η" => eta
local notation "time'" => ψ
local notation "v" => Eval.value q
local notation "g⋆" => (𝓝[>] (0:ℝ) : Filter ℝ)
local notation "A" => carry f B
local notation "U" => backStory f B
local notation "M" => Eval.mass q
local notation "one'" => max 1
local notation "φ" => fun T=> Eval.mass q (ψ (eta T))
lemma etabs {T:ℝ}(h:1≤T): |eta T|=log T:= (abs_neg _).trans (abs_of_nonneg (log_nonneg h))
lemma eta_max {T:ℝ}(h:1≤T):max 1 (Real.exp (eta T))=1 ∧ max 1 (Real.exp (-(eta T)))=T := by
  have t:=zero_lt_one.trans_le h
  unfold eta; rw [Real.exp_neg, Real.exp_log t,neg_neg,Real.exp_log t]; exact ⟨max_eq_left (inv_le_one_of_one_le₀ h),max_eq_right h⟩
include law
lemma moments (a:ℕ) {δ:ℝ}(h:0<δ) :
    ∀ᶠ g in g⋆,∀T, Edge K g T→(max 1 (M (ψ (eta T))))^a*g ≤ δ := by
  obtain ⟨L,hL,n,l⟩:=clock_log law q
  filter_upwards [distills (a:=n*a) h (pow_nonneg (a:=1+L) (by linarith) a) K,self_mem_nhdsWithin (α:=ℝ) (a:=0)]
    with g w gp T u; have p:0<g:=gp
  have le : max 1 (M (ψ (eta T)))≤(1+L)*tick T^n := by
    have b:1≤tick T^n:=one_le_pow₀ (_root_.YM.FVA2.GradedFar.G1.Wire.starts u.1)
    have a:=l (eta T); rw [etabs u.1] at a; rw [add_mul,one_mul]; exact max_le
      (le_add_of_nonneg_right (mul_nonneg hL (by linarith)) |> le_trans b)
      (le_trans a (le_add_of_nonneg_left (by linarith)))
  apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) le a) p.le)
  rw [mul_pow, ← pow_mul]; exact w T u

lemma location {δ:ℝ}(h:0<δ) :
    ∀ᶠ g in g⋆,∀ T, Edge K g T → ∀ z:ℂ, ‖z‖ ≤ 2*g → ‖v (ψ (eta T)) z‖ ≤ δ := by
  filter_upwards [moments law K q 1 (δ:=δ/2) (by positivity), Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with g m e T u z h
  have gp:0<g:=e.1; have he:g ≤ 1/2:=e.2
  apply (Eval.reserve_rooted _ q z (law.led _).start (by linarith)).trans
  specialize m T u; rw [pow_one] at m
  calc _ ≤ max 1 (M (ψ (η T)))*(2*g) := mul_le_mul (le_max_right ..) h (norm_nonneg _) (by positivity)
       _ ≤ δ := by linarith
lemma sizes : ∀ᶠ g in g⋆,∀ T, Edge K g T → M (A (eta T))≤ T^d*g⁻¹ ∧ M (U (eta T))≤g⁻¹ := by
  obtain ⟨L,e,n,u⟩:= pricePrint law f q; obtain ⟨P,c,w,p⟩:=priceBack law f q
  filter_upwards [distills zero_lt_one e n K,distills zero_lt_one c w K,self_mem_nhdsWithin (α:=ℝ) (a:=0)] with g hL hP h T k
  have T₀:=k.1; have g₀:0<g:=h
  specialize u (η T); specialize p (η T); rw [(eta_max T₀).2, etabs T₀] at u
  rw [(eta_max T₀).1, etabs T₀, one_pow,mul_one] at p
  have v₁ := hL T k; have v₂ := hP T k
  constructor
  · rw [← div_eq_mul_inv]; apply (le_div_iff₀ g₀).mpr; apply (mul_le_mul_of_nonneg_right u g₀.le).trans
    calc _=T^d*(L*tick T^n*g):=by unfold tick; ring
         _ ≤ _ := mul_le_of_le_one_right (pow_nonneg (zero_le_one.trans T₀) _) v₁
  rw [← one_div]; exact (le_div_iff₀ g₀).mpr ((mul_le_mul_of_nonneg_right p g₀.le).trans v₂)

end YM.FVA2.GradedFar.Appointed220.Zones.Budget

namespace YM.FVA2.GradedFar.Appointed220.Zones.Telescope
open Function Set Filter FVA2.Scale O O.Enh O.Score PowerSeries XSpace XSpace.Normalize
open MS MS.Land MS.Book.Program Dframe Budget YM.FVA2.GradedFar.G1.Wire
open scoped Topology Classical BigOperators Polynomial
variable {G : Gauge} {d : ℕ} {V : Arenas G} {ψ : ℝ → Cn} {B : ℝ → Frames G}
  (law : Scale.Law V ψ B) {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]
  (f : FieldEnd G d →ₐ[ℂ] R) (q K : ℕ)
local notation "v♪" => Eval.value q
local notation "A" => carry f B
local notation "U" => backStory f B
local notation "η" => eta
local notation "M" => Eval.mass q
local notation "g⋆" => (𝓝[>] (0:ℝ) : Filter ℝ)
include law
lemma reverse_price {L:ℕ} (net:L+2+K*d≤q) :
    ∃ P:ℝ,0≤P∧ ∀ᶠ x in g⋆, ∀ T, Edge K x T → ∀ z:ℂ, ‖z‖≤ 2*x →
      ‖v♪ (A (η T)) z*v♪ (U (η T)) z-1‖ ≤ P*x^L := by
  refine ⟨(2:ℝ)^(q+1),by positivity,?_⟩
  filter_upwards [sizes law f K q,Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with x p a T e z pz
  have xp:0<x:=a.1
  have xx:x≤1:= by linarith [a.2]
  have tp:0<T:=zero_lt_one.trans_le e.1
  have h:=p T e
  have z' := Eval.pay_product (A (η T)) (U (η T)) q z (show ‖z‖ ≤1 by linarith [a.2])
  rw [aft law f, Eval.value_one] at z'
  apply z'.trans
  calc _ ≤ T^d*x⁻¹*x⁻¹ * (2*x)^(q+1) := mul_le_mul (mul_le_mul h.1 h.2 (Eval.mass_nonneg ..) (by positivity))
            (pow_le_pow_left₀ (norm_nonneg _) pz _) (by positivity) (by positivity)
       _ ≤ _ := by
          have ht : T^d*x^(q-1)≤x^L := _root_.YM.FVA2.GradedFar.G1.Wire.taper (by omega) xp xx e
          calc _=(2:ℝ)^(q+1)*(T^d*x^(q-1)) := by
                  rw [mul_pow, show x^(q+1)=x^(q-1)*x*x by rw [←pow_succ,←pow_succ, show q-1+1+1=q+1 by omega]]
                  field_simp
               _≤_:=mul_le_mul_of_nonneg_left ht (by positivity)

end YM.FVA2.GradedFar.Appointed220.Zones.Telescope

