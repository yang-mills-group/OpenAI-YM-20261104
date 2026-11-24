import YM.FormalOPE.RG10.HStein.Placement
import Mathlib.RingTheory.MvPolynomial.Homogeneous
/-!
 # Homogeneous slices on one Episode

 Use arbitrary reexpression; need exact Through-order equality on newly certified stencil sector
 defined by perturbative Ward series when changing representatives. Here no gauge-fixing section is
 constructed. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.GaugeGear
open HStein Route Route.Bulk PowerSeries Function Finset
open Multi.Vacuum.Gauss
open scoped Topology BigOperators Classical
variable {I B J : Type} [Fintype J]
local notation "Q"=> Packet (I⊕B)
variable (e:Episode I B J) (p q : Channel I) (P:Packet I) (c:ℂ) (k:ℕ)
local notation "φ" => e.spur
local notation "V" => e.vertices
local notation "J*" => e.joint

lemma opt_episode : e.floats (PowerSeries.C P)=transfer e.joint (MvPolynomial.aeval φ P) V:= by unfold Episode.floats; change transfer _ _ V= _; rw [replot_constant]
lemma switches (h:Through k p q): Through k (e.floats p) (e.floats q) := by
 apply HStein.through_transfer _ _ k; exact mapCoeff.near_aux (f:=(MvPolynomial.aeval φ : Packet I →ₐ[ℂ] Channel (I⊕B)).toRingHom) h
lemma atTick : e.floats (monomial k P)=X^k * e.floats (C P):= by
 unfold Episode.floats; change transfer _ _ V = X^k * transfer _ _ V
 unfold replot mapCoeff.throwTo; change transfer _ (mapCoeff.push _ _) _ = _; rw [mapCoeff.push_mono,paid]; congr 2; exact (replot_constant _ P).symm

def beam : Packet I→ₗ[ℂ] Packet B where
 toFun P:= coeff k (e.floats (C P))
 map_add' p q:= by simp
 map_smul' c p:= by change coeff k (e.floats (C (c • p)))= c • coeff k (e.floats (C p)); simp_rw [opt_episode,←send,map_smul,coeff_smul]
lemma beams : beam e k P=coeff k (e.floats (C P)):= rfl
lemma amounts : coeff k (e.floats p)=∑ i∈antidiagonal k,beam e i.2 (coeff i.1 p) := by
 rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>beam e j (coeff i p))]
 have he:Through k p (∑ i∈range (k+1), monomial i (coeff i p)):= by intro i hi; rw [map_sum]; simp [coeff_monomial,mem_range,hi]
 rw [switches _ _ _ _ he k le_rfl,map_sum,map_sum]; apply sum_congr rfl;intro i hi; rw [atTick,coeff_X_pow_mul',if_pos (Nat.le_of_lt_succ (mem_range.mp hi)),beams]
lemma boom {i j :ℕ} : beam e j P=coeff (i+j) (e.floats (monomial i P)) := by rw [atTick,coeff_X_pow_mul']; simp [beams]

def first (b:I):= coeff 0 (φ b)


open MvPolynomial (aeval aeval_X)
omit [Fintype J] in
lemma born (p:Packet I) : coeff 0 (MvPolynomial.aeval φ p) = MvPolynomial.aeval (first e) p:= by
 induction p using MvPolynomial.induction_on with
 | C c=> rw [MvPolynomial.aeval_C,MvPolynomial.aeval_C]; rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,coeff_smul,coeff_zero_one]
 | add p q hp hq=> rw [map_add,map_add, map_add,hp,hq]
 | mul_X p i hp=> rw [map_mul,_root_.map_mul (MvPolynomial.aeval (R:=ℂ) (first e)),aeval_X,aeval_X, coeff_zero_eq_constantCoeff_apply,map_mul]; rw [←coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply,hp]; rfl
lemma opt_flat (p:Packet (I⊕B)): opt e.joint V 0 p= hand e.joint p:= by
 unfold opt; change coeff 0 (transfer _ (C p) _) = _; rw [transfer,coeff_zero_eq_constantCoeff_apply,map_mul]; rw [← coeff_zero_eq_constantCoeff_apply,← coeff_zero_eq_constantCoeff_apply,move,coeff_mk,coeff_invOfUnit,if_pos rfl,coeff_mul_C,advanced_start]; simp
lemma start : beam e 0 P=hand e.joint (aeval (first e) P):= by
 rw [beams,opt_episode,rational]; simp only [Finset.Nat.antidiagonal_zero, sum_singleton]; rw [opt_flat,born]
lemma beam_unit : beam e k (1:Packet I)=if k=0 then 1 else 0 := by rw [beams,map_one,Episode.float_one,coeff_one]
lemma beam_scalar : beam e k (MvPolynomial.C c) = if k=0 then MvPolynomial.C c else 0:= by
 have h {B:Type}: MvPolynomial.C (σ:=B) c = c • (1:Packet B) := Algebra.algebraMap_eq_smul_one _
 rw [h,map_smul,beam_unit,h]; split <;> simp
end YM.FormalOPE.RG10.GaugeGear
