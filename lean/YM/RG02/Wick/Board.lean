import YM.RG02.Wick.Hessian
import YM.RG02.Marker.Restriction

/-!
A script of vertices varies polynomially on unbounded fields at every
(coefficient,mode). This is convenient for finite Wick contraction under a
parameter and markers at the same time. Multiple presentations allowed with
no change to integrated result. Finer readout of rooted/address/path data
must use actual presentations and keep their indicated costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Wick
open Finset Marker Multi Extra.Trajectories Marks Next.Rank Next.Rank.Normal
open Function MeasureTheory
open PertExtension GaussianScore
open scoped BigOperators Classical
variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {V : Type} [DecidableEq V] {R : Census V}

def Wires (f : E → ℂ) := ∃ p, f=paint (id : (Module.Dual ℝ E) → _) p -- constrain W
namespace Wires
local notation "S" => ((id : Module.Dual ℝ E → Module.Dual ℝ E))
variable {f g : E → ℂ}
lemma const (c : ℂ) : Wires (fun _ : E => c) := ⟨MvPolynomial.C c, funext fun x => by simp [paint]⟩
lemma add (h : Wires f) (hh : Wires g) : Wires (f+g) := by
  obtain ⟨p,rfl⟩ := h; obtain ⟨q,rfl⟩ := hh; exact ⟨p+q, funext fun x => by simp [paint]⟩
lemma mul (h : Wires f) (hh : Wires g) : Wires (f*g) := by
  obtain ⟨p,rfl⟩ := h; obtain ⟨q,rfl⟩ := hh; exact ⟨p*q,funext fun x => by simp [paint]⟩
lemma smul (h : Wires f)(c : ℂ) : Wires (c • f) := (const (E:=E) c).mul h
lemma neg (h : Wires f) : Wires (-f) := by simpa using h.smul (-1)
lemma sub (h : Wires f)(hg : Wires g) : Wires (f-g) := by rw [sub_eq_add_neg]; exact h.add hg.neg
lemma power (h : Wires f)(k : ℕ) : Wires (f^k) := by induction k with
 | zero => rw [pow_zero]; exact const 1
 | succ k ih => rw [pow_succ]; exact ih.mul h
lemma sum {I : Type*}(s : Finset I)(f : I → E → ℂ)(h : ∀ i∈s,Wires (f i)) : Wires (∑ i∈s,f i) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact const 0
  | insert i s hi ih => rw [sum_insert hi]; exact (h _ (mem_insert_self ..)).add (ih fun i hi => h i (mem_insert_of_mem hi))
lemma sum_x {I : Type*}(s : Finset I)(f : I → E → ℂ)(h : ∀ i∈s,Wires (f i)) : Wires fun x => ∑ i∈s,f i x := by
  rw [show (fun x => ∑ i∈s,f i x)=_ from ?_]; exact sum s f h
  funext x; symm; exact sum_apply x s f
lemma port (L : E→ₗ[ℝ]ℝ) : Wires fun x => (L x:ℂ) := ⟨MvPolynomial.X L, funext fun _ => by simp [paint]⟩

lemma prod {I : Type*}(s : Finset I)(f : I → E → ℂ)(h : ∀ i∈s,Wires (f i)) : Wires fun x => ∏ i∈s,f i x := by
  induction s using Finset.induction_on with
  | empty => simp_rw [prod_empty]; exact const 1
  | insert i s hi ih => simp_rw [prod_insert hi]; exact (h i (mem_insert_self ..)).mul (ih fun i hi => h _ (mem_insert_of_mem hi))

variable [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]

set_option backward.isDefEq.respectTransparency false in
lemma address {n : ℕ}(F : ContinuousMultilinearMap ℝ (fun _ : Fin n=>X) ℂ)
    (f : Fin n → E→ₗ[ℝ]X)(w : Fin n→X) : Wires fun x => F fun i => f i x + w i := by
  let N:= Module.finrank ℝ X
  let B := Module.finBasis ℝ X
  let b (i : Fin n) (j : Fin N) (x : E) := B.coord j (f i x + w i)
  have h (i : Fin n) (x : E) : (∑ j : Fin N,b i j x • B j) = f i x + w i := B.sum_repr _
  let G := F.toMultilinearMap
  let H : Fin n→ Fin N→ E → ℂ := fun i j x => ↑(b i j x)
  have hb (i j) : Wires (H i j) := by
    change Wires fun x=> H i j x
    simp_rw [H,b,map_add,Complex.ofReal_add]
    exact (port ((B.coord j) ∘ₗ f i)).add (const _)
  have he : (fun x => F fun i => f i x+w i)=fun x => ∑ z:Fin n→Fin N,(∏ i:Fin n,H i (z i) x)*F fun i=>B (z i) := by
    funext x
    change G (fun i => f i x+w i)=_
    simp_rw [← h]; rw [G.map_sum]; apply sum_congr rfl; intro i _
    rw [G.map_smul_univ]; simp_rw [H, Complex.real_smul, Complex.ofReal_prod]; rfl
  rw [he]; apply sum_x univ (fun z x=> _) (fun i _ => ?_)
  exact (prod univ (fun j => H j (i j)) (fun _ _ => hb ..)).mul (const _)

lemma lists (f : X→ℝ)(k : ℕ)(L : E→ₗ[ℝ]X)(z : X) : Wires fun x=> (Series.Radial.jet f k (L x+z):ℂ) := by
  simp_rw [Series.Radial.jet,Complex.ofReal_mul]
  exact (const _).mul (address (Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ k f 0)) (fun _=>L) (fun _=>z))
end Wires

def stroke (z : E→ ℂ) : poly (Module.Dual ℝ E) := if h : Wires z then h.choose else 0
lemma painted {z : E→ℂ}(h : Wires z) : paint id (stroke z)=z := by rw [stroke,dif_pos h,h.choose_spec.symm]

section script
open Grade PowerSeries

/-- Mixed action script, uses one column for EACH mode of the census.
Markers here are disjoint-source, not to be included in polynomial leg variables W. -/
def Edged (z : E → Script R) := ∀ n : ℕ, ∀ s : R.Mode, Wires fun x => (coeff n (z x)).part s
namespace Edged
variable {x y : E → Script R}
lemma fixed (z : Script R) : Edged fun _ : E=> z := fun _ _ => Wires.const _
lemma empty : Edged fun _ : E => (0:Script R) := fixed _
lemma linear (h : Edged x)(hd : Edged y) : Edged (x+y) := by
   intro i s; simp_rw [Pi.add_apply,map_add,Poly.part_plus]; exact (h i s).add (hd i s)
lemma scaled (h : Edged x)(c : ℂ) : Edged (c • x) := by
   intro i s; simp_rw [Pi.smul_apply, coeff_smul, Poly.part_smul]; exact (h i s).smul c
lemma times (h : Edged x)(hd : Edged y) : Edged (x*y) := by
   intro i s; simp_rw [Pi.mul_apply,coeff_mul,Poly.part_sum,Poly.part_mul]
   apply Wires.sum_x (Finset.antidiagonal i) (fun j p => _) (fun v _ => ?_)
   apply Wires.sum_x univ (fun j p => _) (fun a _ => ?_); apply Wires.sum_x univ (fun j p => _) (fun b _ => ?_)
   split; exact (h _ _).mul (hd _ _)
   exact Wires.const 0
lemma powers (h : Edged x)(i : ℕ) : Edged (x^i) := by induction i with
  | zero => rw [pow_zero]; exact fixed 1
  | succ i ih => rw [pow_succ]; exact ih.times h
lemma sums {I : Type*}(s : Finset I)(f : I→ E→ Script R)(h : ∀ i∈s,Edged (f i)) : Edged (∑ i∈s,f i) := by
   induction s using Finset.induction_on with
   | empty => rw [sum_empty]; exact fixed 0
   | insert i s hi ih => rw [sum_insert hi]; exact (h i (mem_insert_self ..)).linear (ih (fun j hj => h j (mem_insert_of_mem hj)))
lemma pass [Fintype V](h : Edged x) : Edged fun p => Grade.exponential (x p) := by
   intro n i; let s:=range (n+Fintype.card V+1)
   let f (i:ℕ) := (i.factorial:ℂ)⁻¹ • x^i
   convert! sums s f (fun i _=> (h.powers i).scaled _) n i using 1
   funext p;  simp only [exponential,PowerSeries.coeff_mk]; simp only [Finset.sum_apply,Pi.pow_apply,Pi.smul_apply,s,f]
lemma encodes (h : Edged x)(r : ℕ)(t : (mixed r R).Mode) : Wires fun z=> (encode r (x z)).part t := by
   simp_rw [encode_part]; exact (h _ _).smul _
end Edged

-- integrator state-independent. Check board agrees with any other leg
-- dictionary supplied to positive/character/context estimates. Centered *E* fields.
variable [FiniteDimensional ℝ E]

def weigh (Γ : Law E)(f : E→ℂ) := charge Γ id (stroke f)

def made (Γ : Law E)(f : E→Script R) : Script R := PowerSeries.mk fun n =>
    Poly.inject fun s => weigh Γ fun x => (coeff n (f x)).part s

lemma made_part (Γ : Law E)(f : E→Script R)(n : ℕ)(s : R.Mode) :
    (coeff n (made Γ f)).part s=weigh Γ fun x=> (coeff n (f x)).part s := by rw [made, coeff_mk]; rfl

variable [MeasurableSpace E][BorelSpace E]
variable (Γ : Law E)(μ : Measure E) [μ.HasTemperateGrowth][μ.IsAddRightInvariant][NeZero μ]
include μ

lemma agrees {f : E→ℂ} (h : Wires f) : weigh Γ f=normed Γ μ f := by rw [weigh,← analytic_pairing Γ μ id,painted h]

lemma binds {I : Type}(ℓ : I→Module.Dual ℝ E)(p : poly I){f : E→ℂ}(h : Wires f)(hp : paint ℓ p=f) :
    weigh Γ f=charge Γ ℓ p := (agrees Γ μ h).trans (hp ▸ analytic_pairing Γ μ ℓ p)

theorem interpretation {f : E→Script R}(h : Edged f)(n : ℕ)(s : R.Mode) :
    (coeff n (made Γ f)).part s=normed Γ μ fun x => (coeff n (f x)).part s := by rw [made_part,agrees Γ μ (h n s)]

lemma fixed (f:E→ℂ)(c : ℂ)(hp : f=fun _ => c) : weigh Γ f=c := by
   subst f; rw [binds Γ μ id (MvPolynomial.C c : poly (Module.Dual ℝ E)) (Wires.const _)]
   · rw [show (MvPolynomial.C c: poly (Module.Dual ℝ E))=c • 1 from Algebra.algebraMap_eq_smul_one c,map_smul,charge_one,smul_eq_mul,mul_one]
   funext x; simp [paint]

lemma weigh_smul {f : E→ℂ}(h : Wires f)(c : ℂ) : weigh Γ (c • f)=c*weigh Γ f := by
   rw [agrees Γ μ (h.smul c),agrees Γ μ h]
   unfold normed; simp_rw [Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul]; ring
lemma weighs_add {f g : E→ℂ}(h : Wires f)(hg : Wires g) : weigh Γ (f+g)=weigh Γ f+weigh Γ g := by
   rw [agrees Γ μ (h.add hg),agrees Γ μ h,agrees Γ μ hg]
   unfold normed; simp_rw [Pi.add_apply,add_mul]
   rw [integral_add,add_div]
   · nth_rw 1 [← painted h]; exact paint_integrable Γ μ id _
   nth_rw 1 [← painted hg]; exact paint_integrable Γ μ id _

theorem on_mode {f : E→Script R}(h : Edged f)(r : ℕ)(s : (mixed r R).Mode) :
    (encode r (made Γ f)).part s=weigh Γ fun x => (encode r (f x)).part s := by
   simp_rw [encode_part]; rw [made_part]; exact (weigh_smul Γ μ (h _ _) _).symm
end script
end YM.RG02.Wick
