import YM.RG02.Limit.At
import YM.RG02.Marker.CarryLog

/-!
Finite asymptotic expansions pointwise, without constant uniformity. Use for
identifying coefficients *before* carrying estimates in volume-dependent
representations. Downward closed modes, coupling grade as in script. Gives
exact projected denominator and inverse interpretation on this INTERIOR ray of
fixed fields; doesn't extend this assertion termwise to all failure masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Asym
open PertExtension.Series.Tested PertExtension.Series Filter Finset Topology PowerSeries
open Marker Extra.Trajectories Marks Grade Function
open scoped BigOperators Classical
variable {V : Type} [DecidableEq V]{R : Census V}

def onMode (x : Script R)(s : R.Mode) := PowerSeries.mk fun i => (coeff i x).part s

lemma mode_coeff (x : Script R)(s : R.Mode)(n : ℕ) :
    coeff n (onMode x s)=(coeff n x).part s := coeff_mk ..

lemma mode_one (x : Script R) : onMode x R.quiet=den x := by
   ext i; rw [mode_coeff,den,coeff_map]; rfl

lemma mode_scalar (x : PowerSeries ℂ)(s : R.Mode) : onMode (scalar R x) s=if s=R.quiet then x else 0 := by
   ext i; rw [mode_coeff,scalar,PowerSeries.coeff_map];
   by_cases h : s=R.quiet <;> simp [Poly.bead,h]
lemma mode_atom (x : Poly R)(s : R.Mode) : onMode (C x) s=C (x.part s) := by
   ext i; rw [mode_coeff,PowerSeries.coeff_C,PowerSeries.coeff_C]; by_cases h : i=0 <;> simp [h]
lemma mode_product (x y : Script R)(s : R.Mode) : onMode (x*y) s =
   ∑ i : R.Mode, ∑ j : R.Mode, if Poly.merges i j s then onMode x i*onMode y j else 0 := by
   ext k
   simp_rw [mode_coeff,coeff_mul,Poly.part_sum, Poly.part_mul,map_sum,apply_ite,coeff_mul,mode_coeff, map_zero (coeff k)]
   rw [Finset.sum_comm]; apply sum_congr rfl; intro i _; rw [Finset.sum_comm]
   apply sum_congr rfl; intro j _; split <;> simp
lemma mode_shift (x : Script R)(k : ℕ)(s : R.Mode) : onMode (X^k*x) s=X^k*onMode x s := by
   ext i; rw [mode_coeff,PowerSeries.coeff_X_pow_mul',PowerSeries.coeff_X_pow_mul']; split; exact (mode_coeff ..).symm
   rfl

/-- Pointwise with O for each r, each mode. -/
def Aims (x : ℝ→Poly R)(f : Script R) := ∀ s : R.Mode, Near (fun t => (x t).part s) (onMode f s)
namespace Aims
variable {x y : ℝ→Poly R}{f g : Script R}
lemma same (h : Aims x f)(H : ∀ s : R.Mode, ∀ᶠ t in Tested.germ, (x t).part s=(y t).part s) : Aims y f := fun i => Near.same (h i) (H i)
lemma uniquely (h : Aims x f)(H : Aims x g) : f=g := by
   ext i s; rw [← mode_coeff,← mode_coeff]; exact congr_arg (fun t => coeff i t) (Near.unique' (h s) (H s))
lemma prime (x : Poly R) : Aims (fun _ => x) (C x) := by intro s; rw [mode_atom]; exact Near.fixed _
lemma nothing : Aims (R:=R) 0 0 := by have h:= prime (R:=R) 0; rw [map_zero] at h; exact h
lemma unit : Aims (R:=R) 1 1 := by have h:= prime (R:=R) 1; rw [map_one] at h; exact h
lemma ups (h : Aims x f)(H : Aims y g) : Aims (x+y) (f+g) := by
  intro s
  rw [show onMode (f+g) s= onMode f s+onMode g s from PowerSeries.ext fun i => by simp only [map_add,mode_coeff,Poly.part_plus]]
  exact Near.incline (h s) (H s)
lemma neg (h : Aims x f) : Aims (-x) (-f) := by
   intro s
   rw [show onMode (-f) s= -onMode f s from PowerSeries.ext fun i => by simp only [map_neg,mode_coeff,Poly.part_neg]]
   simp_rw [Pi.neg_apply,Poly.part_neg]; exact Near.down (h s)
lemma sub (h : Aims x f)(H : Aims y g) : Aims (x-y) (f-g) := by simp_rw [sub_eq_add_neg];exact h.ups H.neg
lemma sums {I : Type*} (s : Finset I)(f : I→ℝ→Poly R)(x : I→Script R)(h : ∀ i∈s,Aims (f i) (x i)) :
    Aims (∑ i∈s,f i) (∑ i∈s,x i) := by
   induction s using Finset.induction_on with
   | empty => rw [sum_empty,sum_empty]; exact nothing
   | insert i s hi ih => rw [sum_insert hi,sum_insert hi]; exact (h i (mem_insert_self ..)).ups (ih (fun j hj => h j (mem_insert_of_mem hj)))
lemma product (h : Aims x f)(H : Aims y g) : Aims (x*y) (f*g) := by
   intro s; rw [mode_product]; simp_rw [Pi.mul_apply,Poly.part_mul]
   apply Near.terms_at (x:=fun i t=>∑ j:R.Mode, if Poly.merges i j s then (x t).part i*(y t).part j else 0)
   intro i _
   apply Near.terms_at (x:=fun j t=> if Poly.merges i j s then _ else 0)
   intro j _; split; exact Near.mult (h i) (H j)
   have hb := Near.fixed (0:ℂ); rw [map_zero] at hb; exact hb
lemma highs (h : Aims x f)(k : ℕ) : Aims (x^k) (f^k) := by induction k with
  | zero => rw [pow_zero,pow_zero]; exact unit
  | succ k ih => rw [pow_succ,pow_succ]; exact ih.product h
lemma scaler (h : Aims x f)(c : ℂ) : Aims (c • x) (c • f) := by
   intro s
   rw [show onMode (c • f) s=(C c)*(onMode f s) from PowerSeries.ext fun i => by rw [mode_coeff,coeff_smul,Poly.part_smul,PowerSeries.coeff_C_mul,mode_coeff]]
   exact Near.scaled (h s) _
lemma real_shift (h : Aims x f)(k : ℕ) : Aims (fun t => (t^k:ℝ) • x t) (X^k*f) := by
   intro s; rw [mode_shift]; convert Near.promote (h s) k using 1
   funext t; exact rfl
lemma divide_shift {k : ℕ}(h : Aims (fun t=> (t^k:ℝ) • x t) (X^k*f)) : Aims x f := by
   intro s
   apply Near.priced (k:=k); convert h s using 1
   · funext t; exact rfl
   exact (mode_shift ..).symm
lemma vacuum {l : ℝ→ℂ}{x : PowerSeries ℂ}(h : Near l x) :
    Aims (fun t => Poly.bead R (l t)) (scalar R x) := by
   intro s; simp_rw [mode_scalar,Poly.bead,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk,Poly.part_send]; split
   exact h
   have h:= Near.fixed (0:ℂ); rw [map_zero] at h; exact h
lemma vac (h : Aims x f) : Near (fun t => (x t).part R.quiet) (den f) := (mode_one f) ▸ h R.quiet
lemma nonvanishing (h : Aims x f)(H : basepoint f≠0) : ∀ᶠ t in Tested.germ, (x t).part R.quiet≠0 :=
   (Aspiration.tendsto_first (h R.quiet)).eventually (isOpen_compl_singleton.mem_nhds (show (coeff 0 (onMode f R.quiet)) ∈ ({0}:Set ℂ)ᶜ from by rw [mode_coeff, ← basepoint_read]; exact H))

lemma divide (h : Aims x f)(H : basepoint f≠0) : Aims (Evaluation.divideAway ∘ x) (Grade.quotient f) := by
   let g:= fun t => (x t).part R.quiet
   have hi : Near g (den f) := h.vac
   have hn := vacuum (R:=R) (Near.fine_inverse hi (by rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact H));
   apply (hn.product h).same
   intro i; exact Filter.Eventually.of_forall fun t => by
     change (Poly.bead R _ * x t).part i=_; rw [Poly.product_bead]; rfl

private lemma den_lift (h : Aims x f)(H : ∀ᶠ t in Tested.germ, (x t).part R.quiet=0) :
    den f=0 := by
   have he : Near (fun _ => (0:ℂ)) 0 := by
      have hh := Near.fixed (0:ℂ); rw [map_zero] at hh; exact hh
   exact Near.unique' (Near.same h.vac H) he
variable [Fintype V]
lemma exponential_read (h : Aims x f)(H : ∀ᶠ t in Tested.germ, (x t).part R.quiet=0) :
    Aims (fun t => Poly.pass (x t)) (Grade.exponential f) := by
  rw [Evaluation.only_marked (h.den_lift H)]
  apply (sums (f:=fun i : ℕ => (i.factorial:ℂ)⁻¹ • x^i) _ _ (fun i _=> (h.highs i).scaler _)).same
  intro i; exact Filter.Eventually.of_forall fun j => by simp only [Finset.sum_apply,Pi.smul_apply,Pi.pow_apply]; rfl
lemma after (h : Aims x f) (hx : ∀ᶠ t in Tested.germ, (x t).part R.quiet=1)(H : Grade.den f=1) :
    Aims (fun t=>connected (x t)) (Grade.logarithm f) := by
   rw [Evaluation.source_log H]
   apply (sums _ _ _ (fun i _=> ((h.sub unit).highs (i+1)).scaler (((-1:ℂ)^i)/(i+1:ℂ)))).same
   intro s
   filter_upwards [hx] with t ht; rw [connected_eq_logTable ht];
   simp only [Finset.sum_apply,Pi.smul_apply,Pi.pow_apply,Pi.sub_apply,Pi.one_apply]; rfl
/-- Conditional logarithm at the actual values on this ray. -/
theorem extracted (h : Aims x f)(H : basepoint f≠0) : Aims (fun t=>connected (Evaluation.divideAway (x t)))
    (Grade.logarithm (Grade.quotient f)) := by
   refine (h.divide H).after ?_ (Grade.den_quotient H)
   filter_upwards [h.nonvanishing H] with t ht; exact Evaluation.remains_one ht

end Aims
end YM.RG02.Asym
