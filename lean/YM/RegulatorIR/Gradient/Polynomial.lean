import YM.RegulatorIR.Gradient.Epoch
import Mathlib.Algebra.MvPolynomial.Funext

/-! Equivalence to a scalar-coupling gauge substitution at a fixed order. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Gradient
open Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Train Uniform Diagram Function Finset
open scoped ENNReal Topology BigOperators Classical
variable {X Y:Type} (Γ Ω:Curve X Y)
variable (T:Orders X)
private lemma cut_sym {r s:ℕ} {Γ:Curve X Y} (A:Packet X r) (g:Fin r→ℕ)(h:charge g=s) : IsSym (cut Γ A s g) := by subst s; rw [cut,dif_pos rfl]; exact Packet.is_symmetry _
lemma shiftSym (e r :ℕ) : IsSym (shot Γ T e r) :=by
 unfold shot;apply symmetric_sum ; intro t _; apply symmetric_sum; intro i _; unfold drawn;split
 next h=>
    subst r; unfold updateQ;apply symmetric_sum;intro g h
    have hh:charge g=t.2:= (turns_iff ..).mp h
    exact cut_sym (T t.1 i) g hh
 exact symmetric_zero
variable [Fintype X] [Fintype Y] (ρ:ℕ→ℕ)

def ink (e:ℕ): Jet Y := ∑ i∈Finset.antidiagonal e, PowerSeries.coeff i.2 (alter Γ (packed (T i.1) (ρ i.1)))
lemma drawInk (p s a i:ℕ):
    render (drawn Γ T p s a i)= MvPolynomial.homogeneousComponent i (PowerSeries.coeff s (alter Γ (render (T p a)))):=by
 unfold drawn; rw [← update_formula, MvPolynomial.homogeneousComponent_of_mem (homogen ..)]
 split
 next h=>subst i; rw [if_pos rfl]
 next h=> rw [if_neg (Ne.symm h)]; exact render_zero
omit [Fintype Y] [Fintype X] in
lemma insufficient (p j k:ℕ){n:ℕ}(h: T p j=0) : drawn Γ T p n j k=0:=by
 unfold drawn; split
 next v=>
    subst k; apply Finset.sum_eq_zero (f:=fun g=> cut Γ (T p j) n g)
    intro g hg; unfold cut; split
    next he=> subst n; rw [h,show series Γ g (0:Packet X j)=0 from by ext x;simp [series]]; exact sym_zero
    rfl
 rfl
lemma snapshot (e r:ℕ)(h:∀ i ≤ e,Within (ρ i) (T i)) : render (shot Γ T e r)= MvPolynomial.homogeneousComponent r (ink Γ T ρ e):=by
 unfold ink shot
 rw [map_sum,render_sum]; apply sum_congr rfl; intro p hp; rw [packed,map_sum,map_sum,map_sum,render_sum]
 have hh:= h p.1 (by have hj:= mem_antidiagonal.mp hp; omega)
 simp_rw [← drawInk Γ T p.1 p.2]
 rcases le_total (ρ p.1) r with hx|hx
 · refine (sum_subset (range_mono (by omega)) ?_).symm
   intro v _ hi
   rw [insufficient Γ T _ _ _ (fun_zero hh v hi),render_zero]
 apply sum_subset (range_mono (by omega)); intro v _ hv
 rw [drawn, dif_neg (by rw [mem_range] at hv; omega),render_zero]
where
 fun_zero {p n:ℕ} (H:Within n (T p))(v : ℕ)(h:v∉ range (n+1)): T p v=0 :=by by_contra! h'; exact h (mem_range.mpr (Nat.lt_succ_of_le (H _ h')))

lemma consent (W:Orders X)(e:ℕ)(h:∀ i ≤ e, Within (ρ i) (T i))(hh:∀ i≤e,Within (ρ i) (W i))
    (he:∀ v:Y→ℝ,MvPolynomial.eval v (ink Γ T ρ e)=MvPolynomial.eval v (ink Ω W ρ e)) : shot Γ T e=shot Ω W e:= by
 ext1 i; apply identified _ _ (shiftSym Γ T e i) (shiftSym Ω W e i)
 rw [snapshot Γ T ρ e i h,snapshot Ω W ρ e i hh]; rw [MvPolynomial.funext he]
end YM.RegulatorIR.Gradient
