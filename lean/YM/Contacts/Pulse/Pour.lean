import YM.Contacts.Pulse.Form
/-! finite Wick time connection all-orders -/
set_option autoImplicit false
noncomputable section
namespace YM.Pulse.Form
open Function Filter RG PowerSeries Finset
open scoped Classical BigOperators Topology NNReal
variable {X:Type*}{a b n m:ℕ}
section operators
abbrev Hour (α:Type*) := PowerSeries (Plate α)
abbrev PulseTime (α:Type*) := PowerSeries (Hour α)
variable [Fintype X] (g : X→X→ℝ)
abbrev D (i : X) : Derivation ℝ (PulseTime X) (PulseTime X):= grows (grows (MvPolynomial.pderiv i (R:=ℝ)))
-- instance search? explicit derivative
abbrev clock (X:Type*) : Derivation ℝ (PulseTime X) (PulseTime X) := grows ((d⁄dX (Plate X)).restrictScalars ℝ)
omit [Fintype X] in
lemma tick (f : PulseTime X) (i:ℕ)(u:ℕ) : coeff u (coeff i (clock X f))= (u+1:ℕ) • coeff (u+1) (coeff i f) := by
  rw [clock,grows_coeff,Derivation.restrictScalars_apply,coeff_derivative]; rw [nsmul_eq_mul,Nat.cast_add_one,mul_comm]
lemma lap_at (f : PulseTime X) : linear (linear (lap g)) f= ∑ i: X,∑ j:X,(g i j/2) • D j (D i f):= by
  apply PowerSeries.ext; intro i; apply PowerSeries.ext; intro j
  simp_rw [map_sum,coeff_smul,linear_coeff,D,grows_coeff,lap_apply,MvPolynomial.C_mul']
lemma cross_at (f h: PulseTime X)(i j:ℕ): coeff j (coeff i (∑ a:X, ∑ b:X,(g a b/2) • (D a f * D b h)))=∑ a∈antidiagonal i,∑ b∈antidiagonal j, cross g (coeff b.1 (coeff a.1 f)) (coeff b.2 (coeff a.2 h)):= by
  simp only [map_sum,coeff_smul,coeff_mul,D,grows_coeff,smul_sum,cross_apply,MvPolynomial.C_mul'] -- need final collect
  conv_lhs => arg 2; intro x; rw [sum_comm]
  rw [sum_comm]; apply Finset.sum_congr rfl; intro i hi;
  conv_lhs => arg 2; intro x; rw [sum_comm]
  rw [sum_comm]

variable (F:ℕ→ Rack X)
def sermon (g:X→X→ℝ)(F:ℕ→ Rack X) : PulseTime X:= PowerSeries.mk (fun e=>PowerSeries.mk fun i=>stage e (gathering g F i e))
lemma sermon_zero (h:Snug F): coeff 0 (sermon g F)=0:= by apply PowerSeries.ext; intro n; simp_rw [sermon,coeff_mk,stage, (h.bounded g n).thin 0 _ (Or.inl rfl),verse_quiet]; simp
lemma nonlinear (h:Snug F) : let S:= sermon g F; clock X S=linear (linear (lap g)) S + ∑ i:X,∑ j:X,(g i j/2) • (D i S * D j S):= by
  intro S; apply PowerSeries.ext; intro e; apply PowerSeries.ext; intro n
  rw [map_add,map_add,tick,linear_coeff,linear_coeff,cross_at]; simp only [S,sermon,coeff_mk]; exact staging g h
lemma fire (h:Snug F) : let S:=sermon g F; clock X (breath S)= linear (linear (lap g)) (breath S):=by
   intro S; have hz: coeff 0 S=0:= sermon_zero g F h
   rw [show clock X (breath S)=breath S * clock X S from breath_deriv _ hz, nonlinear g _ h]; simp only [lap_at,mul_add,mul_sum,mul_smul_comm, show ∀ (i:X), D i (breath S)= breath S * D i S from fun i=> breath_deriv _ hz, S, Derivation.leibniz,_root_.smul_eq_mul]
   simp only [smul_add,sum_add_distrib, mul_left_comm]

lemma fuel (h:Snug F) (e i:ℕ) : let S:= breath (sermon g F); (i+1:ℕ) • coeff (i+1) (coeff e S)= lap g (coeff i (coeff e S)):= by intro S; rw [←tick,show clock X S= linear (linear (lap g)) S from fire g F h,linear_coeff,linear_coeff]

def stream (g : X→X→ℝ)(a:Plate X) : ℕ→ Plate X
 | 0=>a
 | i+1=>((i+1:ℕ):ℝ)⁻¹ • lap g (stream g a i)
lemma fireplace (h:Snug F) (i e:ℕ) : let p:= coeff e (breath (sermon g F)); coeff i p= stream g (coeff 0 p) i:= by
  intro p; induction i with
  | zero=>rfl
  | succ i ih=>
    apply nsmul_right_injective (by omega : i+1≠0)
    dsimp only; rw [show (i+1:ℕ) • coeff (i+1) p=_ from fuel g F h _ _,stream, ← Nat.cast_smul_eq_nsmul ℝ,smul_smul, mul_inv_cancel₀ (by exact_mod_cast i.succ_ne_zero),one_smul, ← ih]
end operators
end YM.Pulse.Form
