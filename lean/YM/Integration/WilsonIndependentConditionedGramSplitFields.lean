import YM.Integration.WilsonIndependentConditionedGramSplitAward

/-! Only the high thermal remainder can use a third source payment. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramSplitFields
open WilsonIndependentConditionedGramSplitAward (homeLow homeHigh)
local notation "J" => Fin 2

theorem original (q:ℕ)(U inv V β:ℝ)(P H D:J→ℝ)(E:J→ℕ)
    (up:0 ≤ U)(ip:0 ≤ inv)(vp:0 ≤ V)(base:1 ≤ β)(reports:∀i,0 ≤ P i)(start:∀i,0 ≤ H i)
    (offer:∀i,H i ≤ D i*β^(E i)):
    homeLow q U inv H ≤ homeLow q U inv D*β^(E 0+E 1) ∧
    homeHigh q U P H V ≤ homeHigh q U P D V*β^(E 0+E 1+max (E 0) (E 1)):=by
  let n:=E 0+E 1
  let m:=max (E 0) (E 1)
  let prod:=fun (h:J→ℝ)=>(1+h 0)*(1+h 1)
  let fees:=fun (h:J→ℝ)(i:J)=>P i*h i
  have bp:=zero_lt_one.trans_le base
  have Dp (i:J):0 ≤ D i:=nonneg_of_mul_nonneg_left ((start i).trans (offer i)) (pow_pos bp _)
  have ppos (i:J):0 ≤ 1+D i:=by linarith only [Dp i]
  have plus (i:J):1+H i ≤ (1+D i)*β^(E i):=(add_le_add (one_le_pow₀ base) (offer i)).trans_eq (by ring)
  have homes:prod H ≤ prod D*β^n:=by
    calc
      _ ≤ (1+D 0)*β^(E 0)*((1+D 1)*β^(E 1)):=mul_le_mul (plus 0) (plus 1)
        (add_nonneg zero_le_one (start 1)) (mul_nonneg (ppos 0) (pow_nonneg bp.le _))
      _=_:=by dsimp only [prod,n];rw [pow_add];ring
  have priced (i:J):fees H i ≤ fees D i*β^(E i):=by
    calc
      _ ≤ P i*(D i*β^(E i)):=mul_le_mul_of_nonneg_left (offer i) (reports i)
      _=_:=by dsimp only [fees];ring
  have Fpos (i:J):0 ≤ fees D i:=mul_nonneg (reports i) (Dp i)
  have any (i:J)(h:E i ≤ m):fees H i ≤ fees D i*β^m:=
    (priced i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ base h) (Fpos i))
  have first:fees H 0+fees H 1 ≤ (fees D 0+fees D 1)*β^m:=by
    rw [add_mul];exact add_le_add (any 0 (le_max_left ..)) (any 1 (le_max_right ..))
  have both:fees H 0*fees H 1 ≤ fees D 0*fees D 1*β^(n+m):=by
    calc
      _ ≤ (fees D 0*β^(E 0))*(fees D 1*β^(E 1)):=mul_le_mul (priced 0) (priced 1)
        (mul_nonneg (reports 1) (start 1)) (mul_nonneg (Fpos 0) (pow_nonneg bp.le _))
      _=fees D 0*fees D 1*β^n:=by dsimp only [n];rw [pow_add];ring
      _ ≤ _:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ base (Nat.le_add_right _ _)) (mul_nonneg (Fpos 0) (Fpos 1))
  have pre:prod H*(fees H 0+fees H 1) ≤ prod D*(fees D 0+fees D 1)*β^(n+m):=calc
    _ ≤ (prod D*β^n)*((fees D 0+fees D 1)*β^m):=mul_le_mul homes first
      (add_nonneg (mul_nonneg (reports 0) (start 0)) (mul_nonneg (reports 1) (start 1)))
      (mul_nonneg (mul_nonneg (ppos 0) (ppos 1)) (pow_nonneg bp.le _))
    _ = _:=by rw [pow_add];ring
  constructor
  · calc
      _=((q+1:ℕ)*U*inv)*prod H:=by dsimp only [homeLow,prod];ring
      _ ≤ ((q+1:ℕ)*U*inv)*(prod D*β^n):=mul_le_mul_of_nonneg_left homes (by positivity)
      _=_:=by dsimp only [homeLow,prod,n];ring
  · calc
      _=(2*(q+1:ℕ)*U)*(prod H*(fees H 0+fees H 1))+(3*V)*(fees H 0*fees H 1):=by
        dsimp only [homeHigh,prod,fees];ring
      _ ≤ (2*(q+1:ℕ)*U)*(prod D*(fees D 0+fees D 1)*β^(n+m))+(3*V)*(fees D 0*fees D 1*β^(n+m)):=
        add_le_add (mul_le_mul_of_nonneg_left pre (by positivity)) (mul_le_mul_of_nonneg_left both (by positivity))
      _=_:=by dsimp only [homeHigh,prod,fees,n,m];ring

end YM.Integration.WilsonIndependentConditionedGramSplitFields
