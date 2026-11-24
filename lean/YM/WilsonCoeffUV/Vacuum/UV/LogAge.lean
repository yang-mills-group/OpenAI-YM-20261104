import YM.WilsonCoeffUV.Vacuum.Step.Instantiation
/-!
# Staggered log-age charge

Use a shifted polynomial of the age as a supersolution and keep the same
positive power exponent `1/4` through *all* strict arrows. Charges at skipped
step enlargement L and fine-end TOP explicitly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free Real
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{n N M m k r b j:ℕ}

structure Credit where
  d : ℕ
  x : ℝ
  good : 1≤ x
namespace Credit
def buy (T:Credit)(y:ℝ):= T.x*y^T.d
variable {T V : Credit} {y z a γ κ:ℝ}
lemma purchase (T:Credit)(h:1≤ y): 1≤T.buy y:= one_le_mul_of_one_le_of_one_le T.good (one_le_pow₀ h)
lemma elder (T:Credit)(h:1≤ y)(g:y≤ z) : T.buy y≤ T.buy z:= mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) g _) (by linarith [T.good])
def plus (T V:Credit) :Credit := ⟨T.d+V.d,T.x+V.x,by linarith [T.good,V.good]⟩
def unit : Credit:=⟨0,1,le_rfl⟩
def leanC : Credit:= ⟨1,1,le_rfl⟩
@[simp] lemma unit_cost (x:ℝ): unit.buy x=1:=by simp [unit,buy]
@[simp] lemma lean_cost (x:ℝ): leanC.buy x=x:=by simp [leanC,buy]
lemma fuel (T V:Credit)(h:1≤y): T.buy y+V.buy y≤ (T.plus V).buy y:= by
   unfold buy plus; dsimp; rw [add_mul]; exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h (by omega)) (zero_le_one.trans T.good)) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h (by omega)) (zero_le_one.trans V.good))
lemma thickens (V:Credit)(h:1≤y): T.buy y≤ (T.plus V).buy y:= (le_add_of_nonneg_right (le_trans zero_le_one (purchase V h))).trans (fuel _ _ h)
lemma thickened (T:Credit)(h:1≤y): V.buy y≤ (T.plus V).buy y:= (le_add_of_nonneg_left (le_trans zero_le_one (purchase T h))).trans (fuel _ _ h)
def prodC (T V:Credit):Credit:=⟨T.d+V.d,T.x*V.x,one_le_mul_of_one_le_of_one_le T.good V.good⟩
def powC (T:Credit)(j:ℕ):Credit:=⟨T.d*j,T.x^j,one_le_pow₀ T.good⟩
lemma power (T:Credit)(y:ℝ)(j:ℕ): (T.powC j).buy y=(T.buy y)^j:=by unfold buy powC; dsimp; rw [pow_mul,mul_pow]
lemma products (T V:Credit)(y:ℝ): (T.prodC V).buy y=T.buy y*V.buy y:=by unfold prodC buy; simp [pow_add]; ring
def usingC (T V:Credit): Credit:=⟨V.d*T.d,T.x * V.x^T.d,one_le_mul_of_one_le_of_one_le T.good (one_le_pow₀ V.good)⟩
lemma stock_up (T V:Credit)(y:ℝ): (T.usingC V).buy y=T.buy (V.buy y):=by simp [buy,usingC,pow_mul]; ring

-- super poly
private def cushion (T:Credit):ℝ:= ((T.d:ℝ)+1)*8
private lemma cp (T:Credit): 0 < cushion T:=by unfold cushion; positivity
def tower (T:Credit) (a y:ℝ):ℝ:= a*T.buy (y+cushion T)
lemma raised (T:Credit)(a y:ℝ)(h:1≤a)(e:1≤y): T.buy y≤T.tower a y:= (T.elder e (le_add_of_nonneg_right (cp T).le)).trans (le_mul_of_one_le_left (by have hh:= T.purchase (show 1≤y+cushion T from e.trans (le_add_of_nonneg_right (cp T).le)); linarith) h)
def finances (T:Credit)(a:ℝ)(h:1≤a):Credit:= ⟨T.d, a*T.x*(1+cushion T)^T.d, one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h T.good) (one_le_pow₀ (le_add_of_nonneg_right (cp T).le))⟩
lemma donation (T:Credit)(a:ℝ)(h:1≤a)(y:ℝ)(e:1≤y): T.tower a y ≤ (T.finances a h).buy y:= by
   have hg : y+cushion T ≤ (1+cushion T)*y:= by have H:= cp T; nlinarith
   have hp : 1≤y+cushion T:= e.trans (le_add_of_nonneg_right (cp T).le)
   refine (mul_le_mul_of_nonneg_left (T.elder hp hg) (zero_le_one.trans h)).trans_eq ?_; simp only [finances,buy,mul_pow]; ring
private lemma swelling_aux (T:Credit) (he:1≤ y)(h:1≤ z)(g:y≤z+γ)(p:0≤ γ): T.buy (y+cushion T)≤T.buy (z+cushion T)*Real.exp (γ/8):= by
   let b:ℝ:=z+cushion T
   let C:= cushion T
   have hC:0<C:=cp T; have hb:1≤ b:=le_trans h (le_add_of_nonneg_right hC.le)
   have hy:1≤ y+C:= he.trans (le_add_of_nonneg_right hC.le)
   have hu:y+C≤ b* Real.exp (γ/C):=by
     have hf:y+C≤b+γ:=by unfold b C; linarith
     refine hf.trans ?_; have hh: b* (γ/C+1)≤ b*Real.exp (γ/C) := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (zero_le_one.trans hb); refine le_trans ?_ hh
     rw [mul_add,mul_one]; have hm:γ≤ b*(γ/C):=by
       rw [← mul_div_assoc, le_div_iff₀ hC]; have ht:b≥C:= by unfold b C; linarith
       nlinarith
     linarith
   refine (T.elder hy hu).trans ?_
   rw [show z+cushion T=b from rfl]; unfold buy; rw [mul_pow]

   calc
    _ = T.buy b * Real.exp (T.d*(γ/C)) := by unfold buy; rw [Real.exp_nat_mul]; ring
    _ ≤ T.buy b * Real.exp (γ/8) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by rw [← mul_div_assoc,div_le_iff₀ hC]; unfold C cushion; nlinarith only [p])) (zero_le_one.trans (T.purchase hb))
lemma swell (T:Credit)(he:1≤a)(h:1≤y)(hp:1≤z)(hv:z≤y+γ)(p:0≤γ): T.tower a z ≤ T.tower a y * Real.exp (γ/8):= by unfold tower; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (swelling_aux _ hp h hv p) (by linarith)
lemma rag_fee (T:Credit)(h:1≤ y)(hp:1≤z)(hv:z≤y+γ)(p:0≤γ): T.buy z * Real.exp (-γ/2) ≤ (T.finances 1 le_rfl).buy y * Real.exp (-γ/4):= by
    calc
     _ ≤ (T.tower 1 y * Real.exp (γ/8)) * Real.exp (-γ/2) := mul_le_mul_of_nonneg_right (le_trans (T.raised 1 z le_rfl hp) (T.swell le_rfl h hp hv p)) (by positivity)
     _ ≤ _ := by
       rw [mul_assoc,← Real.exp_add]; exact mul_le_mul (donation _ _ _ _ h) (Real.exp_le_exp.mpr (by linarith)) (by positivity) (zero_le_one.trans (purchase _ h))

def taxR : ℝ:= Real.exp (-Real.log 3 /8)
lemma tax_pos : 0<taxR:=by unfold taxR; positivity
lemma tax_lt : taxR<1:= by have h : 0<Real.log 3:= Real.log_pos (by norm_num); unfold taxR; rw [Real.exp_lt_one_iff]; linarith
def liftA : ℝ:= (1-taxR)⁻¹
lemma lift_good:1≤liftA:=by unfold liftA; rw [one_le_inv₀ (sub_pos.mpr tax_lt)]; linarith [tax_pos]
abbrev behind (T:Credit): Credit:= T.finances liftA lift_good
lemma ceiling (T:Credit)(h:1≤y): taxR*T.tower liftA y + T.buy y ≤ T.tower liftA y:=by
   unfold tower liftA
   have he : T.buy y ≤ T.buy (y+cushion T):= T.elder h (le_add_of_nonneg_right (cp T).le)
   refine (add_le_add_right he _).trans_eq ?_; have hv:= (sub_pos.mpr tax_lt).ne'; field_simp; ring
lemma step_cap (T:Credit)(h:1≤y)(hp:1≤ z)(hv:z ≤ y+γ)(p:Real.log 3≤γ): Real.exp (-γ/4)*T.tower liftA z + T.buy y ≤ T.tower liftA y:=by
    have hy : 0≤ γ:= (Real.log_nonneg (by norm_num)).trans p
    have hz : Real.exp (-γ/4)*T.tower liftA z ≤ taxR*T.tower liftA y:= calc
      _ ≤ Real.exp (-γ/4)*(T.tower liftA y*Real.exp (γ/8)) := mul_le_mul_of_nonneg_left (swell _ lift_good h hp hv hy) (by positivity)
      _ = Real.exp (-γ/4+γ/8)*T.tower liftA y:=by rw [Real.exp_add]; ring
      _ ≤ _:=by
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (zero_le_one.trans ((purchase T h).trans (T.raised liftA y lift_good h)))
    exact (add_le_add_left hz _).trans (ceiling _ h)
end Credit

namespace PathCost
variable (S:Schedule)

def arc (m:ℕ):ℝ:=S.scale (m+1)-S.scale m
lemma arch (m:ℕ) : arc S m=Real.log (S.block m).val:= by rw [arc,S.scale_succ]; ring
lemma arch_pos (m:ℕ): Real.log 3 ≤ arc S m:= by rw [arch]; exact Real.log_le_log (by norm_num) (by exact_mod_cast S.block_large m)
lemma arc_nn (m:ℕ):0≤arc S m:= (Real.log_nonneg (by norm_num)).trans (arch_pos ..)
lemma scales : Monotone S.scale:= monotone_nat_of_le_succ (fun n=> sub_nonneg.mp (arc_nn S n))

def trailC (m n:ℕ) : ℝ:= Real.exp (-(S.scale n-S.scale m)/4)
lemma trail_pos (m n): 0< trailC S m n:=Real.exp_pos _
lemma fade (m:ℕ) : Tendsto (trailC S m) atTop (𝓝 0):=by
   apply Real.tendsto_exp_atBot.comp
   exact Tendsto.atBot_div_const (by norm_num) (tendsto_neg_atTop_atBot.comp (S.divergent.atTop_add (tendsto_const_nhds (x := -S.scale m))))
lemma trail_ratio (m n) : trailC S m n=(S.a n / S.a m)^((4:ℝ)⁻¹):=by
   unfold trailC Schedule.scale; rw [Real.rpow_def_of_pos (div_pos (S.a_pos _) (S.a_pos _)),Real.log_div (S.a_pos _).ne' (S.a_pos _).ne',Real.log_inv,Real.log_inv]; congr 1; ring
lemma one_leg (m b:ℕ): trailC S m b=Real.exp (-(arc S m)/4)*trailC S (m+1) b:=by unfold trailC arc; rw [← Real.exp_add]; congr 1; ring
lemma skipping (m b:ℕ):trailC S (m+1) b≤ (S.block m).val*trailC S m b:=by
   have hy: exp (arc S m)=(S.block m).val:=by rw [arch,Real.exp_log]; positivity
   rw [one_leg S m, ←mul_assoc,←hy, ←Real.exp_add]; apply le_mul_of_one_le_left (trail_pos ..).le
   apply Real.one_le_exp; linarith [arc_nn S m]
lemma trail_end (m:ℕ): trailC S m m=1:= by rw [trailC,sub_self,neg_zero, zero_div,Real.exp_zero]
lemma narrow (h:m≤ n)(b:ℕ): trailC S m b≤ trailC S n b:= Real.exp_le_exp.mpr (by linarith [scales S h])
lemma rag_rep (m b:ℕ): Real.sqrt (S.a b/S.a m)=Real.exp (-(S.scale b-S.scale m)/2):=by
  rw [Real.sqrt_eq_rpow]; unfold Schedule.scale; rw [Real.rpow_def_of_pos (div_pos (S.a_pos _) (S.a_pos _)), Real.log_div (S.a_pos _).ne' (S.a_pos _).ne',Real.log_inv,Real.log_inv]; congr 1; ring
end PathCost
end YM.WilsonCoeffUV.Bank
