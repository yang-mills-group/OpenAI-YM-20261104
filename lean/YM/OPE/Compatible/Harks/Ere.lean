import YM.OPE.Compatible.Broma.Wage
/-!
# Exponential dichotomy with phase filtration. Prelim.# T-variation
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {E F M:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F] {r x b c t q:ℝ}
local notation "A!"=> (E→L[ℝ] E)
variable {a f:ℕ→ E}{g:ℕ→ F}{p:ℕ→ E→L[ℝ] E}
def Hex {E:Type}[NormedAddCommGroup E](r:ℝ)(a:ℕ→ E)(b:ℝ):Prop:=∀ i:ℕ,‖a i‖≤b*r^i
section
omit [NormedSpace ℝ E]
lemma Hex.price (h:Hex r a b) :0≤b:=by simpa only [pow_zero,mul_one] using (norm_nonneg _|>.trans (h 0)) -- parse
lemma Hex.add {f g:ℕ→ E}(hp:Hex r f b)(hx:Hex r g c):Hex r (f+g) (b+c):=by intro i; rw [Pi.add_apply,add_mul]; exact (norm_add_le ..).trans (add_le_add (hp i) (hx i))
lemma Hex.sub (hp:Hex r f b)(hx:Hex r a c):Hex r (f-a) (b+c):=by intro i; rw [Pi.sub_apply,add_mul]; exact (norm_sub_le ..).trans (add_le_add (hp i) (hx i))
lemma Hex.zero (E:Type)[NormedAddCommGroup E](r:ℝ) : Hex r (0:ℕ→E) 0:=by intro i; simp
lemma Hex.tips (hp:Hex r f b)(ht:0≤r)(h:b≤c):Hex r f c:=fun i=>(hp i).trans (mul_le_mul_of_nonneg_right h (pow_nonneg ht _))
lemma Hex.warm (hp:Hex r f b)(ht:0≤r)(h:r≤q):Hex q f b:=fun i=>(hp i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht h _) hp.price)
lemma Hex.forward (hp:Hex r f b):Hex r (fun i=> f (i+1)) (b*r):=by intro i; rw [mul_assoc,← pow_succ']; exact hp _
end
lemma Hex.invoke (T:E→L[ℝ] F)(hp:Hex r f b): Hex r (fun i=> T (f i)) (‖T‖*b):=by intro i; rw [mul_assoc]; exact (le_opNorm ..|>.trans (mul_le_mul_of_nonneg_left (hp i) (norm_nonneg _)))
lemma Hex.tint (hp:Hex r f b)(T:ℝ):Hex r (T • f) (‖T‖*b):=by intro i; rw [Pi.smul_apply,norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (hp i) (norm_nonneg _)
lemma Hex.acts (hp:Hex r f b)(hq:Hex x p c):Hex (r*x) (fun i=>p i (f i)) (b*c):=by intro i; refine (le_opNorm ..).trans ((mul_le_mul (hq i) (hp i) (norm_nonneg _) ((norm_nonneg _).trans (hq i))).trans_eq ?_); rw [mul_pow]; ring
lemma Hex.pays (hp:Hex r f b)(T:ℕ→ E→L[ℝ] F)(ht:∀ i, ‖T i‖≤x): Hex r (fun i=> T i (f i)) (x*b):=by intro i; rw [mul_assoc]; exact (le_opNorm ..).trans (mul_le_mul (ht i) (hp i) (norm_nonneg _) ((norm_nonneg _).trans (ht i)))
def Run (p: ℕ→ A!)(a f:ℕ→ E):Prop:=∀ n, a (n+1)= p n (a n)+ f n
def race (p:ℕ→ A!)(f:ℕ→ E)(v:E): ℕ→E
   | 0=>v
   | i+1=> p i (race p f v i)+ f i
lemma gait (P:ℕ→ A!)(f:ℕ→ E)(y:E): Run P (race P f y) f:=fun _=>rfl
lemma Run.isRace (hp:Run p a f): a=race p f (a 0):=by ext i; induction i with | zero=>rfl| succ j ih=> rw [hp,ih];rfl
lemma Run.agrees {a b f:ℕ→ E}{P:ℕ→ A!}(h:Run P a f)(hp:Run P b f)(hx:a 0=b 0):a=b:=h.isRace.trans ((congrArg (race P f) hx).trans hp.isRace.symm)
lemma Run.add {a b f g:ℕ→ E}(h:Run p a f)(hp:Run p b g):Run p (a+b) (f+g):=fun i=> by rw [Pi.add_apply, Pi.add_apply,Pi.add_apply,h,hp,map_add]; abel
lemma Run.sub {a b f g:ℕ→ E}(h:Run p a f)(hp:Run p b g):Run p (a-b) (f-g):=fun i=>by rw [Pi.sub_apply, Pi.sub_apply,Pi.sub_apply,h,hp,map_sub]; abel
lemma propel (P:ℕ→ A!)(v:E):Run P (race P 0 v) 0:= gait P 0 v
lemma Run.gap (ht:q<r) (w:ℝ)(hw:0≤q)(hz: x/(r-q) ≤ w)(hx: Hex r f x)(hp:Run p a f)(hh: ∀ i,‖p i (a i)‖ ≤ q*‖a i‖) (h0:‖a 0‖≤w): Hex r a w:=by
     intro i; have he:0≤r:=hw.trans ht.le; induction i with
     | zero=> simpa using h0
     | succ i ih=> rw [hp]; refine le_trans ((norm_add_le ..).trans (add_le_add ((hh i).trans (mul_le_mul_of_nonneg_left ih hw)) (hx i))) ?_; have ht:= mul_le_mul_of_nonneg_right ((div_le_iff₀ (by linarith : 0< r-q)).1 hz) (pow_nonneg he i); rw [pow_succ]; nlinarith only [ht]
-- missing grade issue Solve for scalar >r by Neumann
end YM.OPE.Hark
