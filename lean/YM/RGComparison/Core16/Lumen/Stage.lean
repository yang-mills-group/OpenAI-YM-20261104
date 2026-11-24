import YM.RGComparison.Core16.Lumen.Echo

/-!
# Uniform-pressure estimates accounting across families
Not uniform functions of a scaling sequence: holds pointwise all x ≥ fixed gate AND before any
region choice. Dates may be delayed but never depend on point data. Ordinary finite polynomials in
`dollar s` with s=-log physical running g. supplying coefficient bound itself required
(even if tested expression includes `log power`). This module's estimator is only for NONEMPTY
conditional gas test horizon, i.e. after backing to finite local WilsonX call and before purchasing
mounting-horizon debts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Push.Uniform Forge
open PertExtension PertExtension.Series Tested Radial
open Finset
open scoped Topology ContDiff BigOperators Classical

abbrev Cost := ℝ→ℝ
abbrev Script := ℕ→ℝ
def untilB (c:Script)(r:ℕ)(g:ℝ):= ∑ i∈ Finset.range r,g^i*c i
structure Stage where
   L:ℝ
   p:ℕ
   high : 1≤L
namespace Stage
variable (T:Stage)

structure Above (U T:Stage):Prop where
    gate: T.L ≤ U.L
    power : T.p≤ U.p

def rate (c:ℝ)(x:ℝ)(r:ℕ):= x^T.p*dollar x^r*c
structure Ticket (r : ℕ) (c:ℝ)(f:Cost):Prop where
    pos: 0≤c
    budgets : ∃ y: Script,(∀ i<r,|y i| ≤ c) ∧ ∀ x:ℝ,T.L≤x→ |f x-untilB y r (dollar x)| ≤ T.rate c x r

variable {T}
lemma now {x:ℝ}(h:T.L≤x):0<x:=lt_of_lt_of_le zero_lt_one (T.high.trans h)
variable {r s :ℕ} {x c d:ℝ} {g f:Cost}
lemma rate_fair (hc:T.L≤x)(h:c≤d): T.rate c x r ≤ T.rate d x r:=mul_le_mul_of_nonneg_left h (mul_nonneg (pow_nonneg (now hc|>.le) _) (pow_nonneg (dollar_pos _|>.le) _))
lemma rate_ge (hc:T.L≤x)(h:0≤d) : 0≤ T.rate d x r:= by apply le_trans (rate_fair (r:=r) hc h|>.trans' ?_) (le_refl _); simp [rate]
namespace Ticket
variable (A:T.Ticket r c f)
include A
lemma promote (h:c≤d) : T.Ticket r d f :=
    ⟨A.pos.trans h, A.budgets.imp (fun _ H=> ⟨fun i hi=>(H.1 i hi).trans h,fun i hi=>(H.2 i hi).trans (rate_fair hi h)⟩)⟩
lemma extend {U:Stage} (h:U.Above T) : U.Ticket r c f:=by
   have hz:=A.pos
   refine ⟨hz,A.budgets.imp (fun y H=>⟨H.1,fun i hi=>(H.2 i (h.gate.trans hi)).trans ?_⟩)⟩; unfold rate; have hx:= dollar_pos i; gcongr; exact U.high.trans hi; exact h.power
lemma reload {g:Cost}(he:∀x,T.L≤x→f x=g x):T.Ticket r c g:= ⟨A.pos,A.budgets.imp (fun _ hh=>⟨hh.1,fun x hx=> by rw [←he x hx]; exact hh.2 x hx⟩)⟩
lemma more (B:T.Ticket r d g): T.Ticket r (c+d) (fun x=>f x+g x):=by
   obtain ⟨y,hy,he⟩:=A.budgets; obtain ⟨v,hv,ht⟩:=B.budgets
   refine ⟨add_nonneg A.pos B.pos,y+v,fun i h=>(abs_add_le ..).trans (add_le_add (hy i h) (hv i h)),fun x hx=>?_⟩
   let u:= dollar x; unfold untilB; simp only [Pi.add_apply,mul_add,sum_add_distrib]; change |f x+ g x-(untilB y r u+untilB v r u)| ≤ _; rw [add_sub_add_comm]; exact (abs_add_le ..).trans ((add_le_add (he x hx) (ht x hx)).trans_eq (mul_add ..).symm)
lemma scales (z:ℝ) : T.Ticket r (|z| * c) (z*f ·):= by
   obtain ⟨y,hy,he⟩:=A.budgets; refine ⟨mul_nonneg (abs_nonneg z) A.pos, fun i=>z*y i, fun i hi=>?_,fun x hx=>?_⟩
   · dsimp only; rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hy _ hi) (abs_nonneg z)
   unfold untilB; simp only [mul_left_comm _ z,← mul_sum]; rw [← mul_sub,abs_mul]; exact ((mul_le_mul_of_nonneg_left (he x hx) (abs_nonneg z)).trans_eq (mul_left_comm ..))

omit A in
private lemma blend (z:ℝ) (y:Script)  : untilB (fun i=> match i with|0=>0|j+1=>y j) (r+1) z=z*untilB y r z:=by
   unfold untilB; rw [Finset.sum_range_succ',mul_sum]; simp_rw [pow_succ']; simp only [mul_zero,add_zero]
   exact sum_congr rfl fun i _=> mul_assoc ..

lemma lent : T.Ticket (r+1) c (fun x=> dollar x*f x) := by
    obtain ⟨y,hy,h⟩:= A.budgets; have hv:= A.pos; let w (i:ℕ):= match i with| 0=> (0:ℝ)| i+1=>y i
    refine ⟨hv,w,?_,fun i hi=> ?_⟩
    · rintro (_|i) h
      · unfold w; rw [abs_zero]; exact hv
      exact hy i (by omega)
    let z:= dollar i; have hz: 0< z:=dollar_pos _
    change |z*f i-untilB w _ z|≤_; rw [blend z y,← mul_sub,abs_mul,abs_of_pos hz]
    unfold rate; rw [pow_succ (dollar i)]; exact (mul_le_mul_of_nonneg_left (h i hi) hz.le |>.trans_eq (by unfold z rate; ring))
lemma engage (m:ℕ) : T.Ticket (r+m) c (fun x=> dollar x^m*f x):= by
    induction m with
    | zero => simpa [pow_zero] using A
    | succ m IH=> simpa only [pow_succ',mul_assoc,add_assoc] using IH.lent

omit A in
private lemma remove₁ {r:ℕ}(z:ℝ) (y:Script): untilB y (r+1) z=untilB y r z+z^r*y r:= Finset.sum_range_succ ..
omit A in
lemma lower_degree (A:T.Ticket (r+1) c f):T.Ticket r (2*c) f:=by
   have hc:=A.pos; obtain ⟨y,hy,h⟩:=A.budgets; refine ⟨by positivity,y,fun i hi=> (hy i (by omega)).trans (by linarith),fun i hi=>?_⟩
   let z:= dollar i; have hx:1 ≤ i:=T.high.trans hi; have hz:= (dollar_pos i).le; change |f i-untilB y _ z|≤_
   apply (abs_sub_le (f i) (untilB y (r+1) z) (untilB y r z)).trans (add_le_add (h i hi) ?_|>.trans_eq (?_ : T.rate c i (r+1)+ (T.rate (2*c) i r - T.rate c i (r+1))=_)) -- cost left
   · rw [remove₁,add_sub_cancel_left,abs_mul,abs_of_nonneg (pow_nonneg hz _)]; unfold rate; rw [pow_succ (dollar i)]; refine (mul_le_mul_of_nonneg_left (hy r (lt_add_one r)) (pow_nonneg hz _)).trans ?_
     let A:= i^T.p; have hK : 1≤A :=one_le_pow₀ hx; have hZ: z≤1:= dollar_bound (now hi|>.le); change _≤ A*z^_* _-A*(z^_*z)*c
     nlinarith only [mul_nonneg (pow_nonneg hz r) hc, mul_nonneg (by linarith only [hK]:0≤ A-1) (mul_nonneg (pow_nonneg hz r) hc), mul_le_mul_of_nonneg_right hZ (show 0≤ A*z^r*c from mul_nonneg (by unfold z; positivity) hc)]
   abel
lemma reduce (hs:s≤r) : T.Ticket s (2^(r-s)*c) f:=by
   induction r,hs using Nat.le_induction generalizing c with
   | base=>simpa using A
   | succ k hk IH=>
      have he:= IH (c:=2*c) (lower_degree (A:=A)); rw [Nat.succ_sub hk,pow_succ,mul_assoc]; exact he
end Ticket

variable (T r)
lemma free (c:ℝ)(hc:0≤c)(z : Cost)(h:∀ x,T.L≤x→|z x|≤ T.rate c x r): T.Ticket r c z:=by
    refine ⟨hc,0,fun i _=>(by simpa),fun x hx=>by simpa [untilB] using h x hx⟩
lemma ticket_zero : T.Ticket r 0 0:=free T r _ (le_refl _) _ fun x hx=>by simp [rate]
lemma flat (a:ℝ) : T.Ticket r |a| (fun _=>a):=by
     cases r with
     | zero=> apply free _ _ _ (abs_nonneg _); intro x hx; unfold rate; simp only [pow_zero,mul_one]; exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ (T.high.trans hx))
     | succ r=>
         refine ⟨abs_nonneg _,fun i=> if i=0 then a else 0,fun i _=>?_,fun x hx=>?_⟩
         · dsimp only; split; rfl; simp
         unfold untilB; rw [sum_range_succ']; simpa using rate_ge (r:=r+1) hx (abs_nonneg a)
lemma ticket_sum {α:Type*}(I: Finset α)(f:α→Cost)(c:α→ℝ)(h:∀i∈I,T.Ticket r (c i) (f i)): T.Ticket r (∑ i∈I,c i) (fun x=>∑ i∈I,f i x):= by
    induction I using Finset.induction_on with
    | empty=> simp only [sum_empty]; exact ticket_zero ..
    | insert i I hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (mem_insert_self ..)).more (ih (fun j hj=> h j (mem_insert_of_mem hj)))
end Stage
end YM.RGComparison.Core16.Lumen
