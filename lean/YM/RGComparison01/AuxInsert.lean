import YM.RGComparison01.AuxSupport

/-! # Reassemble the central vacuum and mark terms (on auxiliary only)
'small real' on the patch, powers of the actual extra E render. No integrating
its exponential outside the ball in Y! That would not give the intended
estimate (Gibbs errors uncontrolled there in that variable).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxFabric
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Lattice Wilson RG Pressure PhysicalNext.Repeat Push.AbsoluteSums
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp Work.G05
open AuxJets AuxCurtain AuxStage WilsonStartup Tensor AuxConstant Matrix
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι:Type} [Fintype ι] [DecidableEq ι]
local notation "Y" => Poll.Body ι
variable {f g W : Poll.Body ι→ℝ×E → ℝ} {Q : Matrix ι ι ℝ} {u v a b d t D D' C M : ℝ} {i j k n w w' q q' : ℕ}
local notation "s" => d*b
local notation "µ" => Poll.sweep Q

def each (i k:ℕ) (W u v : ℝ) := (W*v*2^k)*((u*2^k)^i)*2^k
omit [DecidableEq ι] in
lemma Probe.crew (H : Probe W k w' 0 (d*b) D a a) (hp : Probe f k j (q+1) (d*b) D u u) (hv : Probe g k w q' (d*b) D v v) (hk : n+(q'+q*n) < k) (hi : i ≤ n) : let c:= each i k a u v
    Probe (W*g*f^i) k (w'+w+j*i) (q'+q*i+i) s D c c:= by
  intro c
  have hw : q*i ≤ q*n:=Nat.mul_le_mul_left q hi
  have hB : (q+1)*i=q*i+i:=by rw [Nat.add_mul,Nat.one_mul]
  have hu : q'+q*i+i≤k:=by omega
  have he:= (H.productP hv (by omega)).productP (hp.powP (show (q+1)*i ≤ k+1 by omega)) (by omega)
  simpa only [hB,Nat.zero_add,Nat.add_assoc] using! he
omit [DecidableEq ι] in

-- supply when power moments are paid only at max test order
lemma Probe.tile (H : Probe W k w' 0 (d*b) D a a) (hp : Probe f k j (q+1) (d*b) D u u) (hv : Probe g k w q' (d*b) D v v) (hk : n+(q'+q*n) < k) (hi : i ≤ n) : let c:= each i k a u v
    Probe (W*g*f^i) k (w'+w+j*n) (q'+q*i) s D c c:= by
  have ht:=H.crew hp hv hk hi
  exact ht.raise le_rfl le_rfl (by gcongr) (by omega)

def numeric (b : ℝ) (W g : Y→ℝ×E→ℝ) (f:Y→ℝ×E→ℝ) (q q' : ℕ) (φ:ℝ→ℝ) : Y→ℝ×E→ℝ:=
    W*((b⁻¹^q') • g)*(fun z y=> φ ((b⁻¹^q • f) z y))
-- estimates on the exponential remainder
abbrev bite (C d : ℝ) (q:ℕ):= C*d^(q+1)+2
local notation "U" => numeric b W g f q q'
local notation "CB0" => bite u d q
variable (H : Probe W k w' 0 (d*b) D a a) (hp : Probe f k j (q+1) (d*b) D u u) (hv : Probe g k w q' (d*b) D v v) (hk : n+(q'+q*n) < k) (hj : 1≤ n) (hh : 0 < b) (hB : 1 < d) (ht : d*b ≤ 1)
    (hm : ∀ y∈ball 0 (bite u d q*b), Brush k C 1 Real.exp y) (he : bite u d q*b ≤ 1)

def aid (C u v d a : ℝ) (n k q q' : ℕ) := a*(v*d^q')*2^k * (k.factorial*(C * bite u d q^(n+1))*2^k)*2^k
include hp hv hk H hj hh hB ht hm he
omit [DecidableEq ι] in
lemma disc : Purchase (numeric b W g f q q' (Real.exp-blockTaylor n Real.exp)) k s D s⁻¹ (aid C u v d a n k q q'*b^(n+1)) := by
  let Z:= Real.exp-blockTaylor n Real.exp
  have hr:= zero_lt_one.trans hB; have hx:= mul_pos hr hh; have hu0:=hp.stencil.positive
  have hq : q ≤ q*n:= Nat.le_mul_of_pos_right _ hj
  have hg := hp.numeric hh hr ht (by omega)
  have hf:= hv.numeric (q:=q') (t:=0) hh hr ht (by omega); simp only [pow_zero,mul_one,pow_one,Nat.add_zero] at hf hg
  have hy0 : 0<CB0*b:= by unfold bite; positivity
  have hC:= (hm 0 (mem_ball_self hy0)).nonneg
  have hx': 0 < CB0:=pos_of_mul_pos_left hy0 hh.le
  let p:= (k.factorial*(C*CB0^(n+1))*2^k)*b^(n+1); have hv0 : 0 ≤ p:=by unfold p; positivity
  have hP : Purchase (fun z y=> Z ((b⁻¹^q • f) z y)) k s D s⁻¹ p:= by
    refine read_comp hg _ ((Real.measurable_exp).sub (blockTaylor_contDiff n Real.exp k|>.continuous|>.measurable)) hv0 ?_
    intro y hy z hz
    let A:=u*d^(q+1)+1; have hr' : A<CB0:=by unfold A bite; linarith
    have hA := (hg.toll y hy).2 z
    have hs:= hA.climb (mul_le_mul_of_nonneg_right (show u*d^(q+1) ≤ A from le_add_of_nonneg_right zero_le_one) hh.le) le_rfl
    have ht:=AuxCurtain.reprice_exp hs (by unfold A; positivity) (mul_lt_mul_of_pos_right hr' hh) he hm le_rfl (by omega : n<k)
    refine ht.climb (le_of_eq ?_) le_rfl; unfold p; rw [mul_pow]; ring
  have hz:= ((H.stencil.widen ((one_le_inv₀ hx).2 ht) le_rfl).productP hf).productP hP
  apply hz.widen le_rfl; unfold aid p at *; exact le_of_eq (by ring)

variable [FiniteDimensional ℝ E]
section withQ
variable (Q : Matrix ι ι ℝ)
local notation "T" => Finset.range (n+1)
def intent (Q:Matrix ι ι ℝ) (W f g : Y→ℝ×E→ℝ) (q q' n : ℕ) : Co E:=
    ∑ i∈Finset.range (n+1), (point_co Real.exp i) • readsH Q (W*g*f^i) (q'+q*i)
def fare (C u v d a : ℝ) (n k q q' : ℕ):= aid C u v d a n k q q'+ ∑ i∈Finset.range (n+1), |point_co Real.exp i| * ritual_fee (q'+q*i) n (each i k a u v) (each i k a u v) d

lemma proceeds {x : E} (hx: ‖x‖ < d*b) (hq : Q.PosDef) (HH : ∀ z:ι→ℝ,dotProduct z (Q*ᵥ z) ≤ M*dotProduct z z) (hD : 0 ≤ D) (hZ : ∫ z in (closedBall (0:Y) D)ᶜ,(1+‖z‖)^(w'+w+j*n) ∂Poll.sweep Q ≤ b^(n+(q'+q*n)+1)) :
    AuxStage.Points (fare C u v d a n k q q') s⁻¹ b n k (fun x:E=> intake Q (numeric b W g f q q' Real.exp) D (b,x)) x (intent Q W f g q q' n) := by
  let o i:= point_co Real.exp i
  let p i := W*g*f^i; let h i:=q'+q*i
  let c i :=each i k a u v
  let F (i:ℕ) (z:ℝ×E):=o i*(b⁻¹^(h i)* intake Q (p i) D z)
  have hi (i) (hi:i∈ Finset.range (n+1)) : i ≤ n:= Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hw i (he:i≤n) : h i ≤ h n:= by unfold h; gcongr
  have hR : b < d*b:=lt_mul_of_one_lt_left hh hB
  let r:=s; have hr:0<r:= hh.trans hR; have hx': (b,x)∈ball 0 r:= mem_ball_zero_iff.mpr (max_lt (by rw [Real.norm_of_nonneg hh.le]; exact hR) hx)
  have ha:=disc H hp hv hk hj hh hB ht hm he
  let A:=aid C u v d a n k q q'
  let R:= U (Real.exp-blockTaylor n Real.exp); let f' x:= intake Q R D (b,x)
  have hW := at_center ha Q (b,x) hx'
  have hb0: Brush k (A*b^(n+1)) s⁻¹ f' x:= on_arc hW.2
  have hF (i:ℕ) (hi':i≤n) := H.tile hp hv hk hi'
  let X:= ∑ i∈T, fun y:E=>F i (b,y)
  have hG : AuxStage.Points (∑ i∈T,|o i| * ritual_fee (h i) n (c i) (c i) d) s⁻¹ b n k X x (intent Q W f g q q' n):= by
    refine Points.summing _ _ _ _ hW.2.pos hh.le (fun i hi=>?_)
    have hκ:= hw i (show i ≤ n from Nat.le_of_lt_succ (Finset.mem_range.mp hi)); have ht' := estimates (H.tile hp hv hk (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (show n+h i < k from Nat.lt_of_le_of_lt (Nat.add_le_add_left hκ _) hk) (le_refl k) hq HH hD (hZ.trans (pow_le_pow_of_le_one hh.le (hR.le.trans ht) (by unfold h at hκ; omega))) hh hB ht x hx
    exact ht'.scale (o i)
  refine Points.quote hG A (hb0.shimmy ?_) (nonneg_of_mul_nonneg_left hb0.nonneg (pow_pos hh (n+1))) hh.le
  -- raw sum holds on the same neighborhood, with fixed D and current b
  filter_upwards [(isOpen_ball.mem_nhds (x:=x) (mem_ball_zero_iff.mpr hx))] with y hy
  have hw : (b,y)∈ball 0 r:=mem_ball_zero_iff.mpr (max_lt (by rw [Real.norm_of_nonneg hh.le]; exact hR) (mem_ball_zero_iff.mp hy))
  let Y' (i:ℕ) (z:Y):=(o i*b⁻¹^(h i))* truncate (p i) D (b,y) z
  have hΨ(i) (he':i∈T): Integrable (Y' i) (Poll.sweep Q):= ((at_center (hF i (hi _ he')).stencil Q (b,y) hw).1).const_mul _
  have hhS: truncate (numeric b W g f q q' Real.exp) D (b,y)= (fun z=>∑ i∈T,Y' i z)+truncate R D (b,y):= by
    ext z; by_cases h':z∈closedBall 0 D; swap
    · simp only [truncate,Y',h',not_false_eq_true, indicator_of_notMem,Pi.add_apply,mul_zero,Finset.sum_const_zero,add_zero]
    simp only [Y',truncate, h',indicator_of_mem, Pi.add_apply,p,h,R,numeric,Pi.mul_apply,Pi.pow_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply]; rw [dom];
    unfold o; rw [mul_sub, Finset.mul_sum]
    have h_eq (U0 V F:ℝ) : (∑ i∈T, point_co Real.exp i * b⁻¹^(q'+q*i)*(U0*V*F^i))= ∑ i∈T, U0*(b⁻¹^q'*V)*(point_co Real.exp i * (b⁻¹^q * F)^i):= Finset.sum_congr rfl (fun i _=> by rw [pow_add,pow_mul,mul_pow]; ring)
    rw [h_eq]; ring
  change intake Q (U Real.exp) D (b,y)-X y=f' y
  unfold intake; rw [hhS,integral_add' (integrable_finsetSum _ hΨ) (at_center ha Q (b,y) hw).1,integral_finsetSum _ hΨ]; unfold X; rw [Finset.sum_apply, Finset.sum_congr rfl (g:=fun i=>F i (b,y)) _]; exact add_sub_cancel_left _ _
  intro i hi; unfold Y' F intake h p; rw [integral_const_mul, mul_assoc]
end withQ
end YM.RGComparison01.AuxFabric
