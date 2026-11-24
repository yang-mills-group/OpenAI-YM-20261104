import YM.MS.MomentumCharge
import YM.MS.LineCost
import Mathlib.Data.Fintype.Option

/-!
# Landau gauge conventions for the momentum calculus

Momentum variables use complex coefficients but sum integer directions in stable dimensions later. Expose single-color symbols; tensor with color identity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau
open Real Function Set Finset Plane Momentum Koszul
open Complex (I)
open scoped Topology ContDiff
variable {A C : Type*} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]
abbrev Atom (A:Type*) := Option A × Bool
abbrev Leg (A C :Type*) := Atom A × C
abbrev p (i:Atom A) := i.2.xor i.1.isNone
abbrev parity (i:Leg A C) := p i.1
abbrev dim (i: Atom A) : ℕ:= cond i.2 2 1
abbrev gauge (i:A):Atom A := (some i,false)
abbrev ghost : Atom A := (none,false)
abbrev anti (i:A):Atom A := (some i,true)
abbrev gaugeC : Atom A := (none,true)
def delta (i j:A) (c:ℝ) : ℝ := if i=j then c else 0
def precision (i j:A) (q:Momentum A):= delta i j q.sq-q i*q j
lemma realK (i j:A) (q:Momentum A): precision i j q= precision j i q:=by unfold precision delta; simp only [eq_comm (a:=j),mul_comm (q i)];
omit [DecidableEq A] in
@[simp] lemma sq_neg (q:Momentum A) : Momentum.sq (-q)=Momentum.sq q := by simp [Momentum.sq]
@[simp] lemma k_even (i j:A) (q:Momentum A): precision i j (-q)=precision i j q:=by simp [precision]
lemma k_times (i j:A) (q:Momentum A) : (∑ a:A, precision i a q * precision a j q)= q.sq*precision i j q := by
   unfold precision delta
   simp_rw [sub_mul, mul_sub,sum_sub_distrib]; simp [ite_mul, mul_ite]
   have hm : (∑ a:A, q i * q a * (q a * q j)) = q.sq*(q i * q j) := by
      unfold Momentum.sq; rw [sum_mul]; exact sum_congr rfl fun k _=>by ring
   rw [hm]; ring

-- one-color layers before pullback on wave

def bare : Atom A → Atom A → Momentum A → ℂ
| (none,false),(some j,false),q=> I*(q j)
| (some j,false),(some a,true),q=> -(precision a j q:ℂ)
| (some j,true),(none,true),q=> - (I*(q j))
| _,_,_=>0

variable {P : Type*}
def stamp (f:P → Momentum A) : Plane.Charge (p (A:=A)) P ℂ where
    table i j q:= bare i j (f q)
    from_opposite a e q h:= by rcases a with ⟨_|a,_|_⟩ <;> rcases e with ⟨_|e,_|_⟩ <;> first | rfl | exact (h rfl).elim

/-- Polchinski multiplier for the logarithmic derivative, pair already halved. -/
def line (r:ℝ) : Flux (Atom A) (Momentum A) ℂ
| (some j,false),(some a,false),q=> (coat 2 r (precision j a) q:ℂ)
| (some j,true),(none,false),q=> I * coat 1 r (fun q : Momentum A=> q.sq*q j) q
| (none,false),(some j,true),q=> I * coat 1 r (fun q : Momentum A=> q.sq*q j) q
| _,_,_=>0

-- w is multiplier χ or its dot. Includes 1/2

def laplace (w : Momentum A → ℝ) : Flux (Atom A) (Momentum A) ℂ
| (some j,true),(some a,false),q=> (delta j a (w q):ℂ)/2
| (some j,false),(some a,true),q=> (delta j a (w q):ℂ)/2
| (none,true),(none,false),q=> -(w q:ℂ)/2
| (none,false),(none,true),q=> -(w q:ℂ)/2
| _,_,_=>0

def low (r:ℝ) (p:Momentum A):= coat 0 r (fun p : Momentum A=> 1 + p.sq) p
def dotLow (r:ℝ) (p:Momentum A):= coat 0 r (fun p : Momentum A=> -2*p.sq^2) p
-- explicit comm proof
lemma k_scale (i j:A) (q:Momentum A) (r:ℝ): precision i j (r • q)= r^2 * precision i j q:=by unfold precision delta; rw [scaling]; dsimp only [Pi.smul_apply, smul_eq_mul]; split <;> ring
private lemma corners (i j:A) (q:Momentum A) :
    - q.sq*precision i j q-q.sq*(q i*q j)= - delta i j (q.sq^2) := by unfold precision delta; split <;> ring
lemma identity (r:ℝ) (a e : Atom A) (q:Momentum A) :
    (stamp id).change (line r) a e q= laplace (dotLow r) a e q:=by
    unfold Plane.Charge.change
    have hc (x y : ℂ) : I*x*(I*y) = -(x*y) := by rw [show I*x*(I*y)= I^2 * (x*y) by ring, Complex.I_sq]; ring
    let z : ℂ := (Real.exp (- (r^2*q.sq)):ℝ); let w:ℂ := (r:ℂ)^4*z
    let d:ℂ:=q.sq
    have hm : z = Complex.exp (-((r:ℂ)^2*(q.sq:ℂ))) := by unfold z; simp
    have hw (x:ℝ) : (r:ℂ)*((r:ℂ)^2*(q.sq:ℂ)*((r:ℂ)*(x:ℂ))*z)=d*w*x := by unfold d w; ring
    have hj (x:ℂ) : (r:ℂ)^2 *((r:ℂ)^2*x*z)=w*x:=by unfold w; ring
    have hd : 2*((r:ℂ)^2*(q.sq:ℂ))^2*z/2=d*w*d:= by unfold d w; ring
    have hv : ∑ x:A, (q x:ℂ)*(q x:ℂ)=d := by unfold d Momentum.sq; simp only [Complex.ofReal_sum, pow_two,Complex.ofReal_mul]
    have h1 (i j:A) : ∑ x, (precision i x q:ℂ)*(precision x j q:ℂ)=d*precision i j q:= by unfold d; exact_mod_cast k_times i j q
    -- cases simplify sums then generic bodies
    rcases a with ⟨_|a,_|_⟩ <;> rcases e with ⟨_|e,_|_⟩ <;>
       simp [Fintype.sum_prod_type,Fintype.sum_option, stamp, p,cross, line,bare,laplace, dotLow, coat, k_even, k_scale, scaling]
    all_goals simp_rw [← hm,hc] -- replace after simp
    all_goals simp_rw [hw]
    · rw [Finset.sum_neg_distrib, neg_neg,hd]; simp_rw [mul_assoc (d*w),← Finset.mul_sum,hv]
    · rw [Finset.sum_neg_distrib, neg_neg,hd]; simp_rw [mul_assoc (d*w),← Finset.mul_sum,hv]
    · simp_rw [hj,mul_assoc w,realK (i:=e),← Finset.mul_sum] -- realK arg maybe
      rw [h1]; dsimp only [z,w,d,precision,delta]; split <;> push_cast <;> ring
    · have hh (i:A) : (precision i e q:ℂ) * (precision a i q:ℂ)=(precision a i q:ℂ)*(precision i e q:ℂ):= mul_comm ..
      simp_rw [hj, mul_assoc w,hh,← Finset.mul_sum,h1]; dsimp only [z,w,d,precision,delta]; split <;> push_cast <;> ring
end YM.MS.Landau
