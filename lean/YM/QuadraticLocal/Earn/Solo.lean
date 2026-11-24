import YM.QuadraticLocal.Earn.Width
/-!
 ## Forward authority: code the already GLOBAL terms as models
 In the exponential kernel passport they are entitled to pass WITHOUT either
 alignment merger detecting a flag to do it (of course if a mask is already
 there in a rank-zero row we instead put this into the stencil comparison and
 never this route). They won't enter the kernel groups comparison nor
 require means/test replumbing. Re-emitting the walk/path choices is still
 paid before continuation.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice Laurent RG Wilson Marker Ac
open Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Echo AllOrder AllOrder.Ink
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι : Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e σ ρ r b :ℝ} {k i' j u i h : ℕ}
namespace Solo
set_option quotPrecheck false
open Width Club Promote Press Accumulate Cable
local notation "Z"=> Cable.links
variable (A:Row P R G α) (q:Ratio c n)
def post : Binder (P.coarser q) R where
  mode := A.mode
  front := A.binder.front
  east:= A.binder.east
  path v:= follows q A.center (A.binder.path v)
  span v hv:= by rw [show (P.coarser q).origin A.binder.front=q.parent A.center from rfl, follows_tip, Row.center,A.binder.capacity v hv]; rfl
  extra:= Cable.mass q A.length

def transmit : Row (P.coarser q) R G α := { A with binder:= post A q } -- type diff
local notation "Ω"=> Solo.transmit A q
variable (hc:A.clear)
include hc
lemma ghost(v:Site n) (U:Config G n)(u':Site c)(U':Config G c): A.atom.unmasked U v=A.atom.unmasked U' u':=by unfold Atom.unmasked; apply congr_arg; funext i; exact False.elim (by have hp:=i.prop; have h:= A.rank hc; omega)
lemma rank_zero : A.atom.length=0:= by unfold Atom.length; have h:A.lamp.r=0:= A.rank hc; exact Finset.sum_eq_zero fun i hi=> False.elim (by have he:=i.prop; omega)
lemma retained (h:A.Graceful σ) : (Ω).Graceful ρ:= by
    change A.atom.budget ρ≤1; rw [Atom.budget, rank_zero A hc]; have he : A.atom.budget σ=A.atom.budget ρ:= by unfold Atom.budget; simp [rank_zero A hc];
    unfold Atom.budget at he; rw [rank_zero A hc] at he; change A.atom.budget σ≤1 at h; unfold Atom.budget at h; rw [rank_zero A hc] at h; exact he ▸ h
lemma reads (t:α) (U:Config G c) : (Ω).nominal g t U=A.nominal g t 1:= by unfold Row.nominal Row.grain; change A.paint t • (Complex.ofReal (g^A.lamp.lag*A.atom.unmasked U (Solo.transmit A q).center))= A.paint t • (Complex.ofReal (g^A.lamp.lag*A.atom.unmasked 1 A.center)); rw [Solo.ghost A hc A.center 1 (Solo.transmit A q).center U] -- orientation? ok n vs c

variable (hh: Width.Memento k q.count σ ρ a)
variable (hy:A.mode.val.card≤k)
local notation "V₁"=> A.mode.val
local notation "L"=> q.count
local notation "D"=> Cable.mass q A.length
local notation "p₁"=> (post A q)
include hh hy
lemma lengths : (Solo.transmit A q).length ≤ 3*k * D:= by
    have he: A.atom.length=0:= Solo.rank_zero _ hc
    have ht:1≤k:=(Finset.card_pos.mpr ⟨_,A.binder.east⟩|>.trans_le hy) -- < not ≤
    have hd i (hi:i∈ A.mode.val): let v₀:= A.binder; let q₀:= A.binder.distance i; (p₁).distance i ≤ 2 * D:= by
      intro v₀ q₀; rw [two_mul]; have hv:(v₀.path i).length+P.height i≤ A.length:=(A.binder.dues i hi).trans (Nat.le_add_right ..); exact Nat.add_le_add ((Cable.follows_bound ..).trans (Cable.mass_mono q ((Nat.le_add_right ..).trans hv))) (Cable.mass_mono q ((Nat.le_add_left ..).trans hv))
    have hp: (p₁).length ≤ D + k*(2*D):= Nat.add_le_add_left ((Finset.sum_le_sum hd).trans (by rw [Finset.sum_const,nsmul_eq_mul]; exact Nat.mul_le_mul_right _ hy)) _
    change (p₁).length+A.atom.length ≤ _; rw [he,Nat.add_zero]; apply hp.trans; nlinarith only [Nat.mul_le_mul_right D ht]
lemma freight : (Solo.transmit A q).height ρ ≤ Width.stash ρ k * A.height σ:= by
    let Z':= q.count.val; let v:ℝ:=A.atom.magnitude; let v₀:=(A.length:ℝ); have hL:0<(Z':ℝ):= Nat.cast_pos.mpr q.count.property
    have he: (D:ℝ) ≤ (Z:ℝ)*((Z':ℝ)+v₀)/(Z':ℝ):= by apply (le_div_iff₀ hL).mpr; rw [mul_comm]; unfold v₀; exact_mod_cast Cable.fare q A.length
    have hf:=lengths A q hc hh hy; let u:= (D:ℝ); let v':=(Solo.transmit A q).length
    have hg : ρ*v' ≤ ρ* (3*k:ℕ) * u:=by
       rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hh.nonzero.le; unfold u; exact_mod_cast hf
    unfold Row.height Width.stash; change A.salary* _ ≤_; rw [mul_left_comm, ← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ A.sound.le; apply Real.exp_monotone;
    have ht:(ρ* (3*k:ℕ))*u ≤ ρ* (3*k:ℕ)*(Z:ℝ)*((Z':ℝ)+v₀)/(Z':ℝ):= (mul_le_mul_of_nonneg_left he (mul_nonneg hh.nonzero.le (Nat.cast_nonneg (3*k)))).trans_eq (by ring);
    apply (hg.trans ht).trans; apply (div_le_iff₀ hL).mpr; push_cast; have hZ : 3*(k:ℝ)*ρ*Cable.links ≤ σ* Z':= by have h : 0 ≤ σ*(Z':ℝ):= mul_nonneg hh.positive.le hL.le; linarith only [h,hh.res]
    change ρ*(3*(k:ℝ))*_ * _ ≤ (_ + σ*v₀)*_; nlinarith only [mul_le_mul_of_nonneg_right hZ (show 0≤ v₀ from Nat.cast_nonneg _)] -- need damping
omit hc hh hy

abbrev Watching (X:ι→ Row P R G α):= {i:ι// (X i).clear}
variable (X:ι→ Row P R G α)
local notation "φ"=> X
local notation "K"=> Watching X
def clearBudget (n':Side) (k:ℕ)(a:ℝ) := Width.stash a k*((n'.val:ℝ)^4)
def capsules (i:Watching X) := transmit (X i.val) q
local notation "τ"=> capsules q X -- order
variable (w:V→ℝ)(hw:∀ i,0<w i) (hf:Offers X w σ b)(hp:∀ i:Watching X,(X i.val).mode.val.card≤k)
include hh hw hf hp
lemma offers : Offers (Solo.capsules q X) w ρ (clearBudget q.count k ρ*b):=by
    intro x; let z i:= (X i).height σ; let g:= Width.stash ρ k; let t(i:K):= g*(if Club.mask X q i.val=x then Poly.toll w ((X i.val).mode)*z i.val else 0); have he: SumBudget t (g*( (q.count.val:ℝ)^4 * b)):= budget_scale (Real.exp_pos _).le (budget_pull (Subtype.val:Watching X→ι) Subtype.val_injective (projected X q w hw hf x)); refine budget_loosen (budget_mono he (fun i=>by split; exact (pieces (capsules q X) w hw ρ i).le; exact le_rfl) (fun i=>by
       unfold t; split; next hp'=>
          rw [if_pos (show Club.mask X q i.val=x from hp'), mul_left_comm]; exact mul_le_mul_of_nonneg_left (freight _ q i.prop hh (hp i)) (Poly.worth hw _).le
       next=> exact he.1 _)) (le_of_eq (mul_assoc ..).symm)
end Solo
end YM.QuadraticLocal.Earn
