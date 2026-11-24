import YM.QuadraticLocal.Earn.Payload
import YM.QuadraticLocal.Earn.Atelier
/-! # Economizing the tickets for the reflected frame choreography

 Supports paid at full output exponent & output waist prepared anew AFTER Lumi→certificate.
 Requires L chosen before such frames. This and the payroll on tails at H supports
 lets continuation in such widths not spend a constant-factor of the exponential rate
 at every use.
 `ψ(Binding burn_stage)` purchases at L asymptotic. Our notion of size is TRUE winding
 length; can use thus also for pay relative forecasts. -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice Laurent RG Wilson Marker Ac
open Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Echo AllOrder AllOrder.Ink
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι : Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e σ ρ r b :ℝ} {k i' j u i h : ℕ}
variable (X:ι→Row P R G α) (C:Club X) (q:Ratio c n)
namespace Width
set_option quotPrecheck false
open Club Promote Press Accumulate
variable (S:Press X j)(B:Press.Receipt X S a e)(p: Press.Palette X q S C)
local notation "Z"=> Cable.links
local notation "L"=> q.count.val
local notation "Λ"=> (Accumulate.rootPrice X)
local notation "A'"=> Agenda.waist
local notation "Q"=> (Press.estate X C q S B p ρ)
local notation "Θ'"=> (Press.plant X C q S p)
local notation "μ"=> ((Θ').atom.magnitude)
local notation "θ"=> Club.length X C

local notation "Δ"=> (Press.toll X C)
structure Memento (k:ℕ) (b:Side)(σ ρ a:ℝ): Prop where
    positive : 0<σ
    nonzero : 0<ρ
    waist : 0<a
    res : 6*(k:ℝ)*Cable.links*ρ ≤ σ*(b.val:ℝ)
    rate : 4*((k:ℝ)+3)*ρ ≤ a

variable (w:V→ℝ)(hw:∀ i,0<w i)
def stash (ρ:ℝ)(k:ℕ):ℝ:= Real.exp (3*(k:ℝ)*Cable.links*ρ)
variable (hy:(Club.alliance X C).val.card ≤ k)
variable (hh: Width.Memento k q.count σ ρ a)
local notation "Ω"=> (Club.alliance X C)
local notation "F₀"=> Real.exp
local notation "Hℓ"=> (Width.stash ρ k)
local notation "Ω'"=> (Club.reach X C q)
include hh hy hw B
omit hw
lemma space :
    ρ*(Press.estate X C q S B p ρ|>.length)+ ρ*(Press.plant X C q S p|>.atom.length) ≤ σ/2*((Club.length X C):ℝ)+a/4*(Press.plant X C q S p|>.length)+3*k*Cable.links*ρ:=by
   let ν n:=Cable.mass q n; have hx:= Promote.bounds (X:=X) C q Θ' (Press.pinned X C q S B p) p.snd.prop.1 hy
   let v:= (Θ').length; let o:= Club.length X C; let e:= (Q).length; let u:= (Θ').atom.length
   change e ≤ _ at hx; have ht : (e:ℝ) + u ≤ ((k:ℝ)+3)*(v:ℝ)+3*k* (ν o:ℝ):=by
      exact_mod_cast (show e+u ≤(k+3)*v+3*k*ν o from (by exact le_trans (Nat.add_le_add hx (show u≤ v from Nat.le_add_left ..)) (le_of_eq (by ring))))
   have hv:((ν o:ℝ)) ≤ (Cable.links:ℝ)*( (L:ℝ)+(o:ℝ))/(L:ℝ) :=by
      have h':0<(L:ℝ):= Nat.cast_pos.mpr q.count.property; apply (le_div_iff₀ h').mpr; exact_mod_cast (by rw [Nat.mul_comm]; exact Cable.fare q o : ν o * L ≤ Cable.links*(L+o))
   have hg:(ρ*3*k)*(ν o:ℝ) ≤ σ/2*(o:ℝ)+3*k*Cable.links*ρ:=by
      apply (mul_le_mul_of_nonneg_left hv (by have h:=hh.nonzero; positivity : 0≤ρ*3*(k:ℝ))).trans; have hL:0<(L:ℝ):= Nat.cast_pos.mpr q.count.property
      rw [← mul_div_assoc]; apply (div_le_iff₀ hL).mpr; nlinarith only [mul_le_mul_of_nonneg_right hh.res (show 0≤ (o:ℝ) from Nat.cast_nonneg _)]
   change ρ*(e:ℝ)+ρ*(u:ℝ) ≤ _; have h₁:= mul_le_mul_of_nonneg_right hh.rate (show 0≤ (v:ℝ) from Nat.cast_nonneg _); have h₂:= mul_le_mul_of_nonneg_left ht hh.nonzero.le; nlinarith only [h₁,h₂,hg]
include hw
lemma house : Poly.toll w (Q).mode * (Q).height ρ ≤ Λ w σ C * Hℓ * ((S.news C p.fst).price (a/2) p.snd.val) * Real.exp (-(σ/2)*(θ:ℝ)) * Real.exp (-(a/4)*((Club.reach X C q):ℝ)):=by
   let V₀:= Q; let Θ := Ω; let u:= θ; let v:=(Θ').length; let t:=(Q).length
   let x:ℝ:= (Θ').atom.magnitude; let w' ℓ:= Poly.toll w ((X ℓ).mode) * ((X ℓ).salary); let f:=∏ i∈ C.val,w' i; have he:Poly.toll w Θ*(∏ i∈ C.val,(X i).salary)=f:=by rw [Club.union_price]; exact (Finset.prod_mul_distrib ..).symm
   have hf:0 < f := prod_pos fun i _=> mul_pos (Poly.worth hw _) (X i).sound; have hν:0<x:= p.snd.property.2
   have hz: Λ w σ C=f*Real.exp (σ*u):=by
       unfold Accumulate.rootPrice Row.height; simp_rw [← mul_assoc]; rw [Finset.prod_mul_distrib]; congr 1; unfold u Club.length; push_cast; rw [Finset.mul_sum, Real.exp_sum]
   let d₀:=3*(k:ℝ)*Cable.links*ρ; let x0:=(Θ').atom.length
   let D0:=σ*u+d₀+(a/2)*(v:ℝ)-(σ/2)*(u:ℝ)-(a/4)*(Club.reach X C q:ℝ)
   have hZ: (Club.reach X C q:ℝ) ≤ v:= by exact_mod_cast tethered X C q Θ' (Press.pinned X C q S B p) p.snd.prop.1
   have ha : ρ*(x0:ℝ)+ρ*t ≤ D0:=by unfold D0 d₀; have hp:= mul_le_mul_of_nonneg_left hZ hh.waist.le; change (Club.reach X C q:ℝ) ≤ ↑v at hZ; linarith only [hp,space X C q S B p hy hh] -- check args hw?
   let U₁:= x* Real.exp (a/2*v); rw [hz];
   calc
    Poly.toll w V₀.mode * (V₀.height ρ) = (f*x)*Real.exp (ρ*(x0:ℝ)+ρ*t):=by rw [Real.exp_add,← he]; change Poly.toll w Θ * ( (x*Real.exp (ρ*x0)*(∏ i∈C.val,(X i).salary)) * Real.exp (ρ*t))= _; ring
    _ ≤ (f*x)*Real.exp D0:= mul_le_mul_of_nonneg_left (Real.exp_monotone ha) (mul_pos hf hν).le
    _ = _:=by change f*x*Real.exp D0=f*Real.exp (σ*u)*Real.exp d₀*U₁*Real.exp (-(σ/2)*u)*_; unfold D0 U₁; simp_rw [neg_mul,sub_eq_add_neg, Real.exp_add]; ring
end Width
end YM.QuadraticLocal.Earn
