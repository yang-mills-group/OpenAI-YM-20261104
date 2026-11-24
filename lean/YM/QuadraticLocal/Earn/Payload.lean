import YM.QuadraticLocal.Earn.Promote
import YM.QuadraticLocal.Echo.Edge
/-!
 # From the exponentially compact kernel lens ATTAINED in a step
   to the real multi-slot projection—with stencils & Loan charges.

 A `Press` describes the actual analytic certificate to look for on a range of
 perturbative orders. Producing such a certificate for the PARTICULAR thing we
 are approximating, before doing this rendering, is therefore important: we may
 generate the labels and analytic stencil-support choices ahead of ANY painting
 tests, not borrowing their budget anew. In the construction sufficiency must/can
 be shown simultaneous in view/body, as in Audience.

 Projection keeps all the faithfully identified/nonzero kernels INCLUDING winding
 and rank-zero. ANC coordinates from all participants, NOT merely their centers.
 Pays kernel price on a static context for all reader λ inputs. `loc` and
 true paths charged by `Binder`. No proof of uniform censorship from a period-zero
 equality or choice of convex Ψ body. All projected births still pay the kernel
 ledger with every ghost-hook.Callback to account high-order Book cap separately.

 Query order fixed by consumer. Need still prove for each demand short stamps
 the estimate vs physical responding Student.Path. This file is the assembly of the
 purchased analytic CAPSULES into a multi-mark (whole phase μ) output representation,
 not pricing them or buying the estimates yet.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice Laurent RG Wilson Marker Ac
open Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Echo AllOrder AllOrder.Ink
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι : Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e σ r b :ℝ} {k u i' j h : ℕ}
namespace Bloom
-- maybe put in Derivs so charged from source winding. Doesn't affect stencil Length; focal
variable (A:Atom G k)
def letdown (v:ℝ) : Atom G k:= {A with coeff i:= v*A.coeff i}
lemma step (t:ℝ)(x:Fin k → G.Color) : (Bloom.letdown A t).poly x=t*A.poly x:=by unfold Atom.poly Bloom.letdown; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _=> mul_assoc ..)
lemma grant (t:ℝ)(V:Config G n)(x:Site n): (letdown A t).unmasked V x=t*A.unmasked V x:= step ..
lemma claim (t:ℝ)(h:A.Invariant): (letdown A t).Invariant:= by intro g U; simp_rw [Bloom.step, h g U] -- check
lemma reduce_charge (t a:ℝ): (letdown A t).budget a=|t| * A.budget a:=by unfold Atom.budget Atom.magnitude letdown; dsimp only; simp_rw [abs_mul,← Finset.mul_sum]; exact mul_assoc ..
lemma awaken (V:Config G n)(x:Site n)(h:A.magnitude=0): A.unmasked V x=0:=by
 have hh:= A.unmasked_bound V x; rw [h,zero_mul] at hh; exact norm_le_zero_iff.mp hh
end Bloom

variable (X:ι→Row P R G α) (C:Club X) (q:Ratio c n)

structure Press (j:ℕ) where
   news : ∀ C:Club X, Fin (j+1)→Poetry.Roll G (Club.Keys X C)

namespace Press
open Club
set_option quotPrecheck false
def toll :ℕ:= ∑ i∈C.val,(X i).lamp.toll
theorem tall (w:V→ℕ) (hs:∀ i,(X i).Credentials k w): toll X C=∑ i∈ (Club.alliance X C).val,w i:=by rw [Club.toll]; exact Finset.sum_congr rfl (fun i _=> (hs i).2)
lemma ticket_pos : 0 < toll X C:= lt_of_lt_of_le (X (Club.stamp X C (Club.lowest X C))).lamp.higher (Finset.single_le_sum (f:=fun i=>(X i).lamp.toll) (fun i _=> Nat.zero_le _) (Club.attends ..))
local notation "s₁"=> (toll X C) -- note Club.toll ambiguous. qualify throughout
local notation "r₁" k:max=> k+Press.toll X C+2
local notation "E"=> (P.coarser q)
local notation "K"=> Club.Keys X C
local notation "L"=> Club.lowest X C
local notation "Z" a:max=> Club.site X C q a
variable (S:Press X j)
local notation "D" k:max=> (S.news C k)
structure Receipt (S:Press X j)(a b:ℝ): Prop where
   care (i:Club X) (k:Fin (j+1)): (S.news i k).Faith Finset.univ (Club.lowest X i) (k.val+Press.toll X i+2) a b
   loyal i k (x:(S.news i k).Ty): ((S.news i k).leg x).atom.Invariant
variable (B:Receipt X S a e)
local notation "Λ"=> ( Fin (j+1))
abbrev Mint (C:Club X)(Y:Poetry.Roll G (Club.Keys X C)) := { p:Y.Ty// Spot.Entails (Y.leg p) (Club.lowest X C) (Club.site X C q) ∧ 0<(Y.leg p).atom.magnitude }
abbrev Palette (C:Club X):=Sigma (fun i:Fin (j+1)=> Press.Mint X q C (S.news C i)) -- syntax shadow C inside `D` macro?
abbrev Runway := Sigma (Press.Palette X q S)
variable (p: Press.Palette X q S C)
local notation "λ₀"=> (D p.fst)
local notation "Ω"=> (λ₀.leg p.snd.val) -- dot token caution.L
abbrev plant : Poetry.Lantern G (Club.Keys X C):=(D p.fst).leg p.snd.val
local notation "p₀"=> (Press.plant X C q S p)
include B
lemma pinned : (Press.plant X C q S p).Bears Finset.univ (Club.lowest X C) (p.fst.val+Press.toll X C+2):= (B.care C p.fst).pinned p.snd.val
local notation "hx✴"=> Press.pinned X C q S B p
lemma rank : (Press.plant X C q S p).r ≤ p.fst.val + Press.toll X C + 1:=by
   let T:=(p₀); have hc:T.r+T.roots.length ≤p.fst.val + Press.toll X C+2:= (hx✴).tall; have hV:0<T.roots.length:=List.length_pos_of_mem ((hx✴).owns); change T.r ≤ _; omega
local notation "δ"=> Promote.mend X C q (p₀) hx✴ p.snd.prop.1
def loan : Loan := ⟨p.fst.val,(p₀).r,Press.toll X C,ticket_pos X C, Press.rank X C q S B p⟩
variable (ρ :ℝ)
omit B
lemma magnitude : 0<(p₀).atom.budget ρ:= mul_pos p.snd.prop.2 (Real.exp_pos _)
local notation "τ"=> ((p₀).atom.budget ρ)
local notation "u₁"=> Bloom.letdown ((p₀).atom) τ⁻¹ -- scopes
local notation "b₁"=> Press.loan X C q S B p
def estate : Row (P.coarser q) R G α := ⟨δ, b₁,u₁,Bloom.claim _ _ (B.loyal C p.fst p.snd.val), (p₀).r=0, τ*(∏ i∈C.val,(X i).salary), mul_pos (magnitude X C q S p ρ) (Finset.prod_pos fun i _=> (X i).sound),fun t=> (Complex.ofReal τ)*( ∏ i∈C.val,(X i).paint t), id⟩
local notation "T"=> (Press.estate X C q S B p ρ)
include B
lemma licensed (w:V→ℕ)(hv:∀ i,(X i).Credentials j w): (Press.estate X C q S B p ρ).Credentials j w:=⟨ Nat.le_of_lt_succ p.fst.prop,tall X C _ hv⟩
lemma assured : (T).Graceful ρ:=by change (Bloom.letdown (plant X C q S p).atom τ⁻¹).budget ρ ≤ 1; have hf:= Press.magnitude X C q S p ρ; rw [Bloom.reduce_charge, abs_of_pos (inv_pos.mpr hf), inv_mul_cancel₀ hf.ne']
lemma plotted (h:∀ i,(X i).Budget): (Press.estate X C q S B p ρ).Budget :=by
   intro v; have hv:= Press.magnitude X C q S p ρ; unfold Press.estate; dsimp only; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hv.le,norm_prod]; exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=> h i v)) hv.le
lemma offered (t:α)(z:ℝ)(U:Config G c)(hz:0<z): (T).nominal z t U = (∏ i∈C.val,(X i).paint t)* (Trace.offered (Club.lowest X C) (Club.site X C q) (Press.plant X C q S p) z p.fst.val U :ℂ):=by
   let M:=(p₀).atom; let u:= Club.roof X C q; let k':=(p₀).r; have he:= Press.magnitude X C q S p ρ
   change ((Complex.ofReal τ)*(∏ i∈C.val,(X i).paint t)) * ( (z^((p.fst.val:ℤ)-((p₀).r:ℤ))*(Bloom.letdown M τ⁻¹).unmasked U u:ℝ):ℂ)= _ * ((AllOrder.Plateau.ratioW z p.fst.val k'* M.unmasked U u:ℝ):ℂ)
   rw [Bloom.grant,zpow_sub₀ hz.ne',zpow_natCast,zpow_natCast,div_eq_mul_inv]; unfold Plateau.ratioW k'; push_cast; have h0z:Complex.ofReal z≠0:= Complex.ofReal_ne_zero.mpr hz.ne'; have h₁: Complex.ofReal ((plant X C q S p).atom.budget ρ) ≠ 0:=Complex.ofReal_ne_zero.mpr he.ne'; field_simp [h0z,h₁] <;> ring -- might unsolved via field_simp Complex positivity; add hn
-- Exponential receipt Pu.Cost.Entry_Bounds.Binding.L. countable all nonzero
omit B in
lemma owned {Y: Roll G (Club.Keys X C)} (hh: Summable (Y.price a)): Countable (Mint X q C Y) :=by
    let U:= Function.support (Y.price a); haveI : Countable U:= Set.Countable.to_subtype hh.countable_support
    let f (i:Mint X q C Y) : U:= ⟨i.val,(mul_pos i.prop.2 (Real.exp_pos _)).ne'⟩; exact Function.Injective.countable (f:=f) (fun x y h=> Subtype.ext (congr_arg (fun x:U=> x.val) h)) -- Drop B omit
lemma availability : Countable (Press.Palette X q S C) := by haveI : ∀ t, Countable (Mint X q C (D t)) := fun t=>Press.owned X C q ((B.care C t).price.2.1); unfold Press.Palette; infer_instance
omit B in
lemma ranked {Y:Poetry.Lantern G (Club.Keys X C)} (hp:Y.atom.magnitude ≤ 0) : Trace.offered (Club.lowest X C) (Club.site X C q) Y a i'= 0 := by ext1 u; unfold Trace.offered; rw [Pi.smul_apply,Bloom.awaken _ u _ (le_antisymm hp (Texture.mag_nonneg _)), smul_zero]; rfl
local notation "Ω'"=> Press.Runway X q S
def placement (ρ:ℝ)(t:Press.Runway X q S) : Row (P.coarser q) R G α := Press.estate X t.fst q S B t.snd ρ
lemma places [Countable ι]: Countable (Press.Runway X q S):=by
   haveI : ∀ C,Countable (Palette X q S C):= fun C=>availability X C q S B; unfold Runway; infer_instance
end Press
end YM.QuadraticLocal.Earn
