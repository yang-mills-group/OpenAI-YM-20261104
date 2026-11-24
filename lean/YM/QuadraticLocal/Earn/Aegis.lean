import YM.QuadraticLocal.Earn.Guard
/-! # Convolving the illumination receipt
window. Use with ANY given normalized operator fields then the estimated bill here
pays the FULL mixture, still summable in the ℝ-weighted sup norm at every center, along
with the exponential path costs. No expectation of exponential regular model approximation at the
real beta by the drawing of the true area. Projection from density permits cancellation only under
aligned masks. Also now provides account for selected omitted vs detached pieces of
rendering model for the physical implementation.

Use smaller sector rates with the TRUE support cost if engaging projection/readout on given e.g.
geodesic. -/
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
local notation "ω"=> Press.estate X C q S B
local notation "Q"=> (ω p ρ)
local notation "Θ"=> Press.plant X C q S
local notation "Θ'"=> Θ p
local notation "Ω"=> (Club.alliance X C)
local notation "F₀"=> Real.exp
local notation "Hℓ"=> (Width.stash ρ k)
local notation "V₁"=> (k:Finset ℕ) -- drop
local notation "Φ"=> (Club.reach X C q)
local notation "I"=> Accumulate.inside
local notation "Y"=> Press.Palette X q S C
local notation "Et"=> Fin (j+1)
local notation "Zℓ" t:max=> (S.news C t)
local notation "Qp"=> Press.placement X q S B ρ
variable (w:V→ℝ)(hw:∀ i,0<w i)
variable (hf:∀ C:Club X,(Club.alliance X C).val.card ≤ k)
variable (hh: Width.Memento k q.count σ ρ a)
local notation "K"=> Club.Keys X C
local notation "U" T:max=> Width.Viewer X S a T
variable {D T H :ℕ}
variable (U' : Width.Viewer X S a T)
local notation "ξ"=> U'.survey
local notation "e₁"=> Club.lowest X C
local notation "Zs"=> Club.site X C q

local notation "F"=> (Real.exp (-(σ/2:ℝ)*(Club.length X C:ℝ)))
local notation "fᵥ" i:max=> Real.exp (-(a/4)*(Club.reach X i q:ℝ))
local notation "f"=> (Real.exp (-(a/4)*(Φ:ℝ)))
local notation "A₀"=> ((Hℓ)*Λ w σ C)
local notation "g₁"=> (Real.exp (-(a/8)*(Φ:ℝ)))
local notation "M" i:max=> ( S.news C i )
local notation "x'"=> (Poly.toll w (Club.alliance X C))
include B hh hw hf
local notation "P!*" i:max=> x'* ( (ω i ρ).height ρ)
variable (H)
local notation "Vd" i:max=> Visible X C q S i U' H
local notation "C₀"=> Real.exp (-(a-a/2)*T)
include U'
local notation "pr" i:max=> Poly.toll w (Club.alliance X i)
local notation "Rf"=> Press.Runway X q S
local notation "φ"=> mint q.count k j a ρ
variable (hp:Offers X w σ b)(hb:b≤1)
variable {θ:ℝ}(he:0≤θ)
omit U'
include hp hb he
open Club Accumulate
lemma illumination (cost: Press.Runway X q S→ℝ) (ht:∀ c:Club X,SumBudget (fun v:Press.Palette X q S c=> cost ⟨c,v⟩) ((j+1:ℕ)*(stash ρ k * Accumulate.rootPrice X w σ c * θ * Real.exp (-(a/8)* Club.reach X c q)))) (x:Site c):
    SumBudget (fun i: Press.Runway X q S=>if (Press.placement X q S B ρ i).center=x then cost i else 0) ((Width.mint q.count k j a ρ)*θ*b):=by
    let S' := ((j+1:ℕ):ℝ); let u:= S'*Hℓ *θ; let A := Club X; let r i:= Real.exp (-(a/8)*(Club.reach X i q:ℝ)); let a':= sink (a/8) q.count k; let g i:= if Club.roof X i q = x then r i*rootPrice X w σ i else 0
    have hf: SumBudget g (b*a'):= Accumulate.total k X q w hw hp hb (fun i=> (Club.cardLe X i).trans (hf i)) x (by have h:=hh.waist; linarith)
    have hu:0≤u:= mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)) he
    apply budget_loosen (trapeze _ (budget_scale hu hf) _)
    · unfold u S'; exact le_of_eq (by unfold Width.mint a'; ring)
    intro i; change SumBudget (fun v:Press.Palette X q S i=> if (Club.roof X i q) = x then cost ⟨i,v⟩ else 0) _; unfold g; split; next hv=> exact budget_loosen (ht i) (le_of_eq (by unfold u S' r; ring))
    next h=> rw [mul_zero]; exact Extra.Multi.Budget.zero le_rfl
-- `placement` keeps all paint. don't assert multilinearity extensions.
variable (he':0≤e)
omit he
include he'
local notation "κ"=> flat a σ e T H
local notation "P★"=> Width.Visible
lemma crew : Offers (Press.placement X q S B ρ) w ρ ((mint q.count k j a ρ)*e*b):=by
    intro x; apply illumination X q S B w hw hf hh hp hb he' _ _ x
    intro I₀; let s:=Hℓ; let e':=Real.exp (-(σ/2:ℝ)*(Club.length X I₀:ℝ)); let p:= Club.reach X I₀ q; let v:= Accumulate.rootPrice X w σ I₀; let u:=Real.exp (-(a/4)*(p:ℝ)); let v₀:=s*v*e
    refine budget_loosen (brushes X I₀ q S B w hw hf hh) (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _));
    have he : u ≤ Real.exp (-(a/8)*(p:ℝ)):= Real.exp_monotone (mul_le_mul_of_nonneg_right (by have ha:=hh.waist; linarith : -(a/4)≤-(a/8)) (Nat.cast_nonneg _)); have hz:e' ≤1:= Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (half_pos hh.positive).le) (Nat.cast_nonneg _));
    refine le_trans (b:=v₀*u) (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le) (mul_le_mul_of_nonneg_left he (mul_nonneg (mul_nonneg (Real.exp_nonneg _) (active X w hw ..).le) he')); exact mul_le_of_le_one_right (mul_nonneg (mul_nonneg (Real.exp_nonneg _) (active X w hw ..).le) he') hz

local notation "Wf"=> Press.Palette X q S
-- semantic remainder.Use with Ledger.Peck actual. Travels in full sent Footprints.
def Obscure (i:Press.Runway X q S) (T:ℕ)(H:ℕ)(C':Viewer X S a T): Prop:= ¬ Visible X i.fst q S i.snd C' H
local notation "By" i:max=> Width.Obscure X q S i T H U'
abbrev Shaded (H:ℕ):= { x:Rf// Width.Obscure X q S x T H U'}
local notation "Ψ"=> (Press.placement X q S B ρ)
include U'
lemma nights : Offers ((Press.placement X q S B ρ) ∘ (Subtype.val (α:= Press.Runway X q S) (p:=fun i=> Width.Obscure X q S i T H U'))) w ρ ((mint q.count k j a ρ)*κ*b) := by
    intro x; let P' i:= (Press.placement X q S B ρ) i; let g(i:Rf):=Poly.toll w (P' i).mode*(P' i).height ρ; let C'(i:Rf):= Width.Obscure X q S i T H U'; let Fx(i:Rf):= if C' i then g i else 0
    have hc(F':Club X): SumBudget (fun i=>Fx ⟨F',i⟩) ((j+1:ℕ)*(stash ρ k * Λ w σ F' * flat a σ e T H * Real.exp (-(a/8)* Club.reach X F' q))) := by
       convert venia X F' q S B w hw hf hh H U' using 1; ext i; unfold Fx; by_cases h: P★ X F' q S i U' H; rw [if_neg (show ¬ C' ⟨F',i⟩ from fun he=> he h),if_pos h]; rw [if_pos (show C' ⟨F',i⟩ from h),if_neg h]; rfl
    let hf := illumination X q S B w hw hf hh hp hb (Width.flat_nn (a:=a) (σ:=σ) (T:=T) H he').le Fx hc x
    let X' := Width.Shaded X q S U' H; convert budget_pull (Subtype.val (p:=C')) Subtype.val_injective hf using 1; ext i;
    unfold Fx; rw [if_pos (show C' i.val from i.property)]
    exact rfl
    -- maybe status.prop [C']

end Width
end YM.QuadraticLocal.Earn
