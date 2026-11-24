import YM.QuadraticLocal.Earn.Wheels
/-! # Paying all the printed requests

One **common** output coefficientα at all configurations in the declared census/stencil
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
def flat (a σ e:ℝ)(T H:ℕ):ℝ:= Real.exp (-(a-a/2)*T)*(1+e)+(Real.exp (-(σ/2)*T)+Real.exp (-(a/8)*H))*e
omit hf hw hh B in
lemma flat_nn (he:0≤e): 0< flat a σ e T H:= add_pos_of_pos_of_nonneg (mul_pos (Real.exp_pos _) (by linarith)) (mul_nonneg (by positivity) he)
lemma omitted_near (h:Together X C q T H): SumBudget (fun i:Press.Palette X q S C => if Visible X C q S i U' H then 0 else P!* i) ((j+1:ℕ)*(A₀ * (C₀*(1+e)) *F*f)):= by
    have hx:0≤e:= budget_nonneg (B.care C (0:Et)).price
    have ht:0 ≤ A₀:= mul_nonneg (Real.exp_pos _).le (active X w hw ..).le
    apply trapeze _ (every _ (by positivity : 0≤ (A₀)* (C₀*(1+e)) *F*f)); intro i
    let u:= M i; let s:=litList X C q S U' i; let g' j:= Trace.rent e₁ Zs u s (a/2) j; let D:= Press.Mint X q C u
    let t:= A₀*(F*f); have ht₁:0≤ t:=by unfold t; positivity
    let b(j:D):= t*g' j.val; have hA := Minty.accord e₁ Zs u (B.care C i) (U'.survey C i) T (half_le_self hh.waist.le) (U'.postage C i); let k:= C₀; have hp : SumBudget b (t*(k+k*e)):= budget_scale ht₁ (budget_pull (Subtype.val:D→u.Ty) (Subtype.val_injective («p»:=_)) hA)
    refine budget_loosen (budget_mono hp (fun i=>?_) (fun x=>?_)) (le_of_eq (by unfold t k; ring)) -- i shadow
    · rename_i j' -- may wrong
      split; rfl; next=> exact (Accumulate.pieces (Press.estate X C q S B · ρ) w hw ρ (⟨j',i⟩:Y)).le
    split; exact hp.1 _; next hL=>
       apply le_trans (Width.house X C q S B ⟨i,x⟩ w hw (hf C) hh); have he : g' x.val=u.price (a/2) x.val:=if_pos ⟨fun he=>hL ⟨h,he⟩,x.prop.1⟩
       unfold b; rw [he]; exact le_of_eq (by unfold u t; simp only []; ring)

omit B hw hf -- need hh only
private lemma eitherAway (h:¬ Together X C q T H): F*f ≤ g₁*(Real.exp (-(σ/2)*T)+Real.exp (-(a/8)*H)):= by
   let v:= Φ; let r:=g₁; have ha:f=r*r:=by rw [←  Real.exp_add]; ring_nf -- defeq r rewrite
   have hF: F ≤ 1:= Real.exp_le_one_iff.mpr (by have h:=hh.positive; nlinarith only [h,Nat.cast_nonneg (Club.length X C) (α:=ℝ)])
   have hR: r ≤1:= Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by have h:=hh.waist; linarith : -(a/8) ≤ 0) (Nat.cast_nonneg _))
   have hr:0≤r:=(Real.exp_pos _).le; rw [ha, mul_left_comm F]; apply mul_le_mul_of_nonneg_left _ hr
   by_cases hm:v≤ H
   · obtain ⟨i,hi⟩ : ∃ i∈C.val, T < (X i).length:= by contrapose! h; exact ⟨hm,h⟩
     have h': F ≤ Real.exp (-(σ/2)*T):= Real.exp_monotone (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (hi.2.le.trans (Club.en_route X C _ hi.1))) (neg_nonpos.mpr (by have hz:= hh.positive; linarith)))
     exact ((mul_le_of_le_one_right (Real.exp_pos _).le hR).trans h').trans (le_add_of_nonneg_right (Real.exp_nonneg _))
   have hz:r≤ Real.exp (-(a/8)*H):= Real.exp_monotone (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (Nat.le_of_lt (lt_of_not_ge hm))) (neg_nonpos.mpr (by have h:= hh.waist; linarith)))
   exact ((mul_le_of_le_one_left hr hF).trans hz).trans (le_add_of_nonneg_left (Real.exp_nonneg _))
omit hh -- generic F
def mint (Lp:Side)(k j:ℕ)(a ρ:ℝ):ℝ:= ((j+1:ℕ):ℝ)*stash ρ k*sink (a/8) Lp k

include B hh hw hf
lemma venia : SumBudget (fun i:Press.Palette X q S C => if Visible X C q S i U' H then 0 else P!* i) ((j+1:ℕ)*(A₀ * flat a σ e T H *g₁)):=by
    have hx:0≤e:= budget_nonneg (B.care C (0:Et)).price
    let t:=( C₀); let z:= Real.exp (-(σ/2)*T)+Real.exp (-(a/8)*H); have ht:0 ≤ A₀:= mul_nonneg (Real.exp_pos _).le (active X w hw ..).le; let k':=k
    by_cases h: Together X C q T H
    · refine budget_loosen (omitted_near X C q S B w hw hf hh H U' h) (mul_le_mul_of_nonneg_left (le_trans ?_ (?_: A₀ * (C₀*(1+e))*g₁ ≤_)) (Nat.cast_nonneg _))
      · rw [mul_assoc]; -- examine wrong occurrence
        have hF: F ≤ 1:= Real.exp_le_one_iff.mpr (by have he:=hh.positive; nlinarith only [he,Nat.cast_nonneg (Club.length X C) (α:=ℝ)])
        have h₁: f≤g₁:= Real.exp_monotone (mul_le_mul_of_nonneg_right (by have hz:=hh.waist; linarith : -(a/4)≤-(a/8)) (Nat.cast_nonneg _));
        exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left (Real.exp_pos _).le hF).trans h₁) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg (by positivity) hx)) ht) (Real.exp_nonneg _)
    show SumBudget (fun i:Y=> if Vd i then 0 else P!* i) _; simp_rw [Visible,h,false_and,ite_false] -- replace with False
    have he:=eitherAway (k:=k) X C q hh H h -- args
    refine budget_loosen (brushes X C q S B w hw hf hh) (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _));
    change A₀ * e * F * f≤ A₀ * (t*(1+e) + z*e) * g₁; calc
       _ = A₀*e* (F*f):= by ring
       _ ≤ A₀*e*(g₁*z):= mul_le_mul_of_nonneg_left he (mul_nonneg ht hx)
       _ = A₀*(z*e)*g₁:=by ring
       _ ≤ _:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by unfold t; positivity)) ht) (Real.exp_nonneg _)

end Width
end YM.QuadraticLocal.Earn
