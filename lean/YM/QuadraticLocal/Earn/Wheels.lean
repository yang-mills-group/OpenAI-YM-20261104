import YM.QuadraticLocal.Earn.Width
import YM.QuadraticLocal.Echo.Minty
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
-- all classification.Support.T.Auth.PIT.Plume.Area.
structure Viewer (a:ℝ)(T:ℕ) where
    survey : ∀ C:Club X, ∀ i:Fin (j+1), Finset ((S.news C i).Ty)
    postage C i: SumBudget (Minty.crystal (S.news C i) (survey C i) a) (Real.exp (-(a-a/2)*T))
local notation "K"=> Club.Keys X C
local notation "U" T:max=> Width.Viewer X S a T
variable {D T H :ℕ}
variable (U' : Width.Viewer X S a T)
local notation "ξ"=> U'.survey
local notation "e₁"=> Club.lowest X C
local notation "Zs"=> Club.site X C q

-- not member Notify.App.Op.Shape seeds without actually on Real stencil engagements. Width uniforms ALL quicker channels
local notation "F"=> (Real.exp (-(σ/2:ℝ)*(Club.length X C:ℝ)))
def Together (T H :ℕ) : Prop:= Club.reach X C q ≤ H ∧ ∀ i∈C.val, (X i).length ≤ T
abbrev litList (i:Fin (j+1)):= Minty.peck (Club.lowest X C) (Club.site X C q) (S.news C i) (U'.survey C i) T
def Visible (H:ℕ) : Prop:= Together X C q T H ∧ p.snd.val ∈ litList X C q S U' p.fst
-- Need Price ALL Y tall.E.In ν.Birth.Body.Root.Share.Price Runtime.Frame.State
local notation "fᵥ" i:max=> Real.exp (-(a/4)*(Club.reach X i q:ℝ))
local notation "f"=> (Real.exp (-(a/4)*(Φ:ℝ)))
local notation "A₀"=> ((Hℓ)*Λ w σ C)
local notation "g₁"=> (Real.exp (-(a/8)*(Φ:ℝ)))
-- general sigma ordinal. keep theorem methods available.
lemma trapeze {α:Type*}{β:α→Type*}(Fx:Sigma β→ℝ){t:α→ℝ}(ht:SumBudget t b)(he:∀i:α,SumBudget (fun j:β i=>Fx ⟨i,j⟩) (t i)): SumBudget Fx b:=by
    have hg u: 0 ≤ Fx u:= (he u.fst).1 u.snd
    apply budget_fiberwise Sigma.fst hg _ ht
    intro u s h
    have hx(i)(hi:i∈s): i∈ Set.range (Sigma.mk u):=by obtain ⟨i,v⟩:=i; obtain rfl:= h ⟨i,v⟩ hi; exact ⟨_,rfl⟩
    let s':=s.preimage (Sigma.mk u) (by exact (sigma_mk_injective).injOn)
    calc
      _ = ∑ i∈s'.image (Sigma.mk u),Fx i := Finset.sum_congr (by unfold s'; rw [image_preimage, Finset.filter_true_of_mem hx]) (fun _ _=>rfl)
      _ ≤ t u:=by rw [Finset.sum_image (g:=Sigma.mk u) (s:=s') (fun i hi j hj h=> sigma_mk_injective h)]; exact budget_sum (he u) _
lemma every (v:ℝ)(hv:0≤v) : SumBudget (fun _ : Fin (j+1)=>v) ((j+1:ℕ)*v):= budget_finite (fun _=>hv) (by simp)

local notation "M" i:max=> ( S.news C i )
local notation "x'"=> (Poly.toll w (Club.alliance X C))
include B hh hw hf
lemma brushes : SumBudget (fun i:Press.Palette X q S C => Poly.toll w (Club.alliance X C)*(Press.estate X C q S B i ρ|>.height ρ)) ((j+1:ℕ)*(A₀ *e*F*f)):=by
    have hx:0≤e:= budget_nonneg (B.care C (0:Et)).price
    have ht:0 ≤ A₀:= mul_nonneg (Real.exp_pos _).le (active X w hw ..).le
    apply trapeze _ (every _ (by positivity : 0≤ (A₀)*e*F*f)); intro i
    let u:= M i; let g j:=u.price a j; let g' j:=u.price (a/2) j; let D := Press.Mint X q C u
    let t:= A₀*(F*f); have ht₁:0≤ t:=by unfold t; positivity
    let d(j:D):= x'*( (ω ⟨i,j⟩ ρ).height ρ); let b(j:D):= (t*g j.val); have hp: SumBudget b (t*e):= budget_scale ht₁ (budget_pull (Subtype.val:D→u.Ty) (Subtype.val_injective («p»:=_)) ((B.care C i).price)) -- subtype inj.V
    refine budget_loosen (budget_mono hp (fun j=> ?_) (fun j=>?_)) (le_of_eq (by unfold t; ring));
    · let j₁ : Y := ⟨i,j⟩
      exact (Accumulate.pieces (Press.estate X C q S B · ρ) w hw ρ j₁).le
    apply le_trans (Width.house X C q S B ⟨i,j⟩ w hw (hf C) hh); rw [show ((Λ w σ C * Hℓ) * _ * F*f) =t*g' j.val from ?_];
    · exact mul_le_mul_of_nonneg_left (Minty.day u (half_le_self hh.waist.le) _) ht₁
    · unfold t g'; ring

end Width
end YM.QuadraticLocal.Earn
