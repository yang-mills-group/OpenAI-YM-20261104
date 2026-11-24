import YM.QuadraticLocal.Shelter.Picnic
import YM.QuadraticLocal.Earn.Blend
import YM.QuadraticLocal.Earn.Theater
import YM.QuadraticLocal.Shelter.Shadows
/-!
# Operational Layout of the analytic side of mask moves

 Split into omitted (paid but not in comparison group) — also use negative
 at exactly that support; global field-independent passes (no mask shift needed,
 counts once even when empty); other visible (counted in the actual group).
 Doesn't depend on which germs certified seminar and θ bounds paid. Use whole
 analytic model for Step SUCCESS after planting the soap. Therefore need estimate
 not only on Aura payments for full but ALSO on `lost`/omitted (using length and
kernel budget/flat tails at the same λ). Comparison uses PRINT of Actual side,
 not a resized model chosen later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice Laurent RG Wilson Marker Ac
open Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Echo AllOrder AllOrder.Ink QuadraticLocal.Shelter
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι : Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {a e σ r b :ℝ} {k i' j u i h : ℕ}
variable (X:ι→Row P R G α) (C:Club X) (q:Ratio c n)
namespace Width
set_option quotPrecheck false
open Club Promote Press Accumulate Scene
variable (S:Press X j)(B:Press.Receipt X S a e)(p: Press.Palette X q S C)
local notation "P₁"=> P.coarser q
local notation "τ"=> (fun i:Club X=> Promote.front X i)
variable {D T H :ℕ}
variable (U' : Width.Viewer X S a T)(W:BudgetPoint) (Hp T₀:ℕ)
local notation "T₁"=> Width.fuelCuts q.count T Hp W.B T₀
variable (hT: Width.fuelCuts q.count T Hp W.B T₀)
local notation "E"=> (Press.placement X q S B)
abbrev Glass (T H:ℕ) := { i:Club X// Width.Together X i q T H }
def archive (T H:ℕ): Terrain (Glass X q T H) R:= ⟨Club.alliance X ∘ Subtype.val, Promote.front X ∘ Subtype.val, fun i=> Club.earn X i.val _ (Club.attends X i.val (Club.lowest X i.val)) ((Club.troops X i.val (Club.lowest X i.val)).binder.east)⟩
local notation "T₀'"=> archive X q T Hp
local notation "H₁"=> Glass X q T Hp
abbrev Seen (i:Glass X q T Hp):= ↥(Width.audience X i.val q S U' Hp)
abbrev Inn:= Σ i: Glass X q T Hp, Seen X q S U' Hp i
local notation "Σ'"=> Press.Runway X q S
local notation "p₁"=> Seen X q S U' Hp
local notation "T₁'"=> Inn X q S U' Hp
abbrev aisle (i: Inn X q S U' Hp) : Press.Runway X q S:=⟨i.1.val,i.2.val⟩
local notation "Φ" => (aisle X q S U' Hp)
local notation "Sp"=> (Width.Shaded X q S U' Hp)
lemma assigned : Injective (aisle X q S U' Hp):=by
    rintro ⟨x,i⟩ ⟨y,j⟩ h; obtain rfl:= (show x=y from Subtype.ext (congr_arg Sigma.fst h)); obtain rfl:= (show i=j from Subtype.ext (Sigma.mk.inj_iff.mp h|>.2 |>.eq)); rfl
lemma complete (i: Press.Runway X q S) : i∈ Set.range (aisle X q S U' Hp) ↔ Visible X i.fst q S i.snd U' Hp:=by
   constructor
   · rintro ⟨i,rfl⟩; exact (ticket X i.fst.val ..).1 i.snd.prop
   intro hv; exact ⟨(⟨⟨i.fst,hv.1⟩,⟨i.snd,(ticket ..).2 hv⟩⟩:Inn X q S U' Hp),rfl⟩
noncomputable def exit : (Inn X q S U' Hp ⊕ Width.Shaded X q S U' Hp) ≃ Press.Runway X q S:=by
    refine Equiv.ofBijective (Sum.elim Φ Subtype.val) ⟨?_,fun i=>?_⟩
    · rintro (x|x) (y|y) h; exact congr_arg Sum.inl (assigned X q S U' Hp h); exact (y.prop ((complete X q S U' Hp y.val).1 ⟨x,h⟩)).elim; exact (x.prop ((complete X q S U' Hp x.val).1 ⟨y,h.symm⟩)).elim; exact congr_arg Sum.inr (Subtype.ext h)
    by_cases h:i∈ Set.range Φ; obtain ⟨i,rfl⟩:=h; exact ⟨Sum.inl i, rfl⟩; exact ⟨.inr (⟨i,mt (complete X q S U' Hp i).2 h⟩:Sp),rfl⟩
variable (ρ g:ℝ)
local notation "Art"=> (Scene.letters X q S B ρ)
abbrev treasured := rendered (Scene.letters X q S B ρ) W g
abbrev quiet := rendered (Solo.capsules q X) W g
abbrev whole := rendered (Press.placement X q S B ρ) W g
abbrev famous := rendered (Press.placement X q S B ρ ∘ Width.aisle X q S U' Hp) W g
abbrev imagined := rendered (Press.placement X q S B ρ ∘ (Subtype.val : Width.Shaded X q S U' Hp→Press.Runway X q S)) W g
local notation "Y*"=> Width.treasured X q S B W ρ g
local notation "F₀"=> Width.famous X q S B U' W Hp ρ g
local notation "Q'"=> Width.quiet X q W g
local notation "R0"=> Width.whole X q S B W ρ g
local notation "H0"=> Width.imagined X q S B U' W Hp ρ g
local notation "V0"=> archive X q T Hp
-- Deck. `region` includes root and stencil fix.
def concerts : Deck (Width.famous X q S B U' W Hp ρ g) (archive X q T Hp) T₀ (Width.Seen X q S U' Hp) where
   enrol:= Equiv.refl _
   calls _:= rfl
   region i:= Width.framing X i.fst.val q S B _ U' hT ((ticket ..).1 i.snd.prop) -- maybe order h
local notation "ArtD"=> Width.concerts X q S B U' W Hp T₀ hT ρ g -- implicit T₀? #check
variable (w:V→ℝ)(x:α)(v:Config G c)
lemma realizes (i:Glass X q T Hp) : (ArtD).white i x v= ∑ k∈ Width.audience X i.val q S U' Hp,((Press.estate X i.val q S B k ρ).nominal g x v):= by
   unfold Deck.white; exact Finset.sum_coe_sort (f:=fun k=>((Press.estate X i.val q S B k ρ).nominal g x v)) _
variable {η:ℝ}
variable (hw:∀ i,0<w i) (hL:(Width.treasured X q S B W ρ g).Paid w W.B η b)
include hL
lemma acquaintances : (R0).Paid w W.B η b:= Lamps.summonPaid (Y*) w Sum.inr Sum.inr_injective hL
lemma famous_paid : (F₀).Paid w W.B η b:=by
    exact (R0).summonPaid w Φ (assigned X q S U' Hp) (acquaintances X q S B W ρ g w hL)
lemma quiet_paid : (Width.quiet X q W g).Paid w W.B η b:= (Y*).summonPaid w Sum.inl Sum.inl_injective hL
include hw
lemma portions (hη:0≤η) : (Y*).log x v=(Q').log x v+(F₀).log x v+(H0).log x v:=by
    let X':= Y*; let VID:= R0; rw [add_assoc ((Q').log x v)] -- orientation want (. + (. +.)) use add_assoc

    have hv : (Y*).log x v= (Q').log x v+ (R0).log x v:=by apply Lamps.separate (Y*) (Equiv.refl (Scene.Texts X q S)) Sum.inl Sum.inr (fun _=> rfl) (fun _=> rfl) x v (hL.sums hη hw x v)
    rw [hv]; congr 1; exact Lamps.separate (R0) (Width.exit X q S U' Hp) Φ Subtype.val (fun _=>rfl) (fun _=>rfl) x v ((acquaintances X q S B W ρ g w hL).sums hη hw x v)
end Width
end YM.QuadraticLocal.Earn
