import YM.Integration.FVA1Physical.TwoReset.ReadCopies
import YM.Integration.FVA1Physical.TwoReset.RepeatedAtoms
import YM.QuadraticLocal.Earn.Blend

/-!
# On every testing period: this *same* cover stencil is a rendering of
# the answer supplied by the compatible all-period Wilson procedure.

Thus the norm proof (on the physical period) uses the rendered independent
answer; not needing to call qlocal with a different torus label basis fitted to
the choice of that step's tests. More than identifying the sum at period-c
probes: this is for all the different covers of c. It can therefore be used
when transmitting this expression at the next step in the cover convention.
This file proves the aliasing identities with the Bulletin (Press). Bind
Press in turn to the independent prescription separately.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle
open Primitives.TwoWave Primitives.TwoWave.RealSlice QuadraticLocal.Aperture AllOrder.Ker
open Laurent AllOrder.Ink QuadraticLocal.Echo QuadraticLocal.Poetry
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {V ι α : Type} [DecidableEq V] {c f C : Side}
  {J : Passport f V} {R : Census V} {p : ℕ} {a b : ℝ}
variable (M : ι→Row J R G α) (Q : Ratio c f)
    (B : Press M p) (L : Press.Receipt M B a b)
    (d : ℝ) (S : Club M)
variable (h : c.val ∣ C.val) (t : α) (x : Stationary.Link G C) (i : ℕ)
local notation "Y" => Scene.letters M Q B L d
local notation "δ" => Pages c C
local notation "I" => Fin δ
local notation "D₁" => Club.site M S Q
local notation "Ω" => Club.lowest M S
local notation "W" => Club.roof M S Q
local notation "news" => B.news S
local notation "w₁" => convey (coverWin h) (Bunch.mapC D₁)
local notation "w" => (∏ j∈S.val,(M j).paint t)
local notation "f₀" j:max => (fun z : Site C => ∑' k,Lantern.gleam (((news j).leg k)) z w₁ (j:ℕ) i x)

include L in
private lemma stencil_at (j:Fin (p+1)) :
    ∑ z: Site C, (f₀ j) z = ∑ u:Fin δ,(f₀ j) (page h W u).val := by
  rw [pages h W (f₀ j)]
  symm
  apply Finset.sum_subset (subset_univ _)
  intro i' _ hi'
  refine (tsum_congr (g:=fun _=>0) ?_).trans tsum_zero
  intro l
  let A := (news j).leg l
  have he : ¬ (splitter h i')=W := fun he => hi' (posted ..|>.2 he)
  have hh := (L.care S j).pinned l
  by_cases hv : (j:ℕ) ≤ i
  · rw [Lantern.placed _ _ _ _ _ _ hv,Ink.Echo.voice (coverWin h),Spot.pixels D₁,coverWin_cut,
      if_neg (fun hx => he ((Spot.origin_key _ _ _ hh).1 hx).1),mul_zero]
  rw [Lantern.pre _ i' w₁ _ (lt_of_not_ge hv)]
  rfl

local notation "color" => Press.Mint M Q S
local notation "zℓ" j:max => Press.estate M S Q B L j d
local notation "image₁" u:max => (page h W u).val
local notation "spot" j:max k:max u:max => ( Lantern.gleam (((news j).leg k)) (image₁ u) w₁ ((j).val) i x )

-- filtered on the BASE period. This retains all the tested vertices,
-- including those with winding displacement to one of the copied marks.
private lemma missed (j:Fin (p+1)) (k:(news j).Ty) (u : Fin δ)
    (he : k∉Set.range (Subtype.val:(color (news j))→(news j).Ty)) :
    spot j k u = 0 := by
  let y := image₁ u
  have hp : (coverWin h).cut y = W := (posted ..).1 (page h W u).prop
  let A := (news j).leg k
  change Lantern.gleam A y w₁ _ _ _ = _
  by_cases hv : j.val ≤ i
  · rw [Lantern.placed A _ _ _ _ _ hv,Ink.Echo.voice (coverWin h), hp, Spot.pixels D₁]
    split
    next ht =>
      have h0 : A.atom.magnitude ≤ 0 := le_of_not_gt (fun h'=>
        he ⟨⟨k,⟨ht,h'⟩⟩,rfl⟩)
      have hz : Helmet.frame A.atom y=0 := funext (fun _ => Bloom.awaken _ _ _
        (le_antisymm h0 (Texture.mag_nonneg _)))
      rw [hz]; unfold Radial.jet; simp
    next => exact mul_zero _
  rw [Lantern.pre _ y w₁ _ (lt_of_not_ge hv)]; rfl

local notation "read₀" k:max u:max => (zℓ k).paint t * Complex.ofReal
  ((TwoReset.copy h (zℓ k) u).markReceipt i x)

private lemma artwork_value (j:Fin (p+1))(k: color (news j)) (u:Fin δ) :
    read₀ (⟨j,k⟩ : Press.Palette M Q B S) u =
      w * Complex.ofReal (spot j k.val u) := by
  let k' : Press.Palette M Q B S := ⟨j,k⟩
  let A := (news j).leg k.val
  let y := image₁ u
  let f := Helmet.frame A.atom y
  let V := TwoReset.copy h (zℓ k') u
  have hp : (coverWin h).cut y=W:=(posted ..).1 (page h W u).prop
  let r : ℕ:= i-j.val+A.r
  let b:= A.atom.budget d
  have hb : 0<b := Press.magnitude M S Q B k' d
  have hq : (Helmet.frame (Bloom.letdown A.atom b⁻¹) y) = b⁻¹ • f:= funext fun i => Bloom.grant ..
  have hr : V.markReceipt i x = b⁻¹ * (spot j k.val u) := by
    unfold Row.markReceipt
    by_cases hv : j.val ≤ i
    · have he : V.lamp.e ≤ i := hv
      rw [if_pos he, Lantern.placed _ _ _ _ _ _ hv,Ink.Echo.voice (coverWin h),hp,
        Spot.pixels D₁,if_pos (show ∀ r∈((news j).leg k.val).roots,D₁ r.2=W+wrap c r.1 from k.prop.1), mul_one]
      change Radial.jet (Helmet.frame (Bloom.letdown A.atom b⁻¹) y) r x=
        b⁻¹*Radial.jet f r x
      rw [hq]
      unfold Radial.jet
      rw [iteratedFDeriv_const_smul_apply ((Helmet.frameGrade A.atom y).smooth.of_le le_top)]
      simp only [_root_.smul_apply,smul_eq_mul]; ring
    rw [if_neg (fun hx : V.lamp.e ≤ i => hv hx), Lantern.pre _ _ _ _ (lt_of_not_ge hv),show
      ((0:Stationary.Link G C → ℝ) x)=0 from rfl,mul_zero]
  change (b:ℂ)* w * Complex.ofReal (V.markReceipt i x)=_
  rw [hr]; push_cast; field_simp [(Complex.ofReal_ne_zero.mpr hb.ne')]

variable (X : Layout G) (T : Finset Age) (φ : V→ℕ) {σ : ℝ} {order : ℕ}
local notation "all₁" => Scene.Texts M Q B
local notation "line" j:max u:max => reading h Y t x i (Sum.inr (⟨S,j⟩ : Press.Runway M Q B)) u
local notation "cp₁" u:max j:max => w * Complex.ofReal (∑' k, (spot j k u))
local notation "sender₁" => Poly.send (Club.alliance M S)
-- Separate statement for a particular actual Page and colour. Convergence follows
-- from the bill on the painter, not from claiming absolute summability for free.
variable [Fintype V]
variable (H : Air.Staff (Scene.letters M Q B L d) (fun i:Scene.Texts M Q B=> (Scene.letters M Q B L d i).paint t) φ σ order)
include H

private lemma panel (j:Fin (p+1)) (u:Fin δ) :
    HasSum (fun k:color (news j)=> line (⟨j,k⟩: Press.Palette M Q B S) u)
      (sender₁ (cp₁ u j)) := by
  -- `reads_page` holds with ANY blank layout because the discharge doesn't involve vacuum.
  let f k := reading h Y t x i k u
  have hR : Summable f:=
    (reads_page h Y φ (fun _ _=>Extra.Iteration.blank G _) ∅ t x i H u).summable -- layout constant?
  let inc (k : color (news j)) : all₁ := Sum.inr
    (⟨S,(⟨j,k⟩ : Press.Palette M Q B S)⟩ : Press.Runway M Q B)
  have hs : Summable (f∘inc):= hR.comp_injective (fun i k hy=> by
    have hh : (⟨j,i⟩:Press.Palette M Q B S) = ⟨j,k⟩ :=
      sigma_mk_injective (β:= fun u:Club M=> Press.Palette M Q B u) (i:=S) (Sum.inr_injective (α:=Solo.Watching M) (show inc i = inc k from hy))
    exact sigma_mk_injective (β:=fun i:Fin (p+1)=> color (news i)) (i:=j) hh)
  suffices hh : (∑' k:color (news j), (f ∘ inc) k) = sender₁ (cp₁ u j) by exact hh ▸ hs.hasSum
  apply Marker.Poly.ext
  intro m
  rw [Poly.share hs,Poly.part_send]
  have he (k : color (news j)): ((f ∘ inc) k).part m = if m=Club.alliance M S then
      w * Complex.ofReal (spot j k.val u) else 0 := by
    change (Poly.send (Club.alliance M S) (_ * _)).part m = _
    rw [Poly.part_send]; exact ite_congr rfl (fun _=>artwork_value M Q B L d S h t x i j k u) (fun _=>rfl)
  simp_rw [he]; split_ifs with H'
  · rw [tsum_mul_left,← Complex.ofReal_tsum]; congr 2
    refine Function.Injective.tsum_eq (g:=(Subtype.val : color (news j) → _)) (f:=fun k:(news j).Ty=> spot j k u) Subtype.val_injective (fun k hk=> ?_)
    by_contra hQ; apply hk; exact missed M Q B S h x i j k u hQ
  exact tsum_zero

private lemma page_club (u:Fin δ) : HasSum
    (fun j:Press.Palette M Q B S=> line j u)
    (∑ j:Fin (p+1),sender₁ (cp₁ u j)) := by
  let f (k:all₁) := reading h Y t x i k u
  have hf : Summable f:= (reads_page h Y φ (fun _ _=>Extra.Iteration.blank G _) ∅ t x i H u).summable
  let inc (j:Press.Palette M Q B S) : all₁ := Sum.inr (⟨S,j⟩: Press.Runway M Q B)
  have hz : Summable (f ∘ inc) := hf.comp_injective (fun i j hy=> (sigma_mk_injective ..)
    (Sum.inr_injective hy))
  have he := (hz.hasSum.sigma (fun j=> panel M Q B L d S h t x i φ H j u)).unique
    (hasSum_fintype _)
  exact he ▸ hz.hasSum

noncomputable def periodic_cluster : Poly R := Poly.send (Club.alliance M S)
    (Complex.ofReal (production (news) x w₁ i) * w)

local notation "ℙ" C:max => periodic_cluster M Q B C h t x i

lemma club_reading : HasSum (fun j:Press.Palette M Q B S=> ∑ u:Fin δ,line j u)
    (periodic_cluster M Q B S h t x i) := by
  let f (u:I)(j:Fin (p+1)):= (w * Complex.ofReal (∑' k,(spot j k u)))
  have H' : HasSum (fun j:Press.Palette M Q B S=> ∑ u:Fin δ,line j u)
      (∑ u: I, ∑ j:Fin (p+1),sender₁ (f u j)) := hasSum_sum (fun u _=>
        page_club M Q B L d S h t x i φ H u)
  convert H' using 1
  unfold periodic_cluster production
  rw [Complex.ofReal_sum,sum_mul, Finset.sum_comm (s:=univ) (t:= (univ:Finset (Fin (p+1))))]
  ext1 y
  simp_rw [Poly.part_send,Poly.part_sum,Poly.part_send]; split_ifs
  · apply Finset.sum_congr rfl
    intro j _
    rw [stencil_at M Q B L S h x i j,Complex.ofReal_sum,sum_mul]
    exact Finset.sum_congr rfl fun i _=> mul_comm _ _
  simp

end YM.Integration.FVA1Physical.TwoReset
