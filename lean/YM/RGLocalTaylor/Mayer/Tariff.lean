import YM.RGLocalTaylor.Mayer.Decor

/-!
# Head-moment Taylor tariffs

Bound at the chosen *whole* Taylor order, relative to the full incoming hit
budget. No absolute volume factors or powers of cut radii refunded elsewhere.
`scale` is the Cauchy radius in the Taylor variable; each additional use of a
log exponential *within a Head* also costs it. Works as well when preparing
marked comparisons, the factors NOT selected are paid at their actual support
prices here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt

namespace Mayer
variable {ρ discount θ K α uJ vJ e : ℝ} {M : ℕ} {p z : Molecule S}
    {Ξ : Utopia H j v d r C' χ} (h : Awning H Ξ A b discount e uJ vJ k l)
    (he : Approved K θ j M) (ht : Q.goal L s ≤ K) (hw:0 ≤ ρ) (hr:ρ*Q.goal L s≤1)
    {f' : Head S→ Insert T} {w : Head S→ℝ} (hb : ∀ i∈p \ z, EstFactor Ξ i (f' i) A (w i) α) (hf : ∀ i∈p \ z, 0≤ w i)
    (hF:∀ i∈p \ z,Fits H (f' i) (H.supportP i) j)
    (hp:z⊆p) (hL:∀ i∈z,Exponential i)
    (hz : (M+4:ℝ)*r≤α)

def tariff (Ξ : Utopia H j v d r C' χ) (p : Molecule S) (θ:ℝ) (u : Decors z M) (w : Head S→ℝ) :=
  (∏ i∈p \ z, w i) * ∏ i:↥z, θ*(Ξ.tag i.val)^((u i).val+1)

def hitFace (Ξ : Utopia H j v d r C' χ) (p z : Molecule S) (w : Head S→ℝ) :=
  (∏ i∈p \ z, w i) * ∏ i∈z, Ξ.tag i

include h he ht hb hf hp hL hz
omit ht hp hL h hb hz in
lemma tariff_nonneg (u : Decors z M) : 0≤ tariff Ξ p θ u w :=
   mul_nonneg (prod_nonneg hf) (prod_nonneg fun _ _=> mul_nonneg (zero_le_one.trans he.nonneg) (pow_nonneg (Ξ.tagged _) _))

omit ht he hp hL h hb hz in
lemma hitFace_nonneg (Ξ : Utopia H j v d r C' χ) : 0≤ hitFace Ξ p z w :=
  mul_nonneg (prod_nonneg hf) (prod_nonneg fun i _=> Ξ.tagged i)

omit hf in
lemma prizes (ha : 1 ≤ α) (hx: troupe T R Q.halo (radiusB s) p) (u:Decors z M) :
    CoveredAt Ξ (tagged H p f' u) p A (tariff Ξ p θ u w) α := by
  let W i:= if hj : i∈z then θ * (Ξ.tag i)^((u ⟨i,hj⟩).val+1) else w i
  have hw (i) (hi:i∈p): EstFactor Ξ i (payload H p f' u i) A (W i) α := by
    unfold W payload; split; next h'=> exact (kernel_price h he ht (own p) (u ⟨i,h'⟩) (hL i h')).weaken le_rfl hz
    next h=> exact hb i (mem_sdiff.mpr ⟨hi,h⟩)
  have h0 : tariff Ξ p θ u w=∏ i∈p, W i:= by
    rw [← prod_sdiff hp]; unfold tariff; refine congr_arg₂ (·*·) (prod_congr rfl fun i hi=> (by unfold W; rw [dif_neg ((mem_sdiff.mp hi).2)])) ?_
    rw [← prod_attach z]; exact prod_congr rfl (fun i _=> by unfold W; rw [dif_pos i.property])
  rw [h0]; exact EstFactor.product (zero_le_one.trans ha) hx hw

include hr hw
omit ht hp h hb hz in
lemma price_cauchy (u:Decors z M):
    tariff Ξ p θ u w * ρ ^ decorOrder u ≤ hitFace Ξ p z w * (θ*ρ)^z.card := by
  unfold decorOrder tariff hitFace
  rw [← prod_pow_eq_pow_sum, mul_assoc, mul_assoc (∏ i∈p \ z, w i)]
  refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg hf)
  rw [← prod_mul_distrib]
  have hz : (θ*ρ)^z.card=∏ _i:↥z,θ*ρ := by rw [prod_const]; simp
  rw [← prod_attach z,hz]; change ∏ i:↥z, _ ≤ (∏ i:↥z, Ξ.tag i.val)* ∏ _i:↥z, θ*ρ
  rw [← prod_mul_distrib]
  refine prod_le_prod ?_ ?_
  · rintro ⟨i,hi⟩ _; exact mul_nonneg (mul_nonneg (zero_le_one.trans he.nonneg) (pow_nonneg (Ξ.tagged _) _)) (pow_nonneg hw _)
  intro i _; let t := Ξ.tag i.val; let k:= (u i).val
  have ht:0 ≤ t:= Ξ.tagged _; have hζ:t * ρ ≤ 1:= by
    rw [mul_comm]; exact (mul_le_mul_of_nonneg_left (tag_small Ξ (hL i.val i.property)) hw).trans hr
  change θ*t^(k+1)*ρ^(k+1) ≤ t*(θ*ρ)
  rw [mul_assoc, ← mul_pow,pow_succ',show t*(θ*ρ)=θ*(t*ρ) by ring]; exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_right (mul_nonneg ht hw) (pow_le_one₀ (mul_nonneg ht hw) hζ)) (zero_le_one.trans he.nonneg)

omit hw
-- pricing including the actual speed constants.
variable {N : Captain H j C' d v Y A b r B q n χ} (hn : N.conduit=Ξ) (hρ: 1≤ρ)
include hn hF hρ
set_option quotPrecheck false
local notation "ι" => (discount * Ξ.rad) ^ (blaze p).card
local notation "f₀" => speedBill e uJ α j
lemma cluster_cost {V:Config G c} (h' : (roster p).flags=∅) (ha : 1 ≤ α) (hX : authorized H p) (hy:Healthy (Pressure.temp s) (H.unionP p) V)
    (u:Decors z M)(m:ℕ)(hM:m ≤ decorOrder u) :
    Ore V ((tagged H p f' u).onLog H χ p) v ((ρ^m)⁻¹ *
      (f₀ * (hitFace Ξ p z w * (θ*ρ)^z.card) * (1+H.shapeW p)^(l+j) * ι)) j := by
  intro E _ _ _ U x hx hu
  subst Ξ; set Ξ := N.conduit
  have he':0≤tariff Ξ p θ u w:= tariff_nonneg he hf u
  have hh:= h.priced (prizes h he ht hb hp hL hz ha hX.2 u) he' ha (fits_tagged H f' hF u) h' V hy E U x hx hu
  apply hh.climb _ le_rfl
  let v':ℝ:= 1+H.shapeW p; have hv':0≤ v':= add_nonneg zero_le_one (H.positive_volume p)
  have hf' : 0≤ f₀:= mul_nonneg h.earn (by have ht:= h.bSc; positivity)
  have hw': 0≤ (discount * Ξ.rad) ^ (blaze p).card := pow_nonneg (mul_nonneg h.nonneg Ξ.awake) _
  have hp' : 0<ρ:= zero_lt_one.trans_le hρ
  have hx := price_cauchy (Ξ:=N.conduit) he hp'.le hr hf hL u
  rw [inv_mul_eq_div,le_div_iff₀ (pow_pos hp' _)]
  calc
    _ = f₀*(tariff Ξ p θ u w * ρ^m)*v'^(l+j)* (discount * Ξ.rad) ^ (blaze p).card :=by unfold Ξ v'; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hρ hM) he').trans hx) hf') (pow_nonneg hv' _)) hw'

end Mayer
end YM.RGLocalTaylor
