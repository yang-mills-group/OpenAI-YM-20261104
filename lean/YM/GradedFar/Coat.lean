import YM.GradedFar.Ambient
import YM.GradedFar.ForkLedger
/-!
# Specifying/using QScale's basic physical field expense (G.2)

Uses the actor basis through each cap; `Cast.lift` multiplies the row of weight j by
r^j (and the slots grade preserving). The needed money is polynomial upper bounds on Z and inverse
(Z as in 1423). `Coat` spells this hypothesis directly on a pair of linear maps with usual operator norm
(in the precise Sec norm convention of this development). Pull every stretched length s with
HR truth through this, not substituting matching costs on some chosen annular profile. No
filtration preservation assumption needed once we have those estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Filter Finset Function Set Spec Table Extraction OPE OPE.Orbits OPE.Log
open Trace.Pilot PhysMS
open XSpace XSpace.Normalize FVA2.GradedFar
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P:ℝ→tower S)
def Z (d:ℕ)(r:ℝ) := ((columns G d).toLinearMap ∘ₗ (assign P r d).symm.toLinearMap ∘ₗ Cast.lift F R d r).toContinuousLinearMap
def Zopp (d:ℕ)(r:ℝ) := row ((Cast.lift F R d r⁻¹) ∘ₗ (assign P r d).toLinearMap)
def Coat (d:ℕ) := ∃ k:ℕ, ∃ b:ℝ,0≤b ∧ ∀ᶠ r in trail, ‖Z F R P d r‖ + ‖Zopp F R P d r‖ ≤ b*badge r^k

variable {h:ℕ}
lemma inverse_Z {r:ℝ}(hr:0<r)(p : S.Field h) : Zopp F R P h r (Z F R P h r p)=p:= by
  change Cast.lift F R h r⁻¹ (assign P r h ((columns G h).symm (columns G h ((assign P r h).symm _)))) = _
  rw [LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply,← LinearMap.comp_apply,
    Cast.lift_mul, inv_mul_cancel₀ hr.ne',Cast.lift_one]
lemma Z_width (u:Sec G h)(r:ℝ):
    ‖Cast.lift F R h r⁻¹ (assign P r h u)‖ ≤ ‖Zopp F R P h r‖ * width u := by
  exact row_le ((Cast.lift F R h r⁻¹) ∘ₗ (assign P r h).toLinearMap) u
-- define actual basis coefficients & transformed fields; reusability all ℓ & Sall. not synthetic Norm.
def coatRead (r:ℝ) (p:Cast F R h) (u:Sec G h):= Cast.judge F R p (assign P r h u)
def coatSpend (r:ℝ) (p:Cast F R h) (u:Sec G h):= Cast.judge F R p (Cast.lift F R h r⁻¹ (assign P r h u))
lemma coasting {r:ℝ} (hr:0<r) (p:Cast F R h) (u:Sec G h): coatRead F R P r p u =
    (r:ℂ)^Cast.cost F R p*coatSpend F R P r p u:= by
  unfold coatSpend; rw [Cast.lifted_grade, Complex.ofReal_inv, inv_pow, ← mul_assoc, mul_inv_cancel₀, one_mul]; rfl
  exact pow_ne_zero _ (by exact_mod_cast hr.ne')
lemma earnsRead (Hw:Coat F R P h)(p:Cast F R h):∃ k:ℕ,∃ b:ℝ,0≤b ∧
    ∀ᶠ r in trail, ∀ u:Sec G h, width u ≤ 1 → ‖coatRead F R P r p u‖ ≤ b*badge r^k*r^Cast.cost F R p:=by
  obtain ⟨k,b,hb,h⟩:= Hw; let B:= (Cast.judge F R p).toContinuousLinearMap
  refine ⟨k,‖B‖*b,mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) hb,?_⟩
  filter_upwards [h,self_mem_nhdsWithin] with r hr (hp:0<r) u hu
  have hQ:=Z_width F R P u r; replace hQ:=hQ.trans ((mul_le_mul_of_nonneg_left hu (ContinuousLinearMap.opNorm_nonneg _)).trans ((mul_one _).le.trans
    ((le_add_of_nonneg_left (ContinuousLinearMap.opNorm_nonneg _)).trans hr)))
  rw [coasting F R P hp,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hp.le]
  exact (mul_le_mul_of_nonneg_left ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left hQ (ContinuousLinearMap.opNorm_nonneg _)))
    (by positivity : 0 ≤ r^Cast.cost F R p)).trans_eq (by ring)

lemma earnsBackward (Hw:Coat F R P h)(p:Cast F R h):∃ k:ℕ,∃ b:ℝ,0≤b ∧
    ∀ᶠ r in trail,width ((assign P r h).symm (Cast.push F R p)) ≤ b*badge r^k*(r^Cast.cost F R p)⁻¹:=by
  obtain ⟨k,b,hb,hQ⟩:= Hw; let c:=‖Cast.push F R p‖
  refine ⟨k,b*c,mul_nonneg hb (norm_nonneg _),?_⟩; filter_upwards [hQ,self_mem_nhdsWithin] with r hr (hp:0<r)
  have price:= (Z F R P h r).le_opNorm (Cast.push F R p); replace price:=price.trans (mul_le_mul_of_nonneg_right
    ((le_add_of_nonneg_right (norm_nonneg _)).trans hr) (norm_nonneg _));
  change width ((assign P r h).symm (Cast.lift F R h r (Cast.push F R p))) ≤ b*badge r^k*c at price
  rw [Cast.lift_apply, map_smul, width_smul, norm_pow, Complex.norm_real,Real.norm_of_nonneg hp.le] at price
  rw [show b*c*badge r^k= b*badge r^k*c by ring,← div_eq_mul_inv]; exact
    (le_div_iff₀ (pow_pos hp _)).mpr (by rw [mul_comm]; exact price)

-- earn several radii. Generic version `Scaled` carries exact hh and charge W. Avoid using powers of g (yet).
variable {A B:Type*} (α:Filter A) {U:A→B→Prop} {L W r:A→B→ℝ}
-- This is varying radius used by different slots j after raising,
-- not the perturbative-order log. Keep ∀ eventually even across arbitrary Valid moves.
def Bedroom (U:A→B→Prop)(L r:A→B→ℝ): Prop :=
    (∀ T:ℝ→Prop,(∀ᶠ t:ℝ in trail,T t) → ∀ᶠ a in α,∀ z, U a z→ T (r a z)) ∧
    ∀ᶠ a in α,∀ z, U a z → 1≤badge (r a z) ∧ badge (r a z) ≤ L a z
variable {α}
lemma Bedroom.logs (H:Bedroom α U L r) :∀ᶠ a in α,∀ z,U a z→1≤L a z:=
  H.2.mono (fun _ h z he=> le_trans (h z he).1 (h z he).2)
lemma Bedroom.pos (H:Bedroom α U L r):∀ᶠ a in α, ∀ z,U a z → 0< r a z:= H.1 _ self_mem_nhdsWithin
lemma earnFrom (H:Bedroom α U L r) {u:A→B→Sec G h} (p:Cast F R h)
    (Hw:Coat F R P h) (hu:∀ᶠ a in α,∀ z, U a z → width (u a z) ≤ 1): Sold α U L
    (fun a z=> r a z^Cast.cost F R p) (fun a z=> coatRead F R P (r a z) p (u a z)):=by
  obtain ⟨k,b,hb,h⟩:= earnsRead F R P Hw p; refine ⟨k,b,hb,?_⟩
  filter_upwards [H.1 _ h,H.2,H.pos,hu] with a ha hx hr h z hz
  obtain ⟨hl,hL⟩:=hx z hz; have hP:= hr z hz; refine (ha z hz _ (h z hz)).trans ?_; gcongr
lemma earnBack (H:Bedroom α U L r) (p:Cast F R h) (Hw:Coat F R P h): Sold α U L
    (fun a z=> (r a z^Cast.cost F R p)⁻¹) (fun a z=> columns G h ((assign P (r a z) h).symm (Cast.push F R p))) := by
  obtain ⟨k,b,hb,hQ⟩:= earnsBackward F R P Hw p; refine ⟨k,b,hb,?_⟩
  filter_upwards [H.1 _ hQ,H.2,H.pos] with a ha hx hr z hz
  obtain ⟨hl,hL⟩:=hx z hz; have hP:= hr z hz; refine (ha z hz).trans ?_; gcongr
end YM.Integration.GradedFar.Fork
