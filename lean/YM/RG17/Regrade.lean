import YM.RG17.Balance
import YM.RG12.Canonical.Before

/-!
# Coarse inverse buys genuine engineering columns

Cuts cost vector (-j) built **using this same observer chart**
(from RG12). All-filter event, not existence on a different sublimit.
Coefficients in coupling copies for physical framing paid RateLE *only*,
enough for spatial budgets. Not a Phi (poly Lambda) ticket.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter Spec Extraction Table OPE OPE.Orbits OPE.Columns
open RG12
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}
    (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (L:Layout F)
set_option quotPrecheck false
local notation "B" => F.sector.derivatives
local notation "ρ" => OPE.run
local notation "m"=> L.level

/-- This is a condition on calendar/scheme conversions not needed by located itself. -/
def ShiftBack : Prop := ∀ d:ℕ, RateLE home ρ (fun r=> (L.shift d r).symm.toContinuousLinearEquiv.toContinuousLinearMap) 0

lemma pieces_master (h:Reach C L.level) (hp:ShiftBack L) (d:ℕ) (v:ℝ→ S.Field d) (c:ℝ)
    (ht:RateLE home ρ v (-(d:ℝ)+c)):∃ u:ℝ→ C.label d, RateLE home ρ u c ∧ ∀ᶠ r in home, master L d r (u r)=v r:=by
   letI := L.notbot
   let x(r:ℝ):ℂ:= ↑(C.S.a (m r)^d:ℝ)
   have hx r:x r≠0:=by unfold x; exact_mod_cast pow_ne_zero d (C.S.a_pos _).ne'
   let w(r:ℝ):= (x r)⁻¹ • v r
   have hh(r:ℝ):=RG12.weak_inside F.room.cutoff L.observes S d (m r)
   choose! p he hb using fun r (a:C.ref d ≤ m r)=> hh r a (w r)
   let M(r:ℝ):= (L.shift d r).symm.toContinuousLinearEquiv.toContinuousLinearMap
   refine ⟨fun r=>M r (p r),?_,?_⟩; swap
   · filter_upwards [h.growing.eventually_ge_atTop (C.ref d)] with i hi
     change engineering L.charts d (m i) ((L.shift d i) ((L.shift d i).symm (p i)))= v i
     rw [LinearEquiv.apply_symm_apply,engineering_at,he _ hi]
     change x i • ((x i)⁻¹ • v i)=_
     rw [smul_smul,mul_inv_cancel₀ (hx i), one_smul]
   have hz: RateLE home ρ w c := by
      refine (?_ : RateLE home ρ (fun r=> (x r)⁻¹) (d:ℝ)).smul ht|>.mono (le_of_eq (by linarith))
      have hq:=((lengthLevels L h).power d).inv.pays ageLarge
      simp only [mul_neg,mul_one,neg_neg] at hq
      exact hq.transfer (Eventually.of_forall fun r=> by unfold x; push_cast; simp)
   let b:= ((C.labels.level d).extra+1:ℕ)
   let Q:= (S.representative d).toContinuousLinearMap
   have hq : RateLE home ρ (fun r=> Q (w r)) c:= by simpa only [zero_add] using! (RateLE.const Q ageLarge).bil hz (u:=fun r=> Q (w r)) (Eventually.of_forall fun r=> Q.le_opNorm _)
   have hf:RateLE home ρ p c:= by
       have hr:=((juice_rate_seq C h.growing h.nearby).pays ageLarge).mul ((RateLE.const (b:ℝ) ageLarge).mul hq.norm); rw [zero_add,zero_add] at hr
       refine RateLE.of_norm_le hr ?_
       filter_upwards [h.growing.eventually_ge_atTop (C.ref d)] with i hi
       exact (norm_le_mass ..).trans ((hb i hi).trans (mul_le_mul_of_nonneg_left (mass_le_norm ..) (zero_le_one.trans (juice_pos ..))))
   simpa only [zero_add] using! (hp d).bil hf (u:=fun r=> M r (p r)) (Eventually.of_forall fun r=> (M r).le_opNorm _)

lemma regrade (h:Reach C L.level) (hp:ShiftBack L) (d:ℕ) (v:ℝ→ S.Field d) (c:ℝ)
    (hr:∀ j:Fin (d+1), RateLE home ρ (fun r=> P.cutTest j d (v r)) (-(j.val:ℝ)+c)) :
    ∃ p : (j:Fin (d+1))→ ℝ→ C.label j, (∀ j,RateLE home ρ (p j) c) ∧
       ∀ᶠ r in home, v r=∑ j:Fin (d+1),F.sector.derivatives.rise (Nat.le_of_lt_succ j.isLt) (master L j.val r (p j r)):=by
   choose p h₁ h₂ using fun (j:Fin (d+1))=> pieces_master L h hp j.val _ c (hr j)
   refine ⟨p,h₁,(eventually_all.mpr h₂).mono fun r hr=>?_⟩
   simp_rw [hr]
   exact ((P.reconstruct d d le_rfl (v r)).trans (F.sector.derivatives.arrival P.continuum.laws.toSymmetric P.lifts _)).symm

lemma byGrade (h:Reach C L.level) (hp:ShiftBack L)
    (u:∀ᶠ r in home,L.shift 0 r (C.labels.level 0).e0=(C.labels.level 0).e0)
    (hu:∀ d,∀ᶠ r in home,L.frame d r ((Maxwell.freeTable C.labels).unit d)= S.unit d)
    (hb:∀ {d e : ℕ} (he:d ≤ e), ∀ᶠ r in home,∀ v,
      L.frame e r ((Maxwell.Free.scheme C.labels).rise he v)= F.sector.derivatives.rise he (L.frame d r v))
    (hx:∀ d,RateLE home OPE.run (fun r=> (L.shift d r).toContinuousLinearEquiv.toContinuousLinearMap) 0)
    (hy:∀ d,∀ v:Free C d,∀ j:Fin (d+1),RateLE home ρ (fun r=>P.cutTest j.val d (L.frame d r v)) (-(j.val:ℝ))) : Located L := ⟨h,u,hu,hb,hx,fun d v => regrade P L h hp d _ 0 (fun i=>by simpa only [add_zero] using hy d v i)⟩
end YM.RG17
