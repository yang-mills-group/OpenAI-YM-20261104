import YM.GapsContact.Power.Moss

/-!
# Geometric bands in annular transfers and operator pairs
-/

set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Power
open Function Filter Set MeasureTheory Metric Extraction Climb Spec Ascent
open Trace Trace.Terrace Trace.Pilot MergeProof.East Next.UVStress Trace.Over
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{C: Family G} {d e n:ℕ}{r s x a ε c R A p:ℝ}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book}
variable (F:Final C f S) {H:(Climb.Bel C.book).Hierarchy}{Z:Trace.Terrace.Arch C}
variable (hG:G.Simple) (Y:Bliss F 𝓛 Z H)
set_option quotPrecheck false
local notation "I" => F.phase.transport.injection
local notation "T" => F.sector.derivatives
local notation "Hh" => F.room.kernel
local notation "O" => F.phase.transport.rights

variable (q Q:ℝ→ℝ) (hq:∀ r,0≤ q r)(hq':AntitoneOn q (Ioc 0 R))(hr:1<r)
variable (hp:0 ≤ p)
lemma incline (ha:x∈ Ioc 0 R)(hr:1 < r): x*r⁻¹ ∈ Ioc (0:ℝ) x∧ x*r⁻¹ ∈ Ioc (0:ℝ) R:=by
  have he:0<r:=zero_lt_one.trans hr; have ht:x*r⁻¹ ∈ Ioc 0 x:=⟨mul_pos ha.1 (inv_pos.mpr he),mul_le_of_le_one_right ha.1.le ((inv_le_one₀ he).2 hr.le)⟩; exact ⟨ht,ht.1,ht.2.trans ha.2⟩
lemma past (x) (hs:0 < s)(hr:1 < r):∃ i:ℕ, x/r^i ≤ s:=
  ((tendsto_const_nhds (x:=x)|>.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hr)).eventually (ge_mem_nhds hs)).exists

lemma exp_pay (hr:1<r) (hp:0 ≤ p) (hh: a∈ Ioc 0 x): 1 ≤ (x/a)^p∧1≤ r^p:=
   ⟨Real.one_le_rpow ((one_le_div hh.1).2 hh.2) hp,Real.one_le_rpow hr.le hp⟩

include hq hq' hr hp
lemma through_up (H:∀ s∈Ioc 0 R, q (s*r⁻¹) ≤ r^p * q s): ∀ x∈ Ioc 0 R, ∀ a∈Ioc 0 x,q a≤ (r^p)*(x/a)^p*q x:=by
  suffices he:∀ i:ℕ,∀ x∈Ioc 0 R,∀ a∈Ioc 0 x, x/r^i ≤ a → q a≤ (r^p)*(x/a)^p*q x by intro x hx a ha; exact he _ x hx a ha (past x ha.1 hr|>.choose_spec)
  intro i; induction i with
  | zero=> rintro x hx a ha hu; rw [pow_zero,div_one] at hu; obtain rfl:= hu.antisymm ha.2; exact le_mul_of_one_le_left (hq _) (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hr.le hp) (exp_pay hr hp ha).1)
  | succ i ih=>
    intro x hx a ha he; have hA:a∈ Ioc 0 R:=⟨ha.1,ha.2.trans hx.2⟩; have he':= incline hx hr; let V:=x*r⁻¹; have hV:0 < V:= he'.1.1; have hz:=H x hx
    by_cases ht:V≤a
    · apply ((hq' he'.2 hA ht).trans hz).trans; exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (Real.rpow_nonneg (zero_le_one.trans hr.le) _) (exp_pay hr hp ha|>.1)) (hq _)
    refine (ih V he'.2 a ⟨ha.1,le_of_not_ge ht⟩ ?_).trans ((mul_le_mul_of_nonneg_left hz (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hr.le) _) (Real.rpow_nonneg (div_pos hV ha.1|>.le) _))).trans_eq ?_)
    · change (x/r)/r^i≤a; rw [div_div, ← pow_succ' r]; exact he
    have hh: V/a*r=x/a:=by have hy:= ha.1.ne'; have he: r≠0:=(zero_lt_one.trans hr).ne'; unfold V; field_simp
    rw [← mul_assoc, mul_assoc (r^p),← Real.mul_rpow (div_pos hV ha.1).le (zero_le_one.trans hr.le),hh]
lemma through_down (H:∀ s∈Ioc 0 R,r^p * q s ≤ q (s*r⁻¹)) : ∀ x∈ Ioc 0 R, ∀ a∈Ioc 0 x,(x/a)^p*q x ≤ r^p*q a:=by
  suffices he:∀ i:ℕ,∀ x∈Ioc 0 R,∀ a∈Ioc 0 x, x/r^i ≤ a → (x/a)^p*q x ≤r^p*q a by intro x hx a ha; exact he _ x hx a ha (past x ha.1 hr|>.choose_spec)
  intro i; induction i with
  | zero=> rintro x hx a ha hu; rw [pow_zero,div_one] at hu; obtain rfl:= hu.antisymm ha.2; rw [div_self hx.1.ne',Real.one_rpow]; exact mul_le_mul_of_nonneg_right (Real.one_le_rpow hr.le hp) (hq _)
  | succ i ih=>
    intro x hx a ha he; have hA:a∈ Ioc 0 R:=⟨ha.1,ha.2.trans hx.2⟩; have he':= incline hx hr; let V:=x*r⁻¹; have hV:0 < V:= he'.1.1; have hz:=H x hx; have hr':0<r:=zero_lt_one.trans hr
    by_cases ht:V≤a
    · have hh: x/a≤r:= (div_le_iff₀ ha.1).2 (by rw [mul_comm r]; exact (div_le_iff₀ hr').1 ht)
      exact mul_le_mul (Real.rpow_le_rpow (div_pos hx.1 ha.1|>.le) hh hp) (hq' hA hx ha.2) (hq _) (Real.rpow_nonneg hr'.le _)
    have hh: V/a*r=x/a:=by have hy:= ha.1.ne'; have he: r≠0:=hr'.ne'; unfold V; field_simp
    refine le_trans ?_ (ih V he'.2 a ⟨ha.1,le_of_not_ge ht⟩ ?_); swap; · change (x/r)/r^i≤a; rw [div_div,← pow_succ']; exact he
    rw [←hh,Real.mul_rpow (div_pos hV ha.1|>.le) hr'.le,mul_assoc]; exact mul_le_mul_of_nonneg_left hz (Real.rpow_nonneg (div_pos hV ha.1|>.le) _)

-- open induction for local-comparator uniform equivalence at variable spacings
omit hq' hp hq
include hr
lemma persistence (B:ℝ→Prop) (hu:0<R) (hb:∀ x∈Icc (R*r⁻¹) R,B x)(hp:∀ x∈Ioc 0 R, B x→B (x*r⁻¹)) : ∀ x∈Ioc 0 R,B x:=by
  have hh:∀ i:ℕ,∀ x∈ Ioc 0 R,R/r^i≤x→ B x:=by
    have hr':0<r:=zero_lt_one.trans hr
    have hs : R*r⁻¹ ≤ R:= (incline ⟨hu,le_refl R⟩ hr|>.1.2)
    intro i; induction i with
    | zero=> rintro x hx h; rw [pow_zero,div_one] at h; exact hb x ⟨hs.trans h,hx.2⟩
    | succ i ih=>
      intro x hx h; by_cases he:R*r⁻¹≤x
      · exact hb x ⟨he,hx.2⟩
      have ht:x*r ∈ Ioc 0 R:=⟨mul_pos hx.1 hr', ((lt_div_iff₀ hr').1 (lt_of_not_ge he)).le⟩
      rw [pow_succ,← div_div] at h; specialize hp _ ht (ih _ ht ((div_le_iff₀ hr').1 h)); rwa [mul_inv_cancel_right₀ hr'.ne'] at hp
  intro x hx; exact hh _ x hx (past _ hx.1 hr|>.choose_spec)

omit hr
lemma some_closed (B:ℝ→Prop)(he:∀ᶠ r in trail,B r) : ∃ R:ℝ,0<R∧∀ x∈Ioc 0 R,B x:=by
  rw [eventually_nhdsWithin_iff] at he; obtain ⟨v,hv,hV⟩:= Metric.eventually_nhds_iff.mp he
  exact ⟨v/2,half_pos hv,fun x ⟨hx,he⟩=> hV (by rw [Real.dist_eq,sub_zero,abs_of_pos hx]; exact he.trans_lt (half_lt_self hv)) hx⟩

-- full unit receipt on horizon d, and quotient unit. Real weights engineering politics.
structure ScaleFirm (R t:ℝ)(ε:ℝ)(d:ℕ):Prop where
   length : 0<R
   mover : 1<t
   paid (x:ℝ)(hx:x∈Ioc 0 R) : Ante F d ε t x
   arrival (x:ℝ)(hx:x∈Ioc 0 R) : Ante F (d+1) ε t x ∧ Firm F d ε t x
   valid (x:ℝ)(hx:x∈Ioc 0 R) : Good Hh d x ∧ Good Hh (d+1) x

namespace ScaleFirm
variable (P':ScaleFirm F R r ε d) (he:0 < ε) (hs:x∈ Ioc 0 R)(hh:a∈Ioc 0 x)
include P' he
lemma pay (x:ℝ)(hx:x∈Ioc 0 R)(a:ℝ)(ha:a∈Ioc 0 x)(u:S.Field d):
    chip Hh d a u ≤ r^((d:ℝ)+ε)*(x/a)^((d:ℝ)+ε)*chip Hh d x u:=by
   apply through_up (fun x=> chip Hh d x u) (fun x=>chip_nn ..) ?_ P'.mover (by positivity) (fun s hs=> P'.paid s hs u) x hx a ha; exact fun s hs z _ hz=> power_signal Hh _ hs.1 hz
include hs hh
lemma pour (u:S.Field (d+1)) : sip Hh T d a u ≤ r^((d:ℝ)+1+ε)*(x/a)^((d:ℝ)+1+ε)*sip Hh T d x u:= by
   let q(y:ℝ):= sip Hh T d y u
   exact through_up q (fun y=>sip_nn ..) (fun s h z h' hh=> sip_go Hh T I O h'.1 (P'.valid _ h').1 h.1 hh _) P'.mover (by positivity) (fun s hs=>(P'.arrival s hs|>.2 u).2) x hs a hh
omit he in
lemma discounted (hh': ε≤ (d:ℝ)+1) (u:S.Field (d+1)) : (x/a)^((d:ℝ)+1-ε)*sip Hh T d x u ≤ r^((d:ℝ)+1-ε)*sip Hh T d a u:= by
   let q(y:ℝ):= sip Hh T d y u
   exact through_down q (fun y=>sip_nn ..) (fun s h z h' hh=> sip_go Hh T I O h'.1 (P'.valid _ h').1 h.1 hh _) P'.mover (sub_nonneg.mpr hh') (fun s hs=>(P'.arrival s hs|>.2 u).1) x hs a hh
end ScaleFirm
include hG
lemma mars (Y:Bliss F 𝓛 Z H)(d:ℕ)(ε:ℝ)(he:0<ε): ∃ R t, ScaleFirm F R t ε d:= by
  obtain ⟨t,ht,hT⟩ := ((both_broad F hG Y d ε he).and (eventually_gt_atTop (1:ℝ))).exists
  obtain ⟨R,hR,hL⟩ := some_closed _ (ht.and ((stronger F hG Y d).and (stronger F hG Y (d+1))))
  exact ⟨R,t,hR,hT,fun x hx=>(hL x hx).1.1,fun x hx=>(hL x hx).1.2,fun x hx=>(hL x hx).2⟩
end YM.GapsContact.Power
