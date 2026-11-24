import YM.RG17.Canvas
import YM.RG17.Sparse
import YM.RG17.Regrade
import YM.RG17.Sheared
import YM.SharpGram.Load.Tensor

/-!
# Locate measuring panels at coupling on actual Family and apply the cost budget

Keep support fixed. From mantle grants in Canvas, derive Master/Frame claims
needed about ONE Layout. Can use costs to refine frames with explicit prices.
Not identifying this pose as the requisite frames for actual WilsonX yet.
Selected radii where also leadership. NO Point price off this path. Suppresses
μ suffix only for the real ℝ lengths. At this basis a signed Pose without
having to produce `Rectilinear` separately, also EXACT engineering normalized
(in g copies after shift as priced).
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.RG17
open Function Filter Set Spec Extraction Table OPE OPE.Orbits
open Trace SharpGram RG12
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{f: Extraction.Order}{S:Table C.book}{F:Final C f S}
    {u : Filter (ℕ×ℕ)}
set_option quotPrecheck false
local notation "H"=> C.path.levels.clock.hatBeta
local notation "a"=>C.S.a
local notation "ρ"=>OPE.run
local notation "Ω"=>Maxwell.Free.scheme C.labels
private lemma totalCharge (C:Family G)(d:ℕ)(c:ℂ)(v:C.label d): mass C d (c•v)=‖c‖*mass C d v:=by
   unfold mass Labels.Frame.coeffSize; rw [Finset.mul_sum]; apply Finset.sum_congr rfl (fun i _=> ?_); exact norm_smul c (v i)
lemma crestArmour {m:ℝ→ℕ}(h:Reach C m) : RateIs home ρ (fun r=> H (m r)) 0:= by
   refine ⟨Eventually.of_forall (fun r=>zero_lt_one.trans (C.path.levels.fits.delayed _)),?_⟩
   have hh:= (((strength C).rate.comp h.growing).mul h.nearby); rw [zero_mul] at hh
   apply hh.congr'; filter_upwards [(C.S.divergent.comp h.growing).eventually_gt_atTop 0] with i hi
   change Real.log _/C.S.scale _ * (C.S.scale (m i)/_)= Real.log _ / _
   change 0<C.S.scale (m i) at hi; field_simp

variable (B:Lenses.Mantle F u) (L:Layout F)
local notation "A"=>fun r d=>Load.tent B (L.level r) d
structure Pegs (L:Layout F) : Prop where
   level : Reach C L.level
   along : L.lens ≤ u
   frame (d:ℕ) (r:ℝ): L.frame d r=Load.tent B (L.level r) d
variable (E:Services C f S)
include E in
lemma engineeringPass (h:Pegs B L) (d:ℕ) : ∀ᶠ r in home,
    (∀ v:Free C d, ∃ w:C.label d,mass C d w ≤ 2*H (L.level r)^Lenses.price d * ‖v‖ ∧
       engineering L.charts d (L.level r) w = L.frame d r v) ∧
    ∀ w:C.label d, ‖(L.frame d r).symm (engineering L.charts d (L.level r) w)‖ ≤
       2* Lenses.bonus C d * mass C d w := by
   let g:=h.level.growing; letI:= L.notbot
   filter_upwards [g.eventually (Load.investors B E d),g.eventually_ge_atTop (C.ref d)] with r hu hr
   let i:= L.level r; let Fm := L.frame d r; let s:= a i ^ d
   have hu': Fm=Load.tent B i d:= h.frame d r
   have hs:0<s:=pow_pos (C.S.a_pos _) _
   have hz : (↑s:ℂ) ≠ 0:= by exact_mod_cast hs.ne'
   constructor
   · intro v; obtain ⟨y,q,he,hq,hU⟩:= hu.1 (Fm v)
     change ∀ᶠ x in u, Next.UVStress.quota C d i _ _ (q x) ≤ 2 * H i^Lenses.price d * s * ‖(Load.tent B i d).symm (Fm v)‖ at hU
     rw [← hu',LinearEquiv.symm_apply_apply Fm] at hU
     obtain ⟨w,hw,hws⟩:= L.observes.value d (L.level r) hr le_rfl q y _ (hU.filter_mono h.along) (hq.mono_left h.along)
     refine ⟨(s:ℂ)⁻¹ • w, ?_,?_⟩
     · rw [totalCharge,norm_inv,Complex.norm_real,Real.norm_of_nonneg hs.le]
       refine (mul_le_mul_of_nonneg_left hws (inv_pos.mpr hs).le).trans_eq ?_; change _=2*H i ^ Lenses.price d * _; field_simp
     rw [engineering_at,map_smul,map_smul]; change ((s:ℂ) • _)= Fm v; rw [smul_smul,mul_inv_cancel₀ hz, one_smul, ← hw]; exact he
   intro w
   obtain ⟨q,hq,hc⟩:= L.observes.purchase d i hr le_rfl w
   have he:=hu.2 _ L.notbot h.along _ _ _ hc hq
   rw [engineering_at,map_smul,norm_smul]; change ‖(s:ℂ)‖ * ‖Fm.symm _‖≤ _
   rw [Complex.norm_real,Real.norm_of_nonneg hs.le,hu']; refine (mul_le_mul_of_nonneg_left he hs.le).trans ?_
   apply le_of_eq; change s*(2*_ / s * mass C d w)=_; field_simp
include E
lemma commands (h:Pegs B L) : Handles L:=⟨by
   filter_upwards [h.level.growing.eventually (Load.authored B E 4), h.level.growing.eventually (Load.obtuse B E 4)] with i he hi
   obtain ⟨hv,hx,hw⟩:= he.1 4 le_rfl
   rw [h.frame]
   exact ⟨Maxwell.Free.gear C.labels,Maxwell.Free.scheme C.labels,Maxwell.Free.hierarchy C.labels,(Load.single E.simpleGate).tensor,
     Maxwell.Free.gear_laws C.labels,Maxwell.Free.gear_motion C.labels, ⟨hv,hx⟩, fun p v=> (hi p v).symm,hw⟩⟩
lemma situated (h:Pegs B L) (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (p:ShiftBack L)
    (hb:∀ d, RateLE home OPE.run (fun r=> (L.shift d r).toContinuousLinearEquiv.toContinuousLinearMap) 0)
    (hz:∀ᶠ r in home,L.shift 0 r (C.labels.level 0).e0=(C.labels.level 0).e0): Located L:=by
   refine byGrade P L h.level p hz ?_ ?_ hb ?_
   · intro d; filter_upwards [h.level.growing.eventually (Load.authored B E d)] with i hi; rw [h.frame]; exact (hi.1 d le_rfl).2.2
   · intro d e he
     filter_upwards [h.level.growing.eventually (Load.authored B E e)] with i hi v; rw [h.frame,h.frame]; exact hi.2 _ _ he le_rfl v
   intro d v j
   have hh:= (engineeringPass B L E h d).mono fun _ h=> h.1 v
   rw [eventually_iff_exists_mem] at hh; obtain ⟨Q,hQ,hP⟩:= hh
   choose! w hW hK using hP
   have hv : RateLE home ρ w 0:=by
       have hz:= ((RateLE.const (2:ℝ) ageLarge).mul (((crestArmour h.level).power (Lenses.price d)).pays ageLarge)).mul (RateLE.const ‖v‖ ageLarge); simp only [mul_zero,add_zero] at hz
       exact RateLE.of_norm_le hz (mem_of_superset hQ fun i hi=> (norm_le_mass ..).trans (hW i hi))
   apply RateLE.congr (engineeringUpper P L h.level E d j.val w hv); exact mem_of_superset hQ fun i hi=> congr_arg _ (hK i hi)

omit E
variable {B}
lemma installed [u.NeBot] (he:u ≤ f.fuse) (p:ℝ→ℕ) (hp:Reach C p) (Z:∀ d:ℕ, ℝ→ C.label d≃ₗ[ℂ]C.label d) :
     ∃ L:Layout F,L.level=p ∧ L.shift=Z ∧ Pegs B L:=by
   obtain ⟨v,hn,hv,M,hM⟩:= observe_all C F.room.cutoff ((Push.RelayDifference.cutoff_grows f).mono_left he)
   exact ⟨⟨p,M,v,hn,hv.trans he,hM,Z,fun d r=> Load.tent B (p r) d⟩,rfl,rfl, hp,hv,fun _ _=>rfl⟩
include B E
/-- Along increasing physical horizon there really is such a Layout (cheap-pre conversion).
Can install other shifts paying actual shift receipts instead. -/
lemma here [u.NeBot] (he:u ≤ f.fuse) (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) :
    ∃ L:Layout F, Pegs B L ∧ Located L ∧ Handles L ∧ ∃ s : Extraction.Sequence,
       StrictAnti (B.radius ∘ ⇑s) ∧ ∀ i:ℕ, L.level (B.radius (s i))= s i := by
   obtain ⟨s,hs⟩:= thinning B
   obtain ⟨p,hp,hR⟩:= patchLevel B s hs
   obtain ⟨L,hl,hX,hU⟩:= installed (B:=B) he p hp (fun d _=> LinearEquiv.refl ..)
   refine ⟨L,hU,situated B L E hU P ?_ ?_ ?_,commands B L E hU,s,hs, by rw [hl]; exact hR⟩
   · intro d; rw [hX]; exact RateLE.const _ ageLarge
   · intro d; rw [hX]; exact RateLE.const _ ageLarge
   rw [hX]; exact Eventually.of_forall fun _=>rfl
end YM.RG17
