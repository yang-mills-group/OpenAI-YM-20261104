import YM.SchemeConversionRG11.FirstW.Calx.Huts
import YM.SchemeConversionRG11.FirstW.Kernel.Paid
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Set Metric Topology Lattice Pert Pert.Align
open scoped Topology BigOperators Classical
variable {E F G : Type*} {T:Itinerary} [NormedAddCommGroup E] {c:ℕ→Side} {R r:ℝ}
-- Supports on orbital center with margin
abbrev Hall (T:Itinerary) (E:Type*) := Board T E
variable {p f y:Hall T E}{F':E4→E}
def Placed (T:Itinerary)(R:ℝ)(p:Hall T E):= ∀ᶠ i in atTop,∀ x:Site (T.period i),p i x≠0 → ‖out T i x‖≤R
lemma Placed.extend (h:Placed T r p)(e:r≤R): Placed T R p:= Eventually.mono h (fun _ hi x hx=> le_trans (hi x hx) e)
lemma given_limit (h:Meets T (Metric.closedBall 0 R) p F')(s:StepPath T)(v:E4)(he:sails T s v)(hs:‖v‖≤R): Tendsto (fun i=>p i (s i)) atTop (𝓝 (F' v)):= h id tendsto_id v (mem_closedBall_iff_norm.mpr (by simpa using hs)) _ he
lemma gone_limit (h:Placed T r p)(s:StepPath T)(v:E4)(he:sails T s v)(hs:r<‖v‖): Tendsto (fun i=>p i (s i)) atTop (𝓝 0):= Tendsto.congr' (f₁:=fun _=>(0:E)) ((Eventually.and h ((Tendsto.norm he).eventually (lt_mem_nhds hs))).mono fun _ hi=> Eq.symm (not_ne_iff.mp (fun e=>not_le.mpr hi.2 (hi.1 _ e)))) tendsto_const_nhds
abbrev Town(R:ℝ):Set E4:=closedBall 0 R
lemma Placed.flow (h:Placed T r p)(hp: r<R)(s:Cover): Placed T R (fun i x=>p i (x+wrap (T.period i) s)):=by
 filter_upwards [h,birthM (T:=T) hp (-s),entryM T R] with i hi he h' x h
 let v:= lift (x+wrap (T.period i) s); have hh: Jam T R i (v+-s):= he v (hi _ h)
 have hz:=h' _ hh; rw [map_add,map_neg,show wrap (T.period i) v=_ from wrap_lift (x+wrap (T.period i) s), add_neg_cancel_right] at hz; unfold out; rw [hz]; exact hh
-- Lebesgue budget for bounded-power singular at one mark, no collapse derivative claim.
def SaveB (T:Itinerary)(k:ℕ)(p:Hall T E):= ∃ C>0,∀ᶠ i in atTop,∀ x:Site (T.period i), growsOut (T.gap i) x ^ k * ‖p i x‖≤ C
section settle
variable [NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] [NormedAddCommGroup G][NormedSpace ℝ G][CompleteSpace G] {k:ℕ}{q:Hall T F}{Y:E4→F}
lemma cap_power (h:SaveB T k p)(hc:MarkGrid T c)(hp:Meets T {x:E4|x≠0} p F')(he:r<R)(hr:0≤r)(hk:k≤3)(hq:Meets T (Town R) q Y)(hw:Placed T r q) (B:E→L[ℝ] F→L[ℝ] G):
  let f(i:ℕ)(x:Site (T.period i)):= B (p i x) (q i x)
  let V: E4→G:= fun v=> (if v∈Town R then B (F' v) (Y v) else 0)
  Integrable V ∧ Tendsto (fun i=>(T.gap i)^4 • ∑ x:Site (T.period i), f i x) atTop (𝓝 (∫ v,V v)) := by
 intro f V; obtain ⟨C,hC,H⟩:= h; obtain ⟨D,hD,Z⟩ := hq.rent (isCompact_closedBall (0:E4) r) (closedBall_subset_closedBall he.le)
 let U:=(r+1)^(3-k)*‖B‖ * C*D
 refine sum_local (F:=f) hc (C:=U) (R:=r+1) (by unfold U; positivity) ?_ ?_
 · filter_upwards [H,Z,hw,T.cutoff.eventually (ge_mem_nhds (by norm_num:(0:ℝ)<1))] with i hi he hw hv x
   by_cases h:q i x=0; · refine ⟨fun e=>(e (by simp [f,h])).elim,(by simp only [f,h,map_zero,norm_zero,mul_zero]; unfold U; positivity)⟩
   let z:=growsOut (T.gap i) x; have hx:= hw x h; have hz0:= mul_pos (T.positive i) (zero_lt_one.trans_le (unit_cy x)); have hz: z ≤ r+1:= by
      have hl : Foot T i (Lattice.lift x) ≤ r+T.gap i:= limb hx; change z≤_ at hl; linarith only [hl,hv]
   refine ⟨fun _=>hz,?_⟩; change z^3 * _ ≤ U
   have he': ‖f i x‖≤ ‖B‖*‖p i x‖*D := (ContinuousLinearMap.le_opNorm _ _).trans ((mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left (he x (by simpa using hx)) (by positivity)))
   have hzz : 0≤z:= hz0.le
   refine le_trans (mul_le_mul_of_nonneg_left he' (by positivity)) ?_
   calc z^3 * _ = z^(3-k)*‖B‖*(z^k * ‖p i x‖)*D:= by nth_rw 1 [show 3=3-k+k from by omega, pow_add]; ring
        _ ≤ U:=mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hzz hz _) (norm_nonneg B)) (hi x) (by positivity) (by positivity)) hD.le
 refine (volume.ae_ne 0).mono fun v hv s hs=>?_ ;
 have hX:= hp id tendsto_id v hv _ hs
 let L : E×F→ G:= uncurry fun x y=>B x y
 have hL: Continuous L:= (B.continuous.comp continuous_fst).clm_apply continuous_snd
 unfold V; split
 next hm=> exact hL.continuousAt.tendsto.comp (hX.prodMk_nhds (hq id tendsto_id v hm _ hs))
 next hm=> have ht := gone_limit hw s v hs (lt_trans he (by simpa only [Town,mem_closedBall_iff_norm,sub_zero,not_le] using hm)); have hZ:=hL.continuousAt.tendsto.comp (hX.prodMk_nhds ht); rw [show L (F' v,0)=0 from map_zero _] at hZ; exact hZ
end settle
end YM.RG11.FirstW
