import YM.GradedFar.Promenade
/-!
# Compact η through general ratios (continued)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Neighbor.Lounge
open Function Filter Set PowerSeries
open Extraction Table Spec OPE.Orbits Climb Trace.Pilot PhysMS
open FVA2 XSpace XSpace.Normalize MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Tide
open FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar YM.FVA2.GradedFar.Cart
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}
   (J:ℝ→tower S) (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ) (h p:ℕ)
local notation "g"=> strength G
local notation "γ" => fun (T:ℝ)=> -Real.log T
local notation "ϕ" => GroupS.ψ Z.criterion M ν
local notation "Kt" => GroupS.gaugeN Z.scheme Z.criterion M ν
local notation "U'" => fun (r s:ℝ)=> LinearEquiv.toLinearMap (relative J r s h)
local notation "D'" => stretching G h
local notation "op" => stamp G h
variable {t:ℝ→ℝ} {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "B'" => fare Z M ν h p
local notation "J'" => ticker Z M ν p
local notation "Θ" => Error J Z M ν h p t
local notation "v'" => fun r=> (t r:ℂ)

lemma stamp_tour {r T x:ℝ}(hT:0<T)(hx:Fits 2 x): ℳ J h r (T*x)=D' (Real.log x)*ℳ J h r T * op (U' (r*T) (r*T*x)):=by
 rw [ℳ,mul_comm T,Real.log_mul (Fits_pos zero_lt_two hx).ne' hT.ne',mul_comm x T,← mul_assoc r T x,
    ℳ, ← stretch_mul]; have hA:=fold J h r (r*T) (r*T*x); dsimp only at hA; rw [← hA, price]; dsimp only; simp only [mul_assoc]
-- redefine LocalPlan for signed
structure LocalPlan (t:ℝ→ℝ)(b r T:ℝ): Prop where
 cost : ‖B' (γ T) (t r)‖ ≤ 2
 surplus x(x1:Fits 2 x) : ‖B' (γ T) (t r)*B' (γ x) (J' (γ T) (t r)) - B' (γ (T*x)) (t r)‖ ≤ b
 corner x(x1:Fits 2 x) : ‖J' (γ x) (J' (γ T) (t r))-J' (γ (T*x)) (t r)‖ ≤ b
 transfer x(x1:Fits 2 x): ‖B' (γ x) (t (r*T))-B' (γ x) (J' (γ T) (t r))‖ ≤ ‖(t (r*T):ℂ)-J' (γ T) (t r)‖
 hear x(x1:Fits 2 x): ‖J' (γ x) (t (r*T))-J' (γ x) (J' (γ T) (t r))‖ ≤ 2*‖(t (r*T):ℂ)-J' (γ T) (t r)‖
include H
set_option maxHeartbeats 400000 in
lemma passage {b c d r T x:ℝ}(hT:0<T)(hx:Fits 2 x)(hA: Θ b r T)(hv:LocalPlan Z M ν h p t c r T)
    (he:Θ d (r*T) x)(hw:‖op (U' (r*T) (r*T*x))‖≤2^h+1): Θ ((2^h*(2^h+1)+3)*b+c+2*d) r (T*x):=by
 let t':=v' r; let s:=r*T; let t₁:=v' s; let t₂:=v' (s*x); let z:=J' (γ T) t'; let z':=J' (γ (T*x)) t'
 have hp:0≤(2:ℝ)^h*(2^h+1):=by positivity
 have Hb:0≤b:=(norm_nonneg _).trans hA.1; have Hd:0≤d:=(norm_nonneg _).trans he.1
 let u:=op (U' (r*T) (r*T*x)); let u':= B' (γ T) t'; let v:=B' (γ x) z; let vΔ:=ℳ J h s x
 have H₁ : ‖vΔ-v‖ ≤ d+b:= (opt _ _ (B' (γ x) t₁)).trans (add_le_add he.1 ((hv.transfer x hx).trans hA.2))
 have H₂ : ‖ℳ J h r (T*x)-u'*vΔ‖ ≤ b*(2^h*(2^h+1)):= by
   let D:=D' (Real.log x); have hP:u'*vΔ=D*u'*u:=by change u'*(D*u)=_; unfold u' t'; rw [kept Z M ν H,mul_assoc]
   have Ht : ‖D‖≤ (2:ℝ)^h := by
      obtain hf:=box_cost h (G:=G) 2 one_le_two x⁻¹ (fits_turn zero_lt_two hx); dsimp only at hf; rw [Real.log_inv,neg_neg] at hf; exact hf
   rw [stamp_tour J h hT hx,hP]; change ‖D* _ *u-D* _ *u‖ ≤ _; rw [← sub_mul,← mul_sub]
   exact (norm_mul_le ..).trans ((mul_le_mul ((norm_mul_le ..).trans (mul_le_mul Ht hA.1 (norm_nonneg _) (by positivity))) hw (norm_nonneg _) (by positivity)).trans_eq (by ring))
 have H₃:= (opt (ℳ J h r (T*x)) (u'*v) (u'*vΔ)).trans (add_le_add H₂ (show ‖u'*vΔ-u'*v‖ ≤ 2*(d+b) from by
   rw [← mul_sub]; exact (norm_mul_le ..).trans (mul_le_mul hv.cost H₁ (norm_nonneg _) (by norm_num))))
 have HH:0≤b*(2^h*(2^h+1)):= mul_nonneg Hb hp
 constructor
 · exact (opt _ _ (u'*v)).trans ((add_le_add H₃ (hv.surplus x hx)).trans (by nlinarith only [Hb]))
 rw [← mul_assoc r]
 have h4: ‖t₂-J' (γ x) z‖ ≤ d+2*b:= (opt _ _ (J' (γ x) t₁)).trans (add_le_add he.2
   ((hv.hear x hx).trans (mul_le_mul_of_nonneg_left hA.2 (by norm_num))))
 exact (opt _ _ (J' (γ x) z)).trans ((add_le_add h4 (hv.corner x hx)).trans (by linarith only [Hb,Hd,HH]))

variable {K:ℝ}(hK:2≤K)(ht:Coupling G t)
include hK ht H
set_option maxHeartbeats 400000 in
lemma always (hp:1≤p):∃ b:ℝ,0≤b ∧ ∀ᶠ r in trail,∀ T,Fits K T→ LocalPlan Z M ν h p t (b*g r^(p+1)) r T:=by
 obtain hV:=show 0<K from zero_lt_two.trans_le hK
 obtain ⟨δ,hδ,hL⟩:= ((show ∀ᶠ δ:ℝ in trail,0<δ from self_mem_nhdsWithin).and (jiffy Z M ν h p H (Real.log K))).exists
 obtain ⟨C,hC,k,hx⟩:= budget_up Z M ν h p H hp (Real.log K)
 let H' := C*(1+Real.log K)^k; have hLog:= Real.log_nonneg (one_le_two.trans hK); have hP:0<H' := by dsimp only [H']; positivity
 refine ⟨H'*2^(p+1),by positivity,?_⟩
 have ht':=Coupling.conforms hG ht; have hF:Tendsto (fun r=>‖v' r‖) trail (𝓝 0):=by simpa only [Complex.norm_real,norm_zero] using ht'.norm
 have hF': Tendsto (fun r=> H'*‖v' r‖^2) trail (𝓝 0):=by simpa using (hF.pow (2:ℕ)).const_mul H'
 filter_upwards [ hF'.eventually_le_const zero_lt_one,
    (show Tendsto (fun r=> H'*‖v' r‖^2+ ‖v' r‖) trail (𝓝 0) from by simpa only [add_zero] using hF'.add hF).eventually_le_const hδ,
    threshold hK _ (hF.eventually_le_const hδ), clock_budget hG ht] with r hq hr ht hc T hT
 let u:=γ T; let t':=v' r; have hv:=Fits_pos hV hT
 have H₁:0<g r:= hc.1; have H₂:‖t'‖ ≤ 1:=by rw [show ‖t'‖=|t r| from (Complex.norm_real _).trans (Real.norm_eq_abs _)]; exact hc.2.1
 have Ht:‖t'‖≤2*g r:=by rw [show ‖t'‖=|t r| from (Complex.norm_real _).trans (Real.norm_eq_abs _)]; exact hc.2.2
 have H0 : C*(1+|u|)^k ≤ H':= by unfold H'; gcongr; exact log_box hV hT
 let A:= hx u 0 t' (by rw [abs_zero]; apply abs_nonneg) H₂; let v:=B' u t'; let w:=J' u t'
 have ha : ‖v-1‖≤1:= (A.1.trans (mul_le_mul_of_nonneg_right H0 (by positivity))).trans hq
 have hβ : ‖w‖ ≤ δ:= by
    have hv: ‖w-t'‖ ≤ H'*‖v' r‖^2:= A.2.1.trans (mul_le_mul_of_nonneg_right H0 (by positivity))
    exact (norm_le_norm_sub_add w t').trans ((add_le_add_left hv _).trans hr)
 have hi(x:ℝ)(hh:Fits 2 x) : |γ x| ≤ |Real.log K|:= (log_box hV (two_box x K hK hh)).trans (le_abs_self _)
 have hg: C*(1+|u|)^k*‖t'‖^(p+1) ≤ H'*2^(p+1)*g r^(p+1):= (mul_le_mul H0 (pow_le_pow_left₀ (norm_nonneg _) Ht (p+1)) (by positivity) hP.le).trans_eq (by rw [mul_pow]; unfold H'; ring)
 have hA(x:ℝ)(hh:Fits 2 x): γ (T*x)=u+γ x:= by unfold u; dsimp only; rw [Real.log_mul hv.ne' (Fits_pos zero_lt_two hh).ne',neg_add]
 refine ⟨?_,fun x ht=>?_,fun x ht=>?_,fun x hx=>(hL (γ x) _ _ (hi x hx) (ht T hT) hβ).1,fun x hx=>(hL (γ x) _ _ (hi x hx) (ht T hT) hβ).2⟩
 · refine (norm_le_norm_sub_add v 1).trans ?_; linarith only [id_cost (G:=G) h,ha]
 · dsimp only; rw [show -Real.log (T*x)=_ from hA x ht]; exact ((hx u (γ x) t' (hi x ht) H₂).2.2.1).trans hg
 dsimp only; rw [show -Real.log (T*x)=_ from hA x ht]; exact ((hx u (γ x) t' (hi x ht) H₂).2.2.2).trans hg
end YM.Integration.GradedFar.Neighbor.Lounge
