import YM.X.Scheme.Wins
import YM.X.Journey.Bare
/-!
# Stable recalibration modulo near-Jet precritical real H frame (association joins).
Any-order statement, used in FO with singular shape estimates.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX
open Lattice Function Filter Set Pert Pert.Position Pulse Detector Jet
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G}{d n:ℕ}
local notation "B"=> Bank F d
namespace Ribbon
open Reed
local notation "R₀" => Buffer F d
local notation "H"=> Bank F d
local notation "U"=> Lens F d n
local notation "Fℕ"=>(atTop:Filter ℕ)
lemma flow_tip {V X:Type*}[NormedAddCommGroup V][NormedAddCommGroup X][NormedSpace ℝ V][NormedSpace ℝ X](a:Word V)(f:V→X)(h:DifferentiableAt ℝ f (a 0)) : run f a 1=fderiv ℝ f (a 0) (a 1):= by
   let w:= delay a 1; have hp:= (show Act 1 w a from Act.swell a le_rfl); have hx: HasDerivAt w (a 1) 0:= by
      have h₁:= hp.writes 1 le_rfl; simp only [someJ,Nat.factorial_one,Nat.cast_one,inv_one,one_smul,iteratedDeriv_one] at h₁; exact h₁ ▸ (hp.nice.differentiableAt (by simp)).hasDerivAt
   rw [←hp.zero] at h; simp only [run, someJ,Nat.factorial_one,Nat.cast_one,inv_one,one_smul,iteratedDeriv_one]; rw [←hp.zero]; exact (h.hasFDerivAt.comp_hasDerivAt 0 hx).deriv
variable (w:Word (Bank F d))(b:Word (Buffer F d))(s:Pert.Position.Section F d) {k:ℕ}(t:Test n)(p:Fin n→ E F d)
lemma all_tips (k:ℕ) : lookie F s (predMarket b w k)=run (cross F s.p) (pair (expose F s.f ∘ w) b) k:= by
    have hx:= appears_delay w k; have hp:= Act.swell b (le_refl k); have ht:= pred_leaves s hx hp; exact ((appears_market hx hp).writes s).trans_at ht le_rfl
lemma cross_bank (x:Word (Bank F d))(a:R₀) (r:ℝ) : cross F p (expose F t (x 0) +r • expose F t (x 1),a)= market F a (x 0+r • x 1) n t p:= by rw [←map_smul,←map_add]; exact cross_market ..
lemma income (x:Bank F d)(a:Buffer F d) : HasDerivAt (fun r:ℝ=> market F (r • a) x n t p) (passV (bufferL F a) (x n t) p) 0:= by
    let v:= (lightBank F (x n t)).restrictScalars ℝ; let f (t:ℝ) := frameC F (t • a) ∘ p
    have he : f 0=p:= by unfold f; rw [zero_smul,frameC_zero];rfl
    have hh: HasDerivAt (v ∘ f) (v.linearDeriv p (a.val ∘ p)) 0 := by rw [←he] ; exact (v.hasFDerivAt _).comp_hasDerivAt 0 (show HasDerivAt f (a.val ∘ f 0) 0 from (by rw [he]; exact hasDerivAt_pi.mpr (fun i=> pulse F (p i) a))) -- rw f expansion
    rw [pass_view]; rw [ContinuousMultilinearMap.linearDeriv_apply] at hh; exact hh
private lemma torque {X Y:Type*}[NormedAddCommGroup X][NormedAddCommGroup Y][NormedSpace ℝ X][NormedSpace ℝ Y](f:X→Y)(p:X)(h:DifferentiableAt ℝ f p)(v:X)(u:Y)(g:HasDerivAt (fun r:ℝ=> f (p+r • v)) u 0): fderiv ℝ f p v=u:= by
    have he:HasDerivAt (fun t:ℝ=>p+t • v) v 0:= by simpa only [one_smul] using! (((hasDerivAt_id' (0:ℝ)).smul_const v).const_add p)
    exact (h.hasFDerivAt.comp_hasDerivAt_of_eq _ he (by simp)).unique g
lemma come_zero (hx:b 0=0) : predMarket b w 1 n t p=w 1 n t p + passV (bufferL F (b 1)) (w 0 n t) p:= by
    let f:= cross F p; let x: Lens F d n × Buffer F d:= (expose F t (w 0),0); let P:= pair (expose F t ∘ w) b; have hp: P 0=x:= by unfold P x pair; rw [hx];rfl
    have h : DifferentiableAt ℝ f x := (cross_smooth F p|>.differentiable (by simp)) _; let L:= fderiv ℝ f x
    let a: E F d→ E F d:= frameC F 0; change lookie F (Pert.Position.Section.mk n p t) (predMarket b w 1) = _ -- params
    rw [all_tips]; change run f P 1=_; rw [flow_tip P f (hp.symm ▸ h),hp,show P 1=(expose F t (w 1),0)+(0,b 1) from Prod.ext (add_zero _|>.symm) (zero_add _|>.symm),map_add]; apply congr_arg₂ (·+·)
    · apply torque (f:=f) x h _ _; unfold f x; simp_rw [show ∀y:Lens F d n,∀r:ℝ,(expose F t (w 0),(0:R₀))+r • (y,0) = (expose F t (w 0)+r • y,0) from fun _ _=> Prod.ext rfl (show 0+_ • (0:R₀)=0 from by simp), cross_bank,market_zero]; refine (show HasDerivAt (fun a:ℝ=> lookie F (Section.mk n p t) (w 0)+ a • lookie F (Section.mk n p t) (w 1)) _ 0 from ?_); simpa only [one_smul] using! (((hasDerivAt_id' (0:ℝ)).smul_const (lookie F (Section.mk n p t) (w 1))).const_add (lookie F (Section.mk n p t) (w 0)))
    apply torque f x h _ _; unfold f x; simp_rw [show ∀r:ℝ,(expose F t (w 0),(0:R₀))+r • (0,b 1)=(expose F t (w 0),r • b 1) from fun r=>by simp, cross_market];exact income ..
end Ribbon
end YM.PositionX
