import YM.XSpace.Compat.Native
import YM.XSpace.Compat.NativeDifference
import YM.XSpace.Compat.Petals

/-! Additive compatibility closure from pinned Oct15 ancestry.
Current baseline definitions are reused; extracted declaration text is unchanged.
Prepared for independent checking; no successful build is claimed here. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Compat.KP
open YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory Lattice Bloch Laurent Exterior Matrix Precision
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι : Type*} {α Ω η : ℝ} {I : Firm α Ω η}
variable (A B : List Axis)

lemma memoir (a b : PA) (ha : 0<α) (he : 0<η) : ∃ C:ℝ, 0≤C ∧ ∀ f : Firm α Ω η,∀ x:E4,1≤‖x‖→
    ‖retract (fun p=> rebus A B f p (plaquette a) (plaquette b)) x-↑(decree A B a b x)‖ ≤ C*(‖x‖^(heft A B+5))⁻¹ := by
  let J := Firm α Ω η; let n := heft A B+1
  let w (i:J) (p:E4) := ivory A B i p (plaquette a) (plaquette b)
  have hu := ivory_goes A B ha (Ω:=Ω) he (plaquette a) (plaquette b)
  have hh : Weight whole (n:ℤ) w := by rw [show (n:ℤ)=sizeL A+sizeL B+1 by unfold sizeL n heft; omega]; exact hu
  have hk : Weight whole (-5) w:=pay_all hh (ivory_lives A B (plaquette a) (plaquette b)) (by omega)
  have hv := scent (n+4) A B a b
  obtain ⟨C,hC,H⟩:=night_pay hh hk; obtain ⟨D,hD,K⟩:=hv.rate
  refine ⟨‖(↑tally:ℂ)‖ * C+D,by positivity,fun f x hx=> ?_⟩
  rw [show (fun p=> rebus A B f p (plaquette a) (plaquette b))=w f+stalk A B a b from funext fun p=> by simp [stalk,w,ivory]]
  unfold retract; rw [meal_sum (asset_good hh hk f) hv.serves.delivered,mul_add,add_sub_assoc]; apply (norm_add_le ..).trans
  rw [norm_mul,add_mul,mul_assoc]; exact add_le_add (mul_le_mul_of_nonneg_left (H f x (norm_pos_iff.mp (zero_lt_one.trans_le hx))) (norm_nonneg _)) (K x hx)

private lemma gear {n : Side} (t : Site n) (i : Axis) (x : Cover) : mode (mon t) (x+step i)-mode (mon t) x = mode (mon t) x * tooth (lit n (lift t)) i := by
  rw [mode_shift,factor,tooth,q,lit_mon]
  ring

private lemma gear_right {n : Side} (t : Site n) (i:Axis) (x:Cover) : mode (mon t) (x-step i)-mode (mon t) x=mode (mon t) x * star (tooth (lit n (lift t)) i) := by
  unfold tooth q
  rw [lit_mon,← factor,sub_eq_add_neg x,mode_shift,star_sub]
  have h:=mode_adjoint (mon t) (step i)
  rw [real_frequency] at h
  rw [h,star_one]
  ring

lemma spin_lag (n) (f:Firm α Ω η) (a b : X2) : slot checkout B (slot checkin A (rock n f a b))=transmits A B n f a b := by
  let G (A B : List Axis) := transmits A B n f a b
  have he (S T) (i : Axis) : checkin i (G S T)=G (S++[i]) T := by
    funext p; unfold checkin G transmits; rw [← mul_sub,← Finset.sum_sub_distrib]; congr 1
    refine Finset.sum_congr rfl fun t _ => ?_; rw [← sub_mul,gear]; unfold record bill; simp; ring
  have hb (S T) (i : Axis) : checkout i (G S T)=G S (T++[i]) := by
    funext p; unfold checkout G transmits; rw [← mul_sub,← Finset.sum_sub_distrib]; congr 1
    refine Finset.sum_congr rfl fun t _=> ?_; rw [← sub_mul,gear_right]; unfold record bill; simp; ring
  have ha (S T : List Axis) : slot checkin A (G S T)=G (S++A) T := by induction A generalizing S with | nil=>simp [slot] | cons a A ih=>rw [slot,he,ih]; simp
  have hh (T S : List Axis) : slot checkout B (G S T)=G S (T++B) := by induction B generalizing T with | nil=>simp [slot] | cons b B ih=>rw [slot,hb,ih]; simp
  change slot checkout B (slot checkin A (G [] []))=G A B; rw [ha,hh]; rfl

theorem k_per (a b : PA) (ha : 0<α) (he : 0<η) (Ω : ℝ) : ∃ C:ℝ,0<C ∧ ∀ (f:Firm α Ω η),∀ (n:Side),∀ (x:Cover),1 ≤ ‖rcast x‖ →
    ‖slot checkout B (slot checkin A (rock n f (plaquette a) (plaquette b))) x-↑(decree A B a b (rcast x))‖ ≤
      C*((‖rcast x‖^(5+A.length+B.length))⁻¹+(1+‖rcast x‖)/(n.val:ℝ)) := by
  obtain ⟨C,hC,H⟩ := lift_mesh A B (Ω:=Ω) ha he (plaquette a) (plaquette b); obtain ⟨D,hD,K⟩:=memoir A B (Ω:=Ω) a b ha he
  refine ⟨C+D+1,by positivity,fun f n x hx=>?_⟩
  specialize H f n x
  specialize K f (rcast x) hx
  rw [spin_lag]
  let F := retract (fun p=> rebus A B f p (plaquette a) (plaquette b)) (rcast x)
  apply (norm_sub_le_norm_sub_add_norm_sub _ F _).trans (add_le_add H K|>.trans ?_)
  rw [show heft A B+5=5+A.length+B.length by unfold heft; omega]
  have ht:=side_pos n
  rw [← sub_nonneg]
  ring_nf
  positivity

end YM.XSpace.Compat.KP
end
