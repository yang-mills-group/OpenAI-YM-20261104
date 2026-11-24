import YangMills.WilsonProof.NativeSupport.YM.MS.Shine.Pick
/-!
# Characterize regular after weighting by zeros of Pick
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Shine
open Set Filter Function Finset MeasureTheory Metric Arc
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open scoped Topology ContDiff
variable {I:Type}{G:Gauge}{F H:Mob G}{f g:ℂ→ Mob G}{m n j:ℕ}
-- mono negative etc
lemma paid_s (m:ℕ)(f:ℂ→Mob G) : paid (m+1) f=fun i=> i • paid m f i:= funext fun i=>by unfold paid; rw [pow_succ',mul_smul]
lemma pay_1 (f:ℂ→ Mob G) : paid 1 f=fun i=> i • f i:= funext fun i=> by simp [paid]
lemma alu (h:Lift f F): Lift (paid 1 f) 0:=by rw [pay_1]; convert Lift.high (x:=fun i=>i) h (fun z _=> by fun_prop) zero_lt_one using 1; rfl; exact (zero_smul ℂ F).symm
lemma strip (f:ℂ→Mob G) : slip (paid 1 f) 0=ᶠ[dotty] f := by filter_upwards [dotty_non] with i hi; rw [pay_1]; change i⁻¹ • (i • f i-0)= f i; rw [sub_zero,inv_smul_smul₀ hi]
lemma move (h:Pick n f F): Pick (n+1) (paid 1 f) F:= by obtain ⟨x,hx⟩:=h.live; exact ⟨0,alu hx, h.congr (strip _).symm⟩
lemma back (h: Lift (paid 1 f) 0)(he:Pick (n+1) (paid 1 f) F): Pick n f F:= by obtain ⟨u,Ht,he⟩:= he; rw [Lift.unique Ht h] at he; exact he.congr (strip f)
lemma stepUp (h:Live f)(n:ℕ): Live (paid 1 (paid n f)):= pay_live _ (pay_live _ h)
lemma PayRight (f:ℂ→Mob G)(n:ℕ):paid (n+1) f=paid 1 (paid n f):= by rw [← pay_add,add_comm]
lemma dry (h:Live f) : ∀ m<n,Pick m (paid n f) 0:= by
    induction n with
    | zero=> omega
    | succ n ih=>
       intro m hm; rw [PayRight]; cases m with
       | zero=> obtain ⟨F,hF⟩:= pay_live n h; exact alu hF
       | succ m=> exact move (ih m (by omega))
lemma land (h:Lift f F)(n:ℕ): Pick n (paid n f) F:= by induction n with| zero=> rw [pay_zero]; exact h| succ n ih => rw [PayRight]; exact move ih
lemma reveal (h: altitude n f)(hc:∀ m<n,Pick m (paid n f) 0): Live f:= by induction n with
    | zero=> unfold altitude at h; rwa [pay_zero] at h
    | succ n ih=>
       simp_rw [PayRight f n] at hc; have hp := hc 0 (by omega); exact ih (Live.congr (Lift.hols hp) (strip _)) (fun m hm=> back hp (hc (m+1) (by omega)))
lemma migrate (h:Pick m f F): Pick (m+n) (paid n f) F:= by induction n with| zero=> simpa only [pay_zero,Nat.add_zero] using h| succ n ih=> rw [PayRight]; exact move ih
lemma hump (m n:ℕ)(F:Mob G)(hp:kPrice F): Pick m (paid n (fun _=>F)) (if m=n then F else 0):= by
    have h:=Hol.rate ( Hol.stays (D:=disc 1) hp) (x:=fun i=>i^n) (fun i _=>by fun_prop); obtain ⟨Y,Yh⟩:=given (G:=G) ⟨_,Lift.trim h (by norm_num)⟩ m -- accidental placeholder set type
    have hu : Y=(if m=n then F else 0):= by
        funext k l; rw [Yh.choice h zero_lt_one]; change charm m (fun i=> (i^n)* F k l)=_; simp only [charm, iteratedDeriv_mul_const_field, iteratedDeriv_fun_pow_zero]; split <;> rename_i h;
        · subst m; field_simp [Nat.factorial_ne_zero n]; -- nf
        simp
    rw [← hu]; exact Yh
end YM.MS.Shine
