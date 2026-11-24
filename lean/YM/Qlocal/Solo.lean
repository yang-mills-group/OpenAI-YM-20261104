import YM.Qlocal.StampCo
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Bind
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j i q r:ℕ} {n c f :Side}{S:StepData c f} {b α t:ℝ}
open PertExtension PertExtension.Series Sienna Lantern Catch Catch.Clock tether
variable (F:Forest S.ratio) (X:Layout G)(A:Finset Age) (R:reed G f)(b:ℝ) {O:ChartRatio G}{B0:ℝ→ Config G f→ℝ}{t:S.Choices} (D:Desk F O B0 t)(h:Legal A X)(hR:Flute R q)
local notation "E"=> Apex c G
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "I"=> ℝ × (E × Y)
set_option quotPrecheck false
local notation "U"=> augment F X A D h
local notation "D'[" i "]"=> boost F t X A h R i D hR
local notation "φ'"=> fderiv ℝ D.quiet 0
local notation "φ"=> colorful (φ')
variable (u: Apex c G × Poll.Body (Precision.Key F G))
open StampCo
namespace Schema
abbrev coda (R:reed G f)(D:Desk F O B0 t) : (Apex c G × Poll.Body (Precision.Key F G)) → (ℝ→ℝ) := fun x t=> Comparison.RG02.Bulk.posed S F R (Binding.gaugeL (G:=G) F (t • colorful (fderiv ℝ D.quiet 0) x))
abbrev arum (R:reed G f) (b:ℝ)(D:Desk F O B0 t)(u:E×Y): ℝ→ℝ:=fun t=> b*t* coda F R D u t
abbrev book (u:Apex c G × Poll.Body (Precision.Key F G)) (j:ℕ)(q:ℕ):= fold (someJ (coda F R D u)) q j
include hR
lemma glance : someJ (coda F R D u)= (roll (fold (someJ (coda F R D u)) q) q) := by
 symm; apply StampCo.recovers; let g:= Comparison.RG02.Bulk.posed S F R; have hp:GradeAt q g:=Comparison.RG02.Bulk.joint_receipt S F hR.zeroAt; intro i hi; let z:=(Binding.gaugeL (G:=G) F) (φ u);
 rw [show coda F R D u=(fun t:ℝ=>g (t•z)) from ?_, Laplace.SigmaP.jet_entry (hp.smooth.of_le le_top)]; · exact hp.jet_z _ hi
 ext t; unfold z g coda; rw [_root_.map_smul]
lemma solo_brief : ContDiffAt ℝ ω (coda F R D u) 0:= by
 let f0:= Comparison.RG02.Bulk.posed S F R; let z:I:= φ u; let g:= f0 ∘ (Binding.gaugeL (G:=G) F); have hf:ContDiffAt ℝ ω g 0:=(show ContDiffAt ℝ ω f0 (Binding.gaugeL F 0) from (Binding.gaugeL F).map_zero.symm ▸ ((Comparison.RG02.Bulk.joint_receipt S F hR.zeroAt).smooth)).comp _ (Binding.gaugeL F).contDiff.contDiffAt
 exact ((zero_smul ℝ z).symm ▸ hf).comp (f:=fun p:ℝ=> p•z) (0:ℝ) (contDiffAt_id.smul contDiffAt_const)
lemma itinerary (u:E×Y)(i:ℕ): let A₀:= someJ (coda F R D u); Radial.jet (Comparison.RG02.Bulk.posed S F R) i (Binding.gaugeL F (φ u)) = A₀ i := by
 let g:= Comparison.RG02.Bulk.posed S F R; let z:=Binding.gaugeL F (φ u); have hz : coda F R D u=(fun t:ℝ=>g (t•z)):= by ext t; unfold coda g z; rw [map_smul]
 intro A₀; exact ((Laplace.SigmaP.jet_entry (X:=Comparison.RG02.Bulk.Joint S F) ((Comparison.RG02.Bulk.joint_receipt S F hR.zeroAt).smooth.of_le le_top) (n:=i) z).symm.trans (congr_arg (someJ · i) hz.symm))
local notation "P'[" z "]"=> Function.swap (Impulse (φ') (D'[z]).high D.paid) u
local notation "P"=> Function.swap (Impulse (φ') (U).high D.paid) u

local notation "K"=> arum F R b D u
include h
lemma boost_tape : P'[b]=P+someJ (road ∘ K):= by
 ext1 k; have hp := (U).pay.activity; have hk := bridge_rent F R b hR; let a₁:I→ℝ:= (D'[b]).high; let b₀:=(U).high; let k₀:= build F R b; let v:=φ u; let f:= road ∘ K
 have he : a₁=b₀ - k₀:= by unfold a₁ b₀ k₀; dsimp only [boost,Floe.augment,changes]; abel
 have hv(k:ℕ) : Radial.jet a₁ k v=Radial.jet b₀ k v-Radial.jet k₀ k v:= by
    rw [he, sub_eq_add_neg, Laplace.jet_add (show ContDiffAt ℝ ω b₀ 0 from hp) (show ContDiffAt ℝ ω (-k₀) 0 from hk.smooth.neg)]; simp [Radial.jet,iteratedFDeriv_neg_apply, sub_eq_add_neg]
 have hw : Radial.jet k₀ (k+2) v=someJ f k:= by
    have hV : (fun p:ℝ=> k₀ (p•v))= (fun t:ℝ=>(1*t)^2*f t):= by
       ext1 t; unfold k₀ f; rw [one_mul]; change (t*1)^2*road (b*(t*1)*_)=_; rw [mul_one]; rfl
    have hr:ContDiffAt ℝ ω f 0:= silk.contDiffAt.comp (f:=K) _ (((contDiffAt_const.mul contDiffAt_id).mul (f:=fun t:ℝ=> b*t) (solo_brief F R D hR u))); rw [← jet_entry (hk.smooth.of_le le_top), hV, dispersal f hr, if_pos (by omega), Nat.add_sub_cancel, one_pow, one_mul]
 by_cases h:k=0; swap; · change Impulse (φ') a₁ D.paid k u=Impulse (φ') b₀ D.paid k u+_; rw [Impulse, Impulse,win_atn _ h,win_atn _ h]; change _- Radial.jet a₁ (k+2) v=_- Radial.jet b₀ (k+2) v+ someJ f k; rw [hv,hw]; abel
 subst k; unfold Impulse; simp_rw [Function.swap,Pi.add_apply,win0, someJ_zero];
 change _=_ + road (b*0*coda F R D u 0); rw [mul_zero,zero_mul,none_path, add_zero]; rw [Function.swap, win0]
local notation "L"=> fold (someJ (coda F R D u)) q
lemma exponent_tag : expS (P'[b])=plus (expS P) (someJ (ramp ∘ K)):= by
 let f:= road ∘ K; have hV:ContDiffAt ℝ ω f 0:= silk.contDiffAt.comp (f:=K) _ (((contDiffAt_const.mul contDiffAt_id).mul (f:=fun t:ℝ=> b*t) (solo_brief F R D hR u))); rw [boost_tape, Response.exp_add,← conviction (show ContDiffAt ℝ ω (road ∘ K) 0 from hV), show Real.exp ∘ road ∘ K= _ from (show Real.exp ∘ f=ramp ∘ K from funext fun p=>clear_path _)]
lemma polarized : expS (P'[1]) - expS (P'[-1])= (2:ℝ) • roll (plus (expS (P)) L) (q+1):= by
 let f:= coda F R D u; let g:=arum F R 1 D u; let h₁:= arum F R (-1) D u; let A:= (ramp ∘ g); let B:= (ramp ∘ h₁)
 have hl: A-B=(2:ℝ) • g:=by ext t; unfold A B g h₁; change ramp (1*t*f t)-ramp (-1*t*f t)=2*(1*t*f t); unfold ramp; ring
 have hp:= solo_brief F R D hR u
 have hv u' : ContDiffAt ℝ ω (arum F R u' D u) 0:= ((contDiffAt_const.mul (f:=fun _ :ℝ=> u') contDiffAt_id).mul hp); let h0:=hv 1
 rw [exponent_tag, exponent_tag,← sunk]; apply Eq.trans (b:=plus (expS P) ((2:ℝ) • someJ g)) _ ?_; swap; ·
    have ht: someJ g=roll (someJ f) 1:= by ext i; have hm:= dispersal _ (hp) 1 i 1; change someJ (fun p:ℝ=>1*p*f p) i=_; simpa only [g, f, StampCo.roll, pow_one, one_mul] using! hm
    rw [lscale,ht,show someJ f=_ from glance F R D hR u,stern,folds, StampCo.back] -- order
 unfold A B at hl; have hx(i:ℕ): someJ (((2:ℝ) • g)) i=2*someJ g i:= ((eo_Act i h0).smul (2:ℝ)).writes i le_rfl
 refine congr_arg _ (?_); rw [←some_sub (paved.contDiffAt.comp (f:=g) _ h0) (paved.contDiffAt.comp (f:=h₁) _ (hv (-1))), hl]; exact funext hx
end Schema
end YM.Qlocal.Bind
