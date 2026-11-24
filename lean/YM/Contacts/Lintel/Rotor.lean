import YM.Contacts.Lintel.Waves
namespace YM.Contacts.Lintel
set_option linter.unusedSectionVars false
set_option quotPrecheck false
open Function Set Finset Filter Metric RG Wilson Lattice Precision Exterior MeasureTheory
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F05
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open PertExtension.Chart Radial
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{c f m: Side}{α:ℕ→Type}{n k:ℕ}
namespace Plata
open Crag Steam Lumen Resetter Ion Angle Convoy
namespace Rotor
open AnalyticNext.QuarticMatch.Sheets
variable {X:ℕ→Side}{φ:ℕ→ℝ}{P : Clip}{R:PathData G}{v u w:ℝ} (hR:R.Bounds P v u w)
variable (M:m.val∣ c.val)
private lemma straight (L: Link G m→L[ℝ] Link G c)(F: Link G m→ℝ)(U:Link G c→ℝ) (h:AnalyticAt ℝ F 0) (hp:AnalyticAt ℝ U 0)(n:ℕ)(t:ℝ) (ht: ∀ x, U (L x)=t • F x) (x: Link G m) : Radial.jet U n (L x)= t*Radial.jet F n x:= by
    erw [← woven hp L, show U ∘ L=t • F from funext ht]; unfold Radial.jet; erw [iteratedFDeriv_const_smul_apply h.contDiffAt]; change _*(t*_)=_; ring_nf; rfl -- syntax
lemma copy_main (x:Link G m) : intended P R (still M x)= (mult M:ℝ)* intended P R x := by
   unfold intended; rw [show input G c (still M x)=copies M (input G m x) from rfl, main_copy,nsmul_eq_mul]
lemma copy_star {α:ℝ} (x:Link G m) : draft α R P (arm G c 1 (still M x))= (mult M:ℝ)*draft α R P (arm G m 1 x):= by
   unfold draft secondTerm Precision.loop Patch.average; simp_rw [show represent (arm G c 1 (still M x))=copies M (represent (arm G m 1 x)) from rfl,pull_copies, map_zero,quadratic_copy,uncut_copy,nsmul_eq_mul, ← mul_sum]; ring
abbrev paye (m:Side)(t:ℝ)(R:PathData G)(P:Clip):= draft (c:=m) t R P ∘ arm G m 1
variable {A:ℝ}
lemma paye_this (g:ℝ)(x:Link G m): paye m g R P x=g * inputSeries P R x + turnSeries R.loop x:= rfl
include hR
lemma payA (m:Side): AnalyticAt ℝ (paye m A R P) 0 := (analyticAt_const.mul (stain_knit R P hR (m:=m)).analytic).add (turns_analytic R.loop hR.width hR.two)
lemma jets_core (x:Link G m)(i:ℕ): jet (intended P R) i (still M x)= (mult M:ℝ)*jet (intended P R) i x:= straight _ _ _ (strain P R hR).analytic (strain P R hR).analytic _ _ (copy_main M) _
lemma jets_phase (x:Link G m)(i:ℕ): jet (paye c A R P) i (still M x)= (mult M:ℝ)*jet (paye m A R P) i x:= straight _ _ _ (payA hR m) (payA hR c) _ _ (copy_star M) x
omit hR
-- whip errors converge normalized by whole count. dim only test.Hessian analysis
section compare
variable {Y:bore G}{T:TableFee}{s η:ℝ≥0}
   {F:∀ i,House (Lines G (X i) 1)}{τ:ℕ→ℝ}
include X
lemma whipped (i:ℕ)(r:ℕ)[NeZero r](hm:∀ i,m.val∣ (X i).val) (hp:Roof s Y T)(hg: Cradle (Dye G) Y) (he: ∀ᶠ k in atTop, Rooted (Range.cheap _) (F k i r-hair Y (X k) i r) (τ k))(ht:Tendsto τ atTop (𝓝 0))(x:Link G m):
    Tendsto (fun k=> ((mult (hm k)):ℝ)⁻¹* design (F k i r) (still (hm k) x)) atTop (𝓝 (design (hair Y m i r) x)):= by
   let U k:=F k i r; let V k:=hair Y (X k) i r; let K k:=whip (hm k) (F k-hair Y (X k)) i r; let Z:= design (hair Y m i r) x; let f k:ℝ:=(mult (hm k):ℝ)
   have hM k:=mult_upper (hm k); have hP (k:ℕ): f k ^ (-1:ℤ) *design (U k) (still (hm k) x) = design (K k) x+Z:=by rw [show design (K k)= _ from whip_beam (hm k) i r (F k-hair Y (X k)), Pi.smul_apply,smul_eq_mul,Function.comp_apply,Pi.sub_apply,Pi.sub_apply,parcel_sub,penn _ _ _ hg hp i r (NeZero.ne r)]; unfold f Z U; field_simp [(hM k).ne']; try ring
   let p k:= design (K k) x; have hh : Tendsto p atTop (𝓝 0):= by
      have hz:= he.mono fun j hj=> (scaled_bound (hm j) (P:=F j-hair Y (X j)) (α:=Dye G) _ hj); let M:=Fin r→ Lines G m 1; have hu (v:M): Tendsto (fun j=>K j v) atTop (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) (hz.mono fun j hj=> hj.bound v 0) ht)
      convert Convoy.design_tend atTop 0 (0:ℝ) (fun _=>x) analyticAt_const (Q:=K) hu using 1; ext1 j; rw [Radial.jet_zero]; rfl
   apply Tendsto.congr' (f₁:=fun i=>p i+Z) (f₂:=_) _ (by simpa using hh.add_const Z); filter_upwards with k; exact Eq.symm (by simpa using hP k)
-- thermal decay after multiplying polynomial volumes from Wave extraction. `draft` approximate there from Finance wavelengths.
variable {β:ℝ} {W:∀ i,fieldDir G (X i) 1→ℝ}
def ports (b C:ℝ)(m:Side):ℝ:= (Fintype.card (Site m):ℝ)*C*Real.exp (-b*(m.val:ℝ))
lemma spends (b C:ℝ)(h:b>0)(hi:Tendsto (fun i=>(X i).val) atTop atTop) (Q:ℝ): let f m:ℝ:=((Fintype.card (Lines G m 1)):ℝ)*Q; Tendsto (fun i=>f (X i)^2 * ports b C (X i)) atTop (𝓝 0):= by
   intro f; let r:ℝ:= Fintype.card (Dye G); have he (m:Side): f m^2 * ports b C m = (C*(r*Q)^2) * ((m.val:ℝ)^12*Real.exp (-b * m.val)) := by unfold f ports; change (( (Fintype.card (Co m (Loc G 1))):ℝ)*Q)^2*_ =_; unfold Co; rw [Fintype.card_prod,site_card]; unfold r; push_cast; ring
   simp_rw [he]; convert Tendsto.const_mul (C*(r*Q)^2) ( (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((12:ℕ):ℝ) b h).comp (tendsto_natCast_atTop_atTop.comp hi)) using 1 <;> first| (ext k; simp [Function.comp_def]) | simp
structure tax (F H:Link G m→ℝ): Prop where
   met : F=H
lemma wave_to {b C:ℝ}(hm:∀ i,m.val∣ (X i).val)(h:b>0)(hc:0 ≤ C) (ht: Tendsto (fun i=>(X i).val) atTop atTop) (he:∀ᶠ i in atTop,AnalyticAt ℝ (W i) 0∧AnalyticAt ℝ (draft (c:=X i) A R P) 0∧∀ p q (u v:TypeFace 1→G.ColorIndex→ℂ),(∀ i j,‖u i j‖≤1)→(∀ i j,‖v i j‖≤1)→ |iteratedFDeriv ℝ 2 (W i) 0 ![wave p u,wave q v]-iteratedFDeriv ℝ 2 (draft (c:=X i) A R P) 0 ![wave p u,wave q v]| ≤ ports b C (X i))(x:Link G m):
   Tendsto (fun i=> (mult (hm i):ℝ)⁻¹*(jet (W i∘ arm G _ 1) 2 (still (hm i) x)-jet (paye _ A R P) 2 (still (hm i) x))) atTop (𝓝 0):= by
    let a:= ‖x‖; apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) (he.mono fun i hi=>?_ ) (spends (G:=G) b C h ht a)
    have hu := hi.1; have hv:=Shelf.triton G (W i) _ (C:=ports b C (X i)) (by unfold ports; positivity) (norm_nonneg x) hu hi.2.1 hi.2.2 (still (hm i) x) (fun j=> norm_le_pi_norm x (spool _ j)); rw [norm_mul]; have hz : 1 ≤ (mult (hm i):ℝ) := (by exact_mod_cast mult_pos (hm i)); exact (mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hz))]; exact inv_le_one_of_one_le₀ hz)).trans hv
include hR
lemma persistent (hm:∀ i,m.val ∣ (X i).val) (ht:Tendsto (fun i=>(X i).val) atTop atTop)
    (hf:Roof s Y T)(hp: Cradle (Dye G) Y)
    (he:∀ᶠ i in atTop, Doric (F i) (intended P R) (W i ∘ arm G (X i) 1))
    (hz:∀ i j:ℕ,j ≠0→∃ t:ℕ→ℝ,Tendsto t atTop (𝓝 0)∧∀ n,Rooted (Range.cheap _) (F n i j-hair Y (X n) i j) (t n))
    {b C:ℝ}(hc:0 < b)(hC:0 ≤ C)(h:∀ᶠ i in atTop,AnalyticAt ℝ (W i) 0∧AnalyticAt ℝ (draft (c:=X i) A R P) 0∧∀ p q (u v:TypeFace 1→G.ColorIndex→ℂ),(∀ i j,‖u i j‖≤1)→(∀ i j,‖v i j‖≤1)→ |iteratedFDeriv ℝ 2 (W i) 0 ![wave p u,wave q v]-iteratedFDeriv ℝ 2 (draft (c:=X i) A R P) 0 ![wave p u,wave q v]| ≤ ports b C (X i)): Doric (hair Y m) (intended P R) (paye m A R P):= by
    let y k:ℝ:= (mult (hm k):ℝ); have hy k : 0<y k:= mult_upper ..
    constructor
    · intro r hr hp' x; letI:NeZero r:= ⟨by omega⟩; obtain ⟨t,ht,hZ⟩:= hz (0+r-2) r (NeZero.ne r); have hh:= whipped _ _ hm hf hp (Eventually.of_forall hZ) ht x; unfold grate; rw [if_pos (by omega)]; refine tendsto_nhds_unique (l:=atTop) ((show Tendsto _ atTop _ from (tendsto_const_nhds (x:=jet (intended P R) r x))).congr' ?_) hh; filter_upwards [he] with i hi; let z':= still (hm i) x; have hL:= hi.draw r hr hp' z'; unfold grate at hL; rw [if_pos (by omega)] at hL; rw [← hL, jets_core hR (hm i),inv_mul_cancel_left₀ (hy i).ne']
    intro x; let v (i:ℕ): Link G (X i):= still (hm i) x; let u i:= jet (W i ∘ arm G _ 1) 2 (v i); let z:= jet (paye m A R P) 2 x; have hl: Tendsto (fun i=> (y i)⁻¹*u i) atTop (𝓝 z):= by
       have hx:= (wave_to hm hc hC ht h x).add_const z; rw [zero_add] at hx; refine hx.congr' (Eventually.of_forall fun i=> ?_); rw [jets_phase hR (hm i)]; change (y i)⁻¹ * (u i-y i*z)+z=(y i)⁻¹*u i; field_simp [(hy i).ne']; try ring
    obtain ⟨t,ht,hZ⟩:= hz (2+2-2) 2 (by norm_num); unfold grate; erw [if_pos (by omega)]; refine tendsto_nhds_unique (hl.congr' (he.mono fun i h=> ?_)) (whipped _ _ hm hf hp (Eventually.of_forall hZ) ht x); unfold u; rw [(h.after (v i)),grate, if_pos (by decide)]
end compare
end Rotor
end Plata
end
end YM.Contacts.Lintel
