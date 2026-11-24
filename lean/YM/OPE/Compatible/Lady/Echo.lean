import YM.OPE.Compatible.Camo.Bron
/-! # production under old inventory roofs. Lip sensors. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma.Chase
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard AnalyticBridge.VerifiedReset Geo
open Next.Rank.Thirst YM.OPE
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P:Teller G} {D:Patch} {E:ConnectedActivityE6.Target G P} {L:Side} {W a σ C κ v γ t s w:ℝ} {m:ℕ}
variable {o:ConnectedActivityE6.Target.Order G W}
variable {ι:Type*} {l g:Filter ι} {A:ι→ Model D P L E o κ C m}
variable (h:Chase A l)
include h
lemma infΘ (hx:g ≤ l): Chase A g:=⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.select_height.mono_left hx,h.port.filter_mono hx⟩
omit h
lemma slim {F:Type*}[Norm F]{f:ι→F}(h:Lite A l f)(hx:g ≤ l): Lite A g f:=by obtain ⟨b,hb⟩:=h; exact ⟨b,hb.filter_mono hx⟩
abbrev ζOp (v:ℝ):= (Real.sqrt v)⁻¹
private lemma rootb (hv:0<a):a=(ζOp a)⁻¹^ (2:ℕ):=by rw [ζOp,inv_inv,Real.sq_sqrt hv.le]
include h
noncomputable abbrev σW (A:ι→ Model D P L E o κ C m)(i:ι):= ζOp (A i).R.beta
noncomputable abbrev roofW (A:ι→ Model D P L E o κ C m)(i:ι):= ζOp (βM A i)
abbrev billSp (A:ι→ Model D P L E o κ C m)(n:ℕ)(i:ι):= spillMass (G:=G) L n (A i).x
lemma Dscale : ∀ᶠ i in l,0<σW A i∧ (A i).R.beta= (σW A i)⁻¹^(2:ℕ) := by
       filter_upwards [h.port,h.high.eventually_gt_atTop 0] with i hi hv; have he:0<(A i).R.beta:= (half_pos hv).trans_le hi.budget.2.2.2.2.2.1; exact ⟨inv_pos.mpr (Real.sqrt_pos.mpr he),rootb he⟩
lemma LimitSp : ∀ᶠ i in l, σW A i/2 ≤ roofW A i∧ roofW A i/2 ≤ σW A i∧ 0 < roofW A i ∧ ∀ n, billSp A n i= roofW A i* echoM A i^n:=by
       filter_upwards [h.port,h.high.eventually_gt_atTop 0] with i hi hp; let v:=βM A i; let R:= (A i).R.beta; obtain ⟨he,hZ⟩:= hi.budget.2.2.2.2.2; have hr:0<R:= (half_pos hp).trans_le he; let a:= Real.sqrt v; let b:= Real.sqrt R; have hx:0<a:= Real.sqrt_pos.mpr hp; have hh:0<b:=Real.sqrt_pos.mpr hr; have hv:v ≤ 4* R:=(by linarith only [show v/2 ≤ R from he,hr]); have hp':R≤4*v:= (by linarith only[show R≤2*v from hZ,show 0<v from hp]); have hb:= Real.sq_sqrt (show 0≤v from hp.le); change a^2=v at hb; have hR:b^2=R:= Real.sq_sqrt hr.le; refine ⟨?_,?_, inv_pos.mpr hx,fun n=>?_⟩
       · change b⁻¹/2≤a⁻¹; have ht:a ≤2*b :=(by nlinarith only [hx,hh,hp,hv,hb,hR]); rw [div_le_iff₀ (by norm_num),inv_le_iff_one_le_mul₀ hh]; field_simp; linarith
       · change a⁻¹/2≤ b⁻¹; have ht : b ≤2*a :=(by nlinarith only [hx,hh,hp',hb,hR]); rw[div_le_iff₀ (by norm_num),inv_le_iff_one_le_mul₀ hx]; field_simp; linarith
       unfold billSp spillMass skimX; rw [Real.rpow_neg hp.le,← Real.sqrt_eq_rpow]
lemma ζOpR : RateIs l (fate A) (σW A) (-(1/2)):=by
        have he:RateIs l (fate A) (roofW A) (-(1/2)):=by refine h.wisdom.congr ((h.high.eventually_gt_atTop 0).mono fun i hi=>?_); change βM A i ^ (-(1/2):ℝ) = ζOp _; rw [Real.rpow_neg hi.le,ζOp,Real.sqrt_eq_rpow]; -- unfold
        exact RateIs.of_sandwich (show RateIs l (fate A) (fun i=>roofW A i/(2:ℝ)) _ from (by simpa using he.div (RateIs.const h.tense (by norm_num :0 < (2:ℝ))))) ((he.pays h.tense|>.mul (RateLE.const (2:ℝ) h.tense)).mono (by simp)) (h.LimitSp.mono fun _ hi=>hi.2.1) (h.LimitSp.mono fun _ hi=>(div_le_iff₀ (by norm_num :0 < (2:ℝ))).1 hi.1) h.tense
end YM.PhysicalNext.Repeat.Aroma.Chase
