import YM.QuadraticLocal.Aperture.Gale
import YM.AllOrder.Docket.Tier
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Aperture
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder PertExtension.Series AllOrder.Laplace AllOrder.Laplace.SigmaP Response Laurent Stationary
open PositionX.Jet Extra.Iteration AllOrder.Floe AllOrder.Floe.Pace AllOrder.Floe.Aero AllOrder.Floe.StateE
open AllOrder.Catch AllOrder.Catch.Clock Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {L n f: Side}{ι:Type*}{T:AllOrder.Catch.Clock ι} {W b D α a B C Ω κ V:ℝ}{k p M:ℕ}
variable {P:Patch}{K:KernelChoices}{S : StepData n f} {s:Teller G}{η : Stage}
open Metric ConnectedActivityE6.Coat
open Aux Aux.Name
namespace Phase
variable {r:Stage}{j:ℕ}{u:ℝ→ℝ} {t w x:ℕ}{U:Push.Uniform.Before G r.width r.paths P.J K ((k+3)+3)}
variable (A: Aux.Name G P K u x r (k+3) U)
local notation "I"=>Aux.Name G P K u x r (k+3) U
local notation "ξ"=> Aux.scope x
local notation "d"=> A.Θ
local notation "Θ"=> A.price.threshold
open Till Tilt Lantern
local notation "F"=> A.Fs
variable {O:ChartRatio G}(hO:LocalRatio O)
variable (W:ι→Aux.Name G P K u x r (k+3) U) (Q:∀ i,Phase (W i))(h:Aux.Name.Proper W T)
set_option quotPrecheck false
local notation "V'"=>fun i=> (W i|>.Bank O)
local notation "b'"=> (fun i=> (W i).Θ)
local notation "hX"=> T.Meter
set_option quotPrecheck false
local notation "Λ"=> T.rail
local notation "R"=> fun i=> (W i).Qc
local notation "K'"=> fun i=> (W i).Ph
local notation "M₁"=> fun i=> (W i).Mh
local notation "Q'"=> fun i=> (W i).Zc
variable (D) (hD:0<D) {p:ι→ℝ}
local notation "Z"=> fun i=> Aperture.Phase.callP (W i) hO (Q i)
set_option quotPrecheck false
local notation "Ψ"=> fun i=> Aperture.Phase.roofP (W i) (Q i)
local notation "Δ"=> fun i=> Ψ i - (W i).Qc
variable (hQ: Flood (Y:=fun i=>(W i).Vx) (X:=fun i=>(W i).X) (fun i=> Aperture.Phase.roofP (W i) (Q i)) T (k+3)) (T₀:ℝ)(hW:∀ᶠ i in T.rail,∀ y:Config G ((W i).f), flags ((W i).price.threshold) y=∅ → Aperture.Phase.shadeP (W i) (Q i) y ≤ T₀)
variable {y z:∀i,(W i).X}(hg:∀ᶠ i in T.rail,(W i).goods O D (p i) (z i))(hy:T.Meter (fun i=> ‖y i‖) (-(1/2:ℝ)))(ht:∀ᶠ i in T.rail,‖y i-z i‖≤ furl G P.L ((W i).whenP))(hP:T.Meter p 0)
local notation "φ"=>fun i=> Aperture.Phase.neckHeat (W i) (Q i) D O (y i)
local notation "ϕ"=> fun i=> Aperture.Phase.aisle (W i) (Q i) (y i)
local notation "t₀"=> fun i=> (W i).scaleO O (y i)
include hy hg hP
include hO hD hQ h
lemma tickedH : Tendsto φ Λ (𝓝 1) ∧ TaylorCap T k (b') (fun i=> Lantern.shade ((W i).Zc) 0-(W i).tenses O (y i)+Real.log (φ i)) (fun i j=> Z i j ((W i).tulip (y i))) := by
 let u:= stand D hO W h hD (hg.mono fun i hi=>by obtain ⟨⟨h,-⟩,-⟩:=hi; exact h) hP; let A:= enorth W h hy; obtain ⟨hh,hR⟩:= early_line u A hQ; let t:= receiptA u A; refine ⟨hh, ?_⟩
 refine TaylorCap.fit (t.pair hR) ?_ ?_; · filter_upwards with i; have hv:=amend (W i) hO (y i); rw [hv]; abel_nf; rfl -- check defeq
 intro j hj; filter_upwards [eventually_all.mpr (show ∀ c:Fin (j+1),∀ᶠ i in T.rail, Integrable (fun z=> someJ (Real.exp ∘ Catch.warmP ((W i).Ph) (V' i) (Q' i) (M₁ i) (Ψ i) ((W i).tulip (y i)) z) c.val) (Poll.sweep ((W i).Zc 0)⁻¹) from fun c=> Catch.ahead u A hQ (by have ht:=c.isLt; omega))] with i hi; exact Eq.symm (leading (W i) hO (Q i) ((W i).tulip (y i)) (j:=j) (fun p hp=> hi ⟨p,by omega⟩)) -- eta

include hW ht
lemma pricingH (s:ℝ) : hX (φ- (ϕ)/(t₀)) s:= by
 let S i:=T.cost i; let A i:=ϕ i / t₀ i; obtain ⟨h',hf⟩:=tickedH D hO W Q h hD hQ hg hy hP; let z':= min s (-1); let g(x:ι):= S x ^ z'; have hz : z'<0:= (min_le_right ..).trans_lt (by norm_num); have he:= ((Meter.pale T z').down hz); let E:= Real.exp (1+T₀); let u i:= Real.exp (-g i) * (φ i); let v i:=Real.exp (g i)* (φ i)+ E*Name.tired D (W i);
 have hF': hX φ 0:= ((Clock.Meter.const T (2:ℝ)).smaller (by have hp: Tendsto (fun i=> |φ i|) Λ (𝓝 |(1:ℝ)|):= continuous_abs.continuousAt.tendsto.comp h'; exact hp.eventually (gt_mem_nhds (by norm_num : |(1:ℝ)| < |(2:ℝ)|))|>.mono fun i hi=>le_of_lt hi))
 have ha(y:ι→ℝ)(h:hX y z') : hX (φ - fun i=> Real.exp (y i)*(φ i)) z':= by
    let p:ι→ℝ:=fun _=>0; have hp:= Clock.Meter.close (T:=T) Real.exp Real.contDiff_exp.contDiffAt (a:=p) tendsto_const_nhds (h.down hz) (show hX (p-y) z' from ((Meter.nil T z').sub h)); -- p binder
    exact ((hp.mul hF').weak (by simp)).eq_mem (Eventually.of_forall fun i=> by simp [p]; ring) -- simp likely huge
 let L:ι→ℝ:= u; refine ((squeezes (f:=φ) (u:=v) (ha (fun i=> -g i) ((Meter.pale T z').neg)) (((ha g (Meter.pale T z')).sub ((tired_cost D W h hD z').lscale E))|>.eq_mem ?_) (?_))).weak (min_le_left ..)
 · exact Eventually.of_forall fun i=>by unfold v; simp only [Pi.sub_apply,Function.comp_apply]; ring
 obtain ⟨Q₁,hQ₁,hL⟩:=h.legible; filter_upwards [hg, hy.stricter (by norm_num [vow] : -(1/2:ℝ)<vow), ht,hL, h.look.same,hW, Proper.bandwidth W h z' hz] with i hi hI hu hl hv hW hp; have hh:‖y i‖ < eaves G P.L (W i).whenP:= (le_abs_self _).trans_lt (by rw [hv] at hI; exact hI); apply Aperture.Phase.comparison (W i) (Q i) D O hl hO hi hh hu T₀ hW (g i); exact hp
lemma forecastP : (∀ᶠ i in Λ,0 < ϕ i) ∧ TaylorCap T k (b') (fun i=> Real.log (ϕ i)-(W i).basis O) (fun i j=> Z i j ((W i).tulip (y i))) := by
 obtain ⟨he,hV⟩:= tickedH D hO W Q h hD hQ hg hy hP; let A:= graded (k+1); let f:= φ; let g(i:ι):=ϕ i / t₀ i; have h':A<0:= (by unfold A graded; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) k]); have hp:hX (f-g) A:=pricingH D hO W Q h hD hQ T₀ hW hg hy ht hP A
 have ht:= uniform he hp h'; have hs(i):0< t₀ i:= mul_pos ((W i).born O hO) (Real.exp_pos _); have hu :∀ᶠ i in Λ,0<ϕ i:= (ht.eventually (lt_mem_nhds zero_lt_one)).mono fun i hi=> by have hi:0<ϕ i/t₀ i:=hi; exact (div_pos_iff_of_pos_right (hs i)).1 hi
 refine ⟨hu,hV.alteration ( (Clock.Meter.close (T:=T) Real.log (Real.contDiffAt_log.mpr one_ne_zero) he ht hp).neg.eq_mem (hu.mono fun i hi=> ?_))⟩; -- alteration diff
 change -(Real.log (φ i)-Real.log (g i)) = (Real.log (ϕ i)-(Real.log ((W i).overhead O)- Lantern.shade ((W i).Zc) 0))- (_- _+ Real.log (φ i)); unfold g; rw [Real.log_div hi.ne' (hs i).ne']; unfold scaleO; rw [Real.log_mul ((W i).born O hO|>.ne') (Real.exp_pos _).ne', Real.log_exp]; ring
end Phase
end YM.QuadraticLocal.Aperture
