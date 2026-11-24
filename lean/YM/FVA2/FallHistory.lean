import YM.FVA2.CityHistory
/-!
# Assemble full periodic path costs with successive eliminations

No theta modes killed. Genuine formal coefficient prescription: coupled in f (directional rough
 β prices only through formal rebase). At each step, input Unit.W(Q) = accumulated vacuum
 interaction except parent Haar; at parent end exactly Q=reduced and W=Joint.uptake.
 Weight z_{1} multiplies step penalty.Trees: ROOT OF EACH block tree.T.S not Landau
 ensemble.Remaining coarse variables are all log links V.U. Weighted program inherits every
 birth, exactly re-closes into full Stamp and conditional denominator.

Everything proved from one History `Descent` room (ellipticity supplied by actual patch `Bid.Larger`;
 see schedule construction later for aligned Path). Not comparing actual smooth remainders at
 this stage or claiming equality of *scalar* answers on full torus vs inversion.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.CityHistory
open Function Filter Set Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice
open Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage
open MeasureTheory.Measure (IsAddHaarMeasure)
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

variable {G:Gauge} {c f n : Side}
variable (S:StepData c f)(T:Forest S.ratio)(d:Descent n f)(t:d.Tags)(b:S.Choices)
variable (h:Bid.Larger (G:=G) S)(H:d.Room G)
local notation "D"=> Descent.push S T d
local notation "Ψ"=> (jointV d t (G:=G))
local notation "Λ"=> jointV (Descent.push S T d) ( show (Descent.push S T d).Tags from (b,t) ) ( G:=G )
local notation "χ"=> CityHistory.fusion G S T d
local notation "v"=> gate G S T
local notation "ξ"=> partΧ G S T d
local notation "Υ"=> partΥ G S T d
local notation "B"=> tax (G:=G) S T b
local notation "K"=> Pins G c
local notation "Y"=> Future G S T
local notation "E"=> Coordinates G d
local notation "ωg"=> (expandGauge («K»:=Pins G c) χ).toContinuousLinearEquiv.toContinuousLinearMap
local notation "Δg"=> (expandGauge («K»:=Pins G c) χ).toLinearMap
local notation "fk"=> Quadratic.genesis 1 ( tax (G:=G) S T b )
local notation "Ω"=> innerV Λ χ

lemma part_s (x : E × (Y×K)): partΧ G S T d ( (ωg) x)= toward v x:= by rcases x with ⟨p,x,y⟩; exact hx_part S T d ..
lemma part_t (x : E × (Y×K)): partΥ G S T d ( (ωg) x)= x.2:= by rcases x with ⟨p,x,y⟩; exact hy_part S T d ..
-- shadow Τ accidental. use direct lift
local notation "Tₓ"=> (show (Descent.push S T d).Tags from (b,t))
lemma carried_phase : consume (Descent.push S T d) Tₓ 1 ∘ (ωg)=consume d t 1 ∘ (toward («E»:=E) ( gate G S T )).toContinuousLinearMap + B ∘ (ContinuousLinearMap.snd ℝ E (Y×K)) := by
   funext i; rw [Function.comp_apply, at_step,part_s,part_t ]; exact congr_arg₂ (·+·) rfl (one_mul _) -- defeq convert upβ

private lemma tax_algebra {F X:Type}[NormedAddCommGroup F][NormedAddCommGroup X][NormedSpace ℝ F][NormedSpace ℝ X]
    {b:F×X→ℝ}{f:X→ℝ}{q:F×X→ℝ}(h:ContDiffAt ℝ ω b 0)(hq:ContDiffAt ℝ ω q 0)(he:b=q+f ∘ ( ContinuousLinearMap.snd ℝ F X)) : ContDiffAt ℝ ω f 0:= by
     let m:=ContinuousLinearMap.inr ℝ F X; suffices ht:f=b ∘ m - q ∘ m by rw [ht]; exact ContDiffAt.sub (h.comp (f:=m) 0 m.contDiff.contDiffAt) (hq.comp (f:=m) 0 m.contDiff.contDiffAt);
     rw [he]; funext p; change f p=q (m p)+ f p - q (m p); rw [add_comm,add_sub_cancel_right]
lemma tax_hot (h:S.patch.Branches S.kernel G): ContDiffAt ℝ ω ( tax (G:=G) S T b ) 0:= by
     let L: Descent f f:= .nil; let H:L.OK G:=trivial; let t:L.Tags:= (); let d:= Descent.push S T L;
     refine tax_algebra ?_ ?_ (carried_phase (G:=G) S T L t b); -- eliminate E
     · let C:= ( expandGauge («K»:=Pins G c) ( CityHistory.fusion G S T L ) ).toContinuousLinearEquiv.toContinuousLinearMap; apply ContDiffAt.comp (f:=C) ; rw [map_zero]; exact thermal d _ ⟨h,H⟩ 1; exact C.contDiff.contDiffAt
     let X:= (toward («E»:= Coordinates G L) ( gate G S T )).toContinuousLinearMap; apply ContDiffAt.comp (f:=X); rw [map_zero]; exact thermal L t H 1; exact X.contDiff.contDiffAt

lemma tax_same (h:S.patch.Branches S.kernel G)(u:S.Choices): tax (G:=G) S T u=ᶠ[𝓝 0] B:= by
     let M:= fun x: Y × K=>T.drape (expLinks G T.Free x.1); have ht:Tendsto M (𝓝 0) (𝓝 1):= by
         have hv: Tendsto (fun x:Y×K=>pext G S T x.1) (𝓝 0) (𝓝 0):= by change Tendsto (pext G S T ∘ (Prod.fst:Y×K→Y)) (𝓝 0) (𝓝 0); simpa using (( (pext G S T).continuous_of_finiteDimensional.comp continuous_fst ).tendsto (0:Y×K) )
         have hw : Tendsto (expLinks G (Edge (Site f))) (𝓝 0) (𝓝 1):= by rw [← identity_zero (I:=Edge (Site f)) (G:=G) ]; exact Inherit.neighborhood_exp.continuousAt.tendsto -- namespace?
         apply (hw.comp hv).congr; intro x; exact inserts ..
     filter_upwards [ ht.eventually (FormalOPE.RG10.BlockGauge.all_t S h u 1 rfl) ] with x hx; unfold tax tagEnergy noiseEnergy; rw [show S.prediction ( _ ) b= _ from hx b]

-- integrated cost. h parameters (on StepData) prove room at all points
include h H
lemma inherits_proof : innerV Λ χ = Tandem.Luggage.inherits Ψ (Quadratic.genesis 1 (tax (G:=G) S T b)) (gate G S T):= by
    apply only_P; apply Quadratic.records; intro x
    let F0:=consume d t 1 ( G:=G ); let F1:=consume ( D ) Tₓ 1 ( G:=G ); let u:= (toward («E»:=E) ( v )).toContinuousLinearMap; let p:=ContinuousLinearMap.snd ℝ E (Y×K); let L:=Λ
    have hz: d.OK G:= room_ok d H; have hb : ( D ).OK G:=⟨h.1,hz⟩; have hf:= tax_hot S T b h.1; have hv :ContDiffAt ℝ ω F0 (u 0):= by rw [map_zero]; exact thermal d t hz 1
    have ht : jet ( F1 ∘ (ωg) ) 2 x=jet F0 2 (u x)+jet B 2 x.2:= by
       unfold F1; rw [ carried_phase, Inherit.plus (a:=F0 ∘ u) (b:=B ∘ p) (2:ℕ) (hv.comp _ u.contDiff.contDiffAt) ( hf.comp (f:=p) (0:E×(Y×K)) contDiffAt_snd ), GermLaplace.jet_pull u _ ((thermal d t hz 1).of_le le_top), GermLaplace.jet_pull p _ (hf.of_le le_top) ]; rfl
    rw [ GermLaplace.jet_pull (ωg) _ (( thermal ( D ) Tₓ hb 1 ).of_le le_top), ← progress d t, ← progress ( D ) Tₓ ] at ht; -- price likely F0 and F1 definitional?
    unfold Quadratic.flourish; rw [toll]; change (Λ).flourish ((ωg) x)= (Ψ).flourish (u x)+( Quadratic.genesis 1 (tax (G:=G) S T b)).flourish x.2; rw [Quadratic.native,show term 1 0=(1:ℝ) from PowerSeries.coeff_zero_one,one_mul]; linarith

local notation "H₀"=> ( show ( Descent.push S T d ).Room G from ⟨h,H⟩ )
local notation "hq"=> gives (Descent.push S T d) Tₓ H₀
local notation "hE"=> gives d t H
local notation "hu"=> Tandem.stays Λ χ hq

def gateQ (R:Quadratic (Pins G f)) : Quadratic (Future G S T × Pins G c):= Quadratic.addOn (Quadratic.drag (gate G S T) R) (Quadratic.genesis 1 (tax (G:=G) S T b))
local notation "Q"=> gateQ S T b (retained d t H)

lemma inherits_w : Quadratic.reduced Ω hu = gateQ S T b (retained d t H):= by
    obtain he:= port_charge Ψ hE fk v; refine Eq.trans ?_ he; congr 1; exact inherits_proof S T d t b h H

lemma useful : ( Quadratic.core (gateQ S T b (retained d t H))).RespectsPrice := (inherits_w S T d t b h H) ▸ Tandem.stays_second Λ χ hq
local notation "hY"=> useful S T d t b h H
lemma future : Quadratic.reduced Q hY= retained ( D ) Tₓ H₀ := by
    have hb:= Tandem.readf Λ χ hq; apply Eq.trans ?_ (show Quadratic.reduced (Quadratic.reduced (Ω) hu) (Tandem.stays_second Λ χ hq)= _ from only_P _ _ (LinearMap.ext (fun i=> LinearMap.ext (fun p=> hb i p)))); congr 1; exact (inherits_w S T d t b h H).symm

end YM.FVA2.CityHistory
