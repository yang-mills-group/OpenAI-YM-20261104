import YM.FVA2.TownLedger
/-!
# Explicit identification of the exponent, on & before coarsening

True by analytic local germs with the actual independent costs. Not postulating the stepped
projection equals pushing remainders.And not mixing the two weights used in block noise and
Haar factors. Abbreviate `J.scale` powers away before forming ratios. Includes all clock-correction
powers $g_j = g_N z_j^-{1/2}$ through all levels. Doesn't assert a selected formal reset in
 any other trajectory satisfies any forecast conditions. Quantitative path bounds not here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Fares
open Function Filter Set Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice
open Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage
open MeasureTheory.Measure (IsAddHaarMeasure)
open PowerSeries Finset StationaryMarks
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}

section exponent
variable {E K:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (w:PowerSeries ℝ)(f:E→ℝ)(hf:Radial.Stationary f)(c:ℝ)(v:E)
-- `roll ofConstSupport η`. Math observation hℏ.Interpretation.
lemma shadow : w + X* Tracks.shadow w=C (term w 0):= by
     apply PowerSeries.ext; intro i; cases i with
     | zero=> simp [coeff_C,term]
     | succ i=> rw [map_add, coeff_succ_X_mul]; simp only [Tracks.shadow,map_neg,Tracks.deduct,coeff_mk,term, Nat.succ_eq_add_one,coeff_C, if_neg (by omega : i+1 ≠ 0)]; rw [Nat.add_comm 1 i, add_neg_cancel]
lemma address : carry w + X* carry (Tracks.shadow w)=roll (E:=E) (term w 0):= by rw [ ← show Stack.carry (E:=E) X=X from map_X _, ← map_mul (carry), ← map_add,shadow, carry, map_C ]; rfl
include hf
lemma overdue (i:ℕ)(hx:i<2): coeff i (rise f)=0:= Subtype.ext (funext fun x=> by rw [rise,coeff_mk]; cases i with| zero=> exact (jet_zero f x).trans hf.base0 | succ j=> obtain rfl:j=0:=(by omega); exact hf.base1 x)

/-- log action precise cost: multiply by coupling² before discarding and get this single expression.
 For p starting at order 2 (Stationary). `pay` has zero zeroth by `OpenSlots.stipend`.
-/
lemma price_charge : X^2 * (pay w f - roll (term w 0)* C (coeff 2 (rise f)))= -(carry w) * rise f:= by
     let f0:= rise f; let p: Ticket E:= X; let v:= Tracks.shadow w; let c:= roll (term w 0) (E:=E)
     have he2: ∀ i<2,coeff i (-f0)=0:= fun i h=> by rw [map_neg, overdue f hf i h, neg_zero ]; -- unfold f0?
     have hp: p^2 * Stack.drop 2 (-f0)=-f0:= Stack.recover 2 _ he2; have hv: p * Stack.drop 1 f0=f0:= by simpa [p] using! ( Stack.recover 1 f0 (fun i h=> overdue f hf i (by omega)) )
     unfold pay advancing; change p^2 * ( c * (Stack.drop 2 (-f0) + C (coeff 2 f0)) + carry v*Stack.drop 1 f0 - c*C (coeff 2 f0) )= -carry w*f0; rw [mul_add, show c * Stack.drop 2 _+_+_- c*C (coeff 2 f0)= c * Stack.drop 2 (-f0)+carry v*Stack.drop 1 f0 from (by ring), mul_add, mul_left_comm _ c,hp, show p^2*(carry v* Stack.drop 1 f0)= p*carry v*f0 from by nth_rw 2 [←hv]; ring, ← show carry w+p*carry v=c from address w ]; ring

lemma carries_jet (hw:constantCoeff w=1): C (term w 0)=1 ∧ (constantCoeff (pay w f)=0 ∧ X^2*(Stack.read v (pay w f) - C (jet f 2 v))=-w*Stack.read v (rise f)) := by
     have ht: term w 0=1:=(by rw [term,coeff_zero_eq_constantCoeff_apply,hw]); refine ⟨ ht ▸ map_one C, OpenSlots.stipend w f hf,?_⟩; obtain he:= congr_arg (Stack.read v) ( price_charge w f hf ); rw [map_mul,map_sub,map_mul,map_mul, rollThrough, ht,map_one,one_mul,map_pow,show ∀ x:E,(Stack.read x) X=X from fun x=>PowerSeries.map_X _, map_neg, load ] at he; exact ( Eq.trans (by rw [ show jet f 2 v= (coeff 2 ( rise f )).val v from (by rw [rise,coeff_mk]) ]; rw [ Stack.read, map_C ]; rfl ) he ) -- eq placeholder
end exponent
end YM.FVA2.Fares
