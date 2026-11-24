import YM.Frontier6.Bouquet.Meter.Jets
import YM.Frontier6.Bouquet.Anise.Reunion

/-! Moving the geometric conditions in the finite-regulator identity to
 the slices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q R U:Ensemble} (h:Free P Q)
lemma Veins.susp_shorn {p:Room} (Q P:Ensemble): T.susp Q P p=T.susp Q P ((ontoSpace (fiber Q) p).val) := by
    unfold Veins.susp Veins.cutter; apply prod_congr rfl; intro u hu; obtain ⟨v,hv,hF⟩:= encloses.mp (Finset.mem_sdiff.mp hu).1; exact congr_arg (fun z=> 1 - Normal.shrink _ (T.range u) z) (on_lower ((normal_sub hF).trans (home_sub hv)) p)

set_option quotPrecheck false
local notation "㏑"=> fiber (Ensemble.merge h)
def tower (Q U: Ensemble) (P:Place): Full P →ₗ[ℂ] Full P:= paneM (Q:=P) (T.susp Q U ∘ (fiber Q).subtypeL) ((T.cutter_smooth (scars Q U)).comp (fiber Q).subtypeL.contDiff)
lemma tower_eq (Q U:Ensemble){P:Place}(f: Full P)(x:P): tower T Q U P f x=T.susp Q U x.val*f x:= by
   change T.susp Q U (ontoSpace (fiber Q) x.val).val * f x= _; rw [← Veins.susp_shorn]
lemma tower_film {he:Free R U}(hR:R≤P)(hU:U≤Q)(f:Full (fiber (merge h))): T.film (merge h) (merge he) f= tower T P R _ (tower T Q U _ f):=by ext1 x; rw [T.filmed,T.susp_products h he hR hU, Pi.mul_apply, tower_eq,tower_eq,mul_assoc]
lemma tower_slot (f:Full (fiber P)): tower T P R _ f= T.film P R f:=by ext1 x;rw [tower_eq,T.filmed]
variable (f:Full (fiber (merge h))) (p:Trip A R)(q:Trip A U)

def received (v:Margin Q U) : Full (fiber P):= (merged h).sampleR (insideCL loft_le v) (train _ (costsD A q) (tower T Q U _ f))
include h in
lemma transmission (g:Tandem.Essay (fiber P))(a:Tandem.Essay (fiber (merge h)))(he: Elevator (merged h).lft g a)(hU:U≤ Q)(v: Margin Q U): received A T h (a f) q v=g (received A T h f q v):=by unfold received; have hh:tower T Q U _ (a f)=a (tower T Q U _ f):=(merged h).wed (g:=T.susp Q U ∘ (fiber Q).subtypeL) ((T.cutter_smooth _).comp (fiber Q).subtypeL.contDiff) g a he f; rw [hh, (merged h).plane_motion (s:=costsD A q) (fun i hi=> plan_sub hU (courses_in A q i hi)) g a he,(merged h).sample_move g a he]; -- tower unfold rw
variable {he: Free R U}(hR:R≤P)(hU:U ≤ Q)
lemma together_ins (u:Margin P R)(v: Margin Q U) : insideCL (Q:=fiber (merge h)) loft_le ((adds_macro h (K:=he) hR hU).together (u,v))= (merged h).together (insideCL loft_le u,insideCL loft_le v):=rfl -- may need subtype
set_option maxHeartbeats 600000 
include he hU hR
lemma impression (u:Margin P R)(v:Margin Q U): train _ (costsD A (palette A he (p,q))) (T.film (merge h) (merge he) f) (insideCL loft_le ((adds_macro h (K:=he) hR hU).together (u,v))) = train _ (costsD A p) (T.film P R (received A T h f q v)) (insideCL loft_le u):=by
    rw [palette_score,tower_film T h hR hU,together_ins h (he:=he) hR hU, trains_add]
    let g:= tower T Q U _ f; let W:=tower T P R (fiber (merge h)); let V:=T.film P R;
    have hV:Elevator (merged h).lft V W:= Elevator.panes _ _ ((T.cutter_smooth (scars P R)).comp (fiber P).subtypeL.contDiff)
    rw [(merged h).plane_motion (s:=costsD A q) (fun i hi=> plan_sub hU (courses_in A q i hi)) V W hV] -- W defeq?
    -- consume P deriv
    rw [← Tandem.sample_right];
    have hw (f'): (merged h).sampleR (insideCL loft_le v) (train _ (costsD A p) f')= train _ (costsD A p) ((merged h).sampleR (insideCL loft_le v) f'):= train_restricted _ _ _ _ (fun i hi=>plan_sub hR (courses_in A p i hi))
    rw [hw, (merged h).sample_move V W hV]; rfl
end YM.Frontier6.Bouquet
