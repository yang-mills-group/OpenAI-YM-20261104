import YM.WilsonCoeffUV.Product.Connected.Labels
/-!
# Heat program for a connected pair
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n:Side}{j r e k h s i a b:ℕ}{U:Type}{V E W ι D:Type*}{G:Gauge}
variable [Fintype U]
omit [Fintype U] in lemma pure_minus (A B:Gen ℝ U)(p:Pure A)(q:Pure B) : Pure (A-B):=fun k σ x=>congr_arg₂ (·-·) (p k σ x) (q _ σ x)
omit [Fintype U] in lemma stopped_sub (P Q:Layers ℝ U)(p:stops i P)(q:stops i Q): stops i (P-Q):=fun j e r t=>by rw [Pi.sub_apply,Pi.sub_apply,Pi.sub_apply,p j e r t,q j e r t,sub_zero]
lemma ramp_minus (P Q:Layers ℝ U)(p:stops i P)(q:stops i Q): ramp (P-Q) i=ramp P i-ramp Q i:=by
   apply lamp_ext; intro j e; let T:=P-Q; have ht:stops i T:=stopped_sub _ _ p q
   have he:= visible_add (finite_stops ht j e) (finite_stops q j e); rw [show T j e+ Q j e=P j e from sub_add_cancel ..] at he
   rw [map_sub,map_sub,glance ht,glance p,glance q,he,add_sub_cancel_right]
omit [Fintype U] in lemma dusk (P: Ink (Option U))(i j:ℕ): spanT i U (coeff j (brush none P))=(i+1) • spanT (i+1) U (coeff j P):=by rw [brush,blot_apply]; exact span_clock ..
lemma goLip_minus (G:Matrix U U ℝ)(P Q R:Ink (Option U)): goLip G P (Q-R)=goLip G P Q-goLip G P R:=by simp only [goLip,map_sub,mul_sub,smul_sub,Finset.sum_sub_distrib]
lemma goLip_two (G:Matrix U U ℝ)(P Q R:Ink (Option U)): goLip G P (Q*R)= Q *goLip G P R+ R*goLip G P Q :=by
   simp only [goLip,Derivation.leibniz,smul_eq_mul,mul_add,smul_add, Finset.sum_add_distrib,Finset.mul_sum,mul_smul_comm]; simp_rw [show ∀ (P Q R:Ink (Option U)),Q*(P*R)=P*(Q*R) from fun a b c=>mul_left_comm b a c]
-- heat law for connected two-parent. D nonzero effective vacuum only; P&Q each transient, common X-ray.
def estuary (G:Matrix U U ℝ)(D:Layers ℝ U)(P Q:Pal ℝ U):= bul G D (woad P Q)- tassel (bul G D P) (bul G D Q)
lemma shineEst (G: Matrix U U ℝ)(D:Layers ℝ U)(P Q:Pal ℝ U)(_p:∀ i,Pure (P i))(_q:∀ i,Pure (Q i))(i j): Pure (estuary G D P Q i j):= pure_minus _ _ (pure_bul G D (woad_pure P Q) i j) (tassel_pure _ _ i j)
lemma stopped (G:Matrix U U ℝ)(D:Layers ℝ U)(P Q:Pal ℝ U)(z:∀ h e r,r>2+e ∨ r+2*h>3*e → D h e r=0)(p:shellK i P)(q:shellK j Q): stops (i+j) (estuary G D P Q):= stopped_sub _ _ (stops_bul G z (i+j) (woad_shell P Q p q)) (tassel_stop _ _ (stops_bul G z i p) (stops_bul G z j q))
lemma estuary_base (G: Matrix U U ℝ)(D: Layers ℝ U)(P Q: Pal ℝ U) : estuary G D P Q 0=0:=by
    have hv (P:Pal ℝ U): bul G D P 0=P:= funext (bul_zero G D P)
    ext1 i; simp [estuary,tassel,hv]
lemma heatPath (G:Matrix U U ℝ)(D:Layers ℝ U)(P Q:Pal ℝ U)(z:∀ h e r,r>2+e ∨ r+2*h>3*e → D h e r=0)(hp:shellK i P)(hq:shellK j Q)(d:∀ i j,Pure (D i j))(p:∀ i,Pure (P i))(q:∀ i,Pure (Q i)):
    let X:= ramp (bul G D P) i; let Y:=ramp (bul G D Q) j; let Z:=ramp D 2; let T:=ramp (estuary G D P Q) (i+j); brush none T=goLap G T+goLip G Z T+goLip G.transpose Z T + goLip G X Y + goLip G.transpose X Y:=by
    intro X Y Z T; let R:=ramp (bul G D (woad P Q)) (i+j)
    have he:T=R-X*Y:= by unfold T R estuary; rw [ramp_minus _ _ (stops_bul G z _ (woad_shell P Q hp hq)) (tassel_stop _ _ (stops_bul G z i hp) (stops_bul G z j hq)),ramp_joint _ _ (stops_bul G z i hp) (stops_bul G z j hq)]
    have ht: brush none R=goLap G R+goLip G Z R+goLip G.transpose Z R:= lamp_bul z (woad_shell _ _ hp hq) (woad_pure P Q) d G
    have hv: brush none X= goLap G X+goLip G Z X+goLip G.transpose Z X:=lamp_bul z hp p d G; have hY: brush none Y=goLap G Y+goLip G Z Y+goLip G.transpose Z Y:=lamp_bul z hq q d G
    rw [he,map_sub,goLip_minus,goLip_minus,map_sub,Derivation.leibniz, hv,hY, ht,goLip_two,goLip_two,lap_split]; simp only [smul_eq_mul]; ring
lemma estuary_next (G:Matrix U U ℝ)(D:Layers ℝ U)(P Q:Pal ℝ U)(z:∀ h e r,r>2+e ∨ r+2*h>3*e → D h e r=0)(hp:shellK i P)(hq:shellK j Q)(d:∀ i j,Pure (D i j))(p:∀ i,Pure (P i))(q:∀ i,Pure (Q i))(k e:ℕ):
   let X:=bul G D P; let Y:=bul G D Q; let Z:=estuary G D P Q
   Z (k+1) e=((k+1:ℕ):ℝ)⁻¹ • (ripple G (Z k e)+ravel G D Z k e+ravel G.transpose D Z k e+ravel G X Y k e+ravel G.transpose X Y k e):=by
   intro X Y Z; have hx:stops i X:=stops_bul G z _ hp; have hy:stops j Y:= stops_bul G z _ hq; have hz: stops (i+j) Z:=stopped G D P Q z hp hq; have hD:stops 2 D:=fun h e r H=>z h e r (by omega)
   have hi := heatPath G D P Q z hp hq d p q
   change brush none (ramp Z _) = goLap G (ramp Z _)+goLip G (ramp D _) (ramp Z _)+ goLip G.transpose (ramp D _) (ramp Z _)+goLip G (ramp X _) (ramp Y _)+ goLip G.transpose (ramp X _) (ramp Y _) at hi
   have he:= congr_arg (fun v:Ink (Option U)=> spanT k U (coeff e v)) hi
   have hA:∀ i j,Pure (Z i j):= shineEst G D P Q p q; have hB:∀ i j,Pure (X i j):=pure_bul G D p; have hC:∀ i j,Pure (Y i j):=pure_bul G D q
   have hf : Pure (Z (k+1) e):= hA _ _
   have hh H:= finite_ravel (e:=e) (j:=k) hD hz H; have h' H:= finite_ravel (e:=e) (j:=k) hx hy H; have hu:=finite_ripple G (finite_stops hz k e); apply gen_inj (finite_stops hz ..) (finite_μ (finite_add (finite_add (finite_add (finite_add hu (hh G)) (hh G.transpose)) (h' G)) (h' G.transpose)) _) hf (fun i=> (((((pure_ripple G (hA k e) i).add (pure_ravel G D Z k e i)).add (pure_ravel G.transpose D Z k e i)).add (pure_ravel G X Y k e i)).add (pure_ravel G.transpose X Y k e i)).smul (((k+1:ℕ):ℝ)⁻¹))
   have hc := finite_stops hz (k+1) e
   simp_rw [map_add] at he; rw [dusk,glance hz,lamp_count _ _ hz _ _ (hA k e),lip_count _ _ _ hD hz k e d hA,lip_count _ _ _ hD hz k e d hA, lip_count _ _ _ hx hy k e hB hC,lip_count _ _ _ hx hy k e hB hC] at he
   rw [visible_μ (finite_add (finite_add (finite_add (finite_add hu (hh G)) (hh G.transpose)) (h' G)) (h' G.transpose)),visible_add (finite_add (finite_add (finite_add hu (hh G)) (hh G.transpose)) (h' G)) (h' G.transpose), visible_add (finite_add (finite_add hu (hh G)) (hh G.transpose)) (h' G),visible_add (finite_add hu (hh G)) (hh G.transpose),visible_add hu (hh G),←he,← Nat.cast_smul_eq_nsmul (R:=ℝ), smul_smul,inv_mul_cancel₀ (by positivity),one_smul]
end YM.WilsonCoeffUV.Mer
