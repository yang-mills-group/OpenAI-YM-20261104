import YM.OPE.Compatible.Speke.Dirt
/-!
# Close the two-sing shelves
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nestle
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
open Balsam Port Extra.FD.OPE
open Pose
variable {U:Gloam}{d c s:ℝ}{K:ℕ→ℕ}{k j l m:ℕ}{X Y Z: Panels} {A:Zem}{p q t:Pose}
def Vener (A:Zem)(c:ℝ):Prop:=∀ x y u v,A (basePair x y) (basePair u v)= c*(x*v-y*u)
lemma Vener.flip (h:Vener A c): Vener A.flip (-c):=by intro x y a b; change A _ _=_; rw [h];ring
lemma D_duo {V W:Axis→ E4→ℝ}{Q:E4→ℝ}(hp:∀ i,epic (V i))(hb:∀ i,epic (W i))(hQ:epic Q)(hc:Vener A c)(hs:0<s)(a b:Axis):
   let X:=basePair (V a) (V b); let Y:= basePair (W a) (W b)
   c*fineI s (ThetaS V W a b*Q)= ∑ p:Fin 4×Fin 4, chi A p* fineI s (X p.1* Y p.2 * Q):=by
   intro X Y; let G(p:Fin 4×Fin 4):= X p.1* Y p.2 * Q; let F(p):= chi A p • G p; have hh(i:Fin 4):epic (X i)∧epic (Y i):=by fin_cases i <;> exact ⟨hp _,hb _⟩
   have he(i):epic (F i):= fun x hx=> (epic_m (epic_m (hh _).1 (hh _).2) hQ x hx|>.const_smul (chi A i))
   rw [← iSc, show c • (ThetaS V W a b*Q)=∑ p:Fin 4×Fin 4,F p from ?_, iSumK _ F hs (fun i _=> he i)]; exact Finset.sum_congr rfl fun i _=> iSc ..
   funext x; have hx(i): (X i) x=basePair ((V a) x) ((V b) x) i:=by fin_cases i <;> rfl
   have hy(i): (Y i) x=basePair ((W a) x) ((W b) x) i:=by fin_cases i <;> rfl
   rw [Finset.sum_apply]; simp_rw [F,G,Pi.smul_apply,Pi.mul_apply,hx,hy,smul_eq_mul]; unfold ThetaS
   simp only [Pi.sub_apply,Pi.mul_apply]
   conv_lhs => rw [← mul_assoc,←hc,chil A, Finset.sum_mul]
   exact Finset.sum_congr rfl (fun i _=>by ring)
lemma sacred (hs:Woody U K d)(hm:m+4=k+1+(p.heat+1)+(q.heat+1))(hp:ShiftRay U d k X)(hc:Vener A c): Fruit U m (Triad K A X (SinB p) (SinB q)) 0:=by
   obtain ⟨t,ht,H⟩:=hs.funding; let P:=SinB p; let M:=nuF p+nuF q; let V(i:Axis):=eve U k (M+1) (X i); have hh(i):=hp.cloud (M+1) i
   let f(a b):=fineI U.q'⁻¹ (ThetaS (p.pureD []) (q.pureD []) a b *TauS V a b)
   have hv:0<U.q'⁻¹:=inv_pos.mpr (zero_lt_one.trans U.qsub)
   rw [show 0 = half_sum (fun a b=>c*f a b) from by unfold half_sum; rw [← Finset.mul_sum,show (∑ a:PlaqAxes,f a.1.1 a.1.2)=0 from balsamic p q hv hh, mul_zero]]; apply receipt (f:=fun a b=>c*f a b)
   intro a b; have Ht:=nu_shape p; have Hz:=nu_shape q; let g:= dart X a b
   rw [show m=k+1+(nuF p+nuF q) from by omega, show c*f a b=_ from D_duo (p.hint []) (q.hint []) (Q:=TauS V a b) (epic_s (fun x hx=>(sph_der (hh a) b).size.smooth.contDiffAt) (fun x hx=>(sph_der (hh b) a).size.smooth.contDiffAt)) hc hv a b]
   apply hotSeries; intro v
   let L:=plume P a b v.1 0; let B:= plume (SinB q) a b v.2 0
   rw [show TimeA K _ _ _ a b v= Oct K (L*B) g from (show TimeA K X (SinB p) (SinB q) a b v= _ from funext fun i=> Finset.sum_congr rfl fun x hx=> by change g i x*L x*B x=(L x*B x)*g i x;ring), ← drop_top a b M hp.ports]; exact twineB (lettr _ _ _ _) (lettr _ _ _ _) (plant _ _ hp.ports) hs.station ht H
lemma rotor (hs:Woody U K d)(hm:m+4=p.heat+1+1+(q.heat+1)+k)(hp:ShiftRay U d k X)(hc:Vener A c): Fruit U m (Triad K A (SinB p) (SinB q) X) 0:=by
   obtain ⟨t,ht,H⟩:=hs.funding; let P:=SinB p; let Y:=SinB q; let M:=nuF p+1+nuF q; have hc':M=nuF p+nuF q+1:=by omega
   let V(i:Axis):=eve U k M (X i); have he:M=p.aLen [0]+q.aLen []:= by unfold M nuF Pose.aLen; simp; omega
   have hh(i):Spherical (V i) (p.aLen [0]+q.aLen []):= he ▸ hp.cloud M i; let A':= q.pureD []; let B:= p.OmegaS; let f(a b):=fineI U.q'⁻¹ (ThetaS A' V a b* B a b); have hv:0<U.q'⁻¹:=inv_pos.mpr (zero_lt_one.trans U.qsub)
   rw [show 0=half_sum (fun a b=> c*f a b) from by unfold half_sum; rw [← Finset.mul_sum, show (∑ a:PlaqAxes,f a.1.1 a.1.2)=0 from p.cerate q hv hh (by unfold V; rw [hc']; exact hp.core),mul_zero]]; apply receipt (f:=fun a b=>c*f a b); intro a b
   have Ht:=nu_shape p; have Hz:=nu_shape q; let F:=dart P a b 0; have hx:=lettr_step p a b
   rw [show m=k+M from by omega,show c*f a b=_ from D_duo (q.hint []) (fun a=>show epic (V a) from fun x h=> (hh a).size.smooth.contDiffAt) (Q:=B a b) (lettr_step p a b|>.fence) hc hv a b]
   apply hotSeries; intro v; let G:=plume Y a b v.1 0
   rw [show TimeA K (SinB p) (SinB q) X a b v=Oct K (F*G) (plume X a b v.2) from rfl, ← pull_top a b M v.2 hp.ports, mul_comm (_*_ : E4→ℝ) (B a b),← mul_assoc]; exact twineB hx (lettr _ _ _ _) (parcelC _ _ _ hp.ports) hs.station ht H
end YM.OPE.Nestle
