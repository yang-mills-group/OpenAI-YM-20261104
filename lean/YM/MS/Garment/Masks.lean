import YM.MS.Garment.Volume
/-!
# All ranks and support coherence

Even when Ward or ℓ only computed on bulk Course,
 the limit/rank equations work on those supports without a prescribed extension. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Momentum Metric
open scoped Topology ContDiff
open Color Book
variable {G:Gauge}{b c:Bool}{m n:ℕ}{z:ℂ}{F H: Mob G}{U:Rip G}{i j k:ℤ}
-- cost h horizon because integer negative vacuum at ≤1. use EqOn for net conj.
structure zeroTest (b:Bool)(F:Mob G)(r:ℤ): Prop where
    passes n (w: Legs (Shore G n)): (w.length:ℤ)=r→ Course b w → F n w=0
lemma roof_ocean (hp:Form0 b F)(ht:Knot b U)(h:zeroTest c F (i+2))(hx:z∈Town): zeroTest c (ocean z U F) i where
   passes n l hl hC:= by
       have hz {m:ℕ}(he:n≤m): Course c (Arts.lift he l):= by intro u; rw [lifts_net,hC u,map_zero] -- p binder not used
       have hv {m:ℕ} (w:Legs (Shore G m))(hw:w.length=i)(hc:Course c w)(p:Momentum (L m)) : trc (U m) p (F m) w=0:= by rw [at_trc]; refine Finset.sum_eq_zero fun a _=> Finset.sum_eq_zero (fun b _=>?_); rw [h.passes m _ (by simp [hw]; omega) (fun hi=>by simp [hc hi]), mul_zero]
       refine Garment.erase ht hp hx (centroid l) (fun p=>?_); let M:=n+1; let X:=Arts.lift (Nat.le_succ n) l; let A:= F M
       change Wtr z U F p X=_; rw [combo (U:=U) z M, Pi.add_apply,Pi.smul_apply,Pi.sub_apply]; simp_rw [tallyN hp.token ht.token (le_refl M), tallyN hp.token ht.token (Nat.le_succ M)]; unfold X; simp_rw [lifts_link]
       rw [hv (Arts.lift (Nat.le_succ n) l) (by simp [Arts.lift,hl]) (hz _) (Left _ p), hv (Arts.lift (n:=M+1) (by unfold M; omega) l) (by simp [Arts.lift,hl]) (hz _) (Left _ p)]; simp
-- k=0 compatibility. Rank lift operations eta.
lemma zeroIssue (h:Goods i F): Issue i F := fun n l hl=> ranks_off h l (by omega)
lemma issue_pl (he: Issue i F)(hp: i<j): zeroTest b F j:= ⟨fun m v hx _=> he m v (by omega)⟩
lemma cap_ocean (hp:Form0 b F)(ht:Knot b U)(hx:z∈Town)(he:Issue i F): Issue (i-2) (ocean z U F):= fun m l hl=> (roof_ocean (c:=false) hp ht (issue_pl he (show i < (l.length:ℤ)+2 by omega)) hx).passes m l rfl (fun v=>Bool.noConfusion v)
lemma goods_pl (he:Goods i F)(hp:j≠i): zeroTest b F j:= ⟨fun m v hx _=> he m v ((mod_int v) ▸ (hx.symm ▸ hp))⟩ -- direction check typo
lemma goods_o (hp:Form0 b F)(ht:Knot b U)(hx:z∈Town)(he:Goods i F): Goods (i-2) (ocean z U F):= fun n l hl=> roof_ocean (c:=false) hp ht (goods_pl he (show (l.length:ℤ)+2≠i by rw [mod_int] at hl; omega)) hx|>.passes n l rfl (fun v=>Bool.noConfusion v)
lemma whole (hp:reverseF U)(he: Issue i F)(hx:Issue j H): Issue (i+j-2) (arbor U F H):= by
   intro n l h; unfold arbor tree; rw [scatter_congr _ _ _ (fun _ _=>(0:ℂ)) ?_]; exact map_zero (allocate ..); intro u v ht; rw [convertR (hp n)]; refine Finset.sum_eq_zero fun a _=> Finset.sum_eq_zero fun b _=> ?_; unfold radius; dsimp only; obtain hz:= split_length ht; by_cases hL:i<(u.length:ℤ)+1; · rw [he n _ (by simpa using hL)]; simp;
   rw [hx n _ (by simp; omega), mul_zero]
lemma mask_Q (Q:Shade G)(h:i=j): spot i (portZ Q F)=portZ Q (spot j F):= by
    ext m l; subst j; unfold portZ; change Book.mask i _ l= _; by_cases hx : (l.length:ℤ)=i; · rw [Book.enough _ hx, visit_Z,visit_Z]; apply Plane.visit_agree; intro u a v he; apply Finset.sum_congr rfl; intro j hj; congr 1; exact (spotted (by rw [← he] at hx; simpa using hx)).symm
    rw [Book.strange _ hx,visit_Z]; rw [← visit_zero (l), Plane.visit_agree]; intro u a v h; refine Eq.symm (Finset.sum_eq_zero (fun j hj=>?_)); rw [spotsOff (by rw [← h] at hx; simpa using hx),mul_zero] -- rewrite inspect
lemma cap_Q (Q:Shade G)(h:Issue i F): Issue i (portZ Q F) := by
      intro m l hm; rw [← spotted (F:=portZ Q F) (show (l.length:ℤ) = l.length from rfl),mask_Q Q rfl]; rw [show spot (l.length:ℤ) F=0 from funext ?_, ← upcoming,map_zero]; rfl
      intro v; funext k; by_cases he:(k.length:ℤ)=l.length; rw [spotted he, h v k (by omega)]; rfl; exact spotsOff he
lemma spot_o (hp:Form0 b F)(ht:Knot b U)(hx:z∈Town): spot i (ocean z U F)=ocean z U (spot (i+2) F):= by
    ext n l; by_cases hL:(l.length:ℤ)=i; · rw [spotted hL]; apply sub_eq_zero.mp; change (ocean z U F-ocean z U (spot (i+2) F)) n l=_; rw [← oceanRsub ht hp (spotM _ hp) hx]; apply (roof_ocean (c:=false) (hp.sub (spotM _ hp)) ht ?_ hx).passes n l hL (fun p=>Bool.noConfusion p); constructor; intro n l h hp; rw [Pi.sub_apply,Pi.sub_apply,spotted h,sub_self]
    rw [spotsOff hL]; exact Eq.symm (ranks_off (goods_o (spotM _ hp) ht hx (goods_sp F (i+2))) l (by omega))
end YM.MS.Garment
