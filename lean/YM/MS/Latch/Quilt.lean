import YM.MS.Latch.Prong
/-!
# General ledge. Past source estimate, comfort convergence. No unknown prelimits. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Latch.Job
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Belt
open scoped Topology ContDiff Interval
variable {G:Gauge}{I E:Type} [NormedAddCommGroup E][NormedSpace ℝ E]{b c:Bool}{K:Belt I}
 {F H:Moments I ( Law G )}{A B:K.time→ℝ}{u:I→ℝ}{k h:ℤ}{ε T:ℝ}
lemma pitch_nn {E:Type}(w: Legs ( Mode ( BH G ) E )):0≤pitch w:=by induction w with| nil=> exact le_rfl| cons i w ih=> rw [pitch,field_cons]; exact add_nonneg (by unfold wfield; omega) ih
lemma slideGrade (hp:Walk K)(_he:0≤k)(hp':Slide K ε (fun i=>( K.price.length i )^k*A i) (fun i=>( K.price.length i )^k*B i))(ht:k≤ h): Slide K ε (fun i=>K.price.length i ^h*A i) (fun i=>K.price.length i^h*B i) := by
    have hB : nn B:= fun i=> nonneg_of_mul_nonneg_right (hp'.target i) (zpow_pos ( K.price.pos i ) _);
    obtain ⟨C,hC,hK⟩:=hp'.moment; refine ⟨ pos_nn _ hB _, C,hC,?_⟩; intro p q hQ hz;
    have hz0(i):K.price.length i >0:= K.price.pos _; let U(p:K.time):= K.price.length p; have hl: U q^(h-k)≤ U p^(h-k):= zpow_le_zpow_left₀ (by omega) (hz0 q).le (hp.length p q hQ hz);
    rw [← sub_add_cancel h k,zpow_add₀ (hz0 p).ne', zpow_add₀ (hz0 q).ne']; rw [mul_assoc]; apply le_trans (mul_le_mul_of_nonneg_left (hK p q hQ hz) (zpow_nonneg (hz0 q).le _)); apply le_trans (mul_le_mul_of_nonneg_right hl ?_); · ring_nf; unfold U; ring_nf; rfl
    have ht:=hp'.target p; have hs:=hB p; have hU:=zpow_pos (hz0 p) k; positivity
-- all root. simplify h variants choose.
lemma breakWalk (h:Walk K)(hv:Slide K ε A B)(he:0<ε): Break (G:=G) b c K A B:= by -- PNN and shift lemma later
    intro E _ _ w hw hm; refine ⟨ ε,he,?_⟩; have h':Slide K ε (fun i=>(K.price.length i)^(0:ℤ)*A i) (fun i=>(K.price.length i)^(0:ℤ)* B i):= (by simpa only [zpow_zero,one_mul] using hv); exact slideGrade h le_rfl h' (pitch_nn w)
def Shore (K:Belt I) : Prop:= ∀ i, K.slot i=Set.Iic 0
lemma stream_at (h:Shore K)(p:K.time): K.stream p= Set.Iic p.2.val:= by
    have hp : p.2.val≤ 0:= (Set.Subset.antisymm_iff.mp (h p.1)).1 p.2.property
    change K.slot p.1 ∩ Set.Iic (tstart p)=Set.Iic (tstart p); rw [h]; exact Set.inter_eq_right.mpr (Set.Iic_subset_Iic.mpr hp)
lemma FarX (h:Break (G:=G) b false K A B)(he:Walk K)(hb:Here b false K F A)(ht: Shore K)(hu:Stroll b F): train b F:= by
   intro i x l hl; let u:= min x 0; let p:K.time:=⟨i,u,by rw [ht i]; exact min_le_right x 0⟩; obtain he:= Dint he h hu hb p l hl (fun z=>Bool.noConfusion z); have h1: IntegrableOn (fun t=> F i t l) (Set.Iic u):= by unfold Belt.Mu at he; rw [ stream_at ht p ] at he; exact he
   refine (integrableOn_union.mpr ⟨ h1,(hu i l hl).continuousOn.integrableOn_compact (isCompact_Icc (a:=u) (b:=x)) ⟩ ).mono_set (fun q hq=>?_); rcases le_total q u with h|h; exact Or.inl h; exact Or.inr ⟨h,hq⟩
lemma follows (h:Shore K) : Dash b K (river F) F 0:= by intro p w hw; unfold river; rw [Belt.Mu, stream_at h p,Pi.zero_apply,Pi.zero_apply,zero_add]
lemma pastH (h:Break (G:=G) b false K A B)(he:Walk K)(hv: nn B)(hx:Shore K)(hF:Warm F b)(hh: Here b false K F A): Here b false K (river F) B ∧ train b F ∧ Warm (river F) b:= by
    obtain hr:= Dance he h hh (Lease.zero hv) hF.walk (follows (b:=b) hx); obtain ht := FarX h he hh hx hF.walk; refine ⟨hr,ht,?_,swampT ht hF.walk⟩; intro i T hT; let J := CK T; let x0:K.time:= ⟨ i,-T,by rw [hx i]; exact neg_nonpos.mpr hT⟩; let g (_:Unit)(v:ℝ):=F i v; let f (_:Unit):= (river F) i; let U:= f () (-T)
    refine Dance (K:=J) (F:=f) (H:=g) ( CKW .. ) (breakWalk (CKW T) ( stripe T hT ) zero_lt_one) ( hF.cost i T hT ) ( Y:=fun _=>U ) ?_ (fun p w hw=> hF.walk i w hw ) ?_
    · intro E _ _ w hV _; convert (constant_at hr x0 J.price (fun _=>le_rfl) w hV (fun z=> Bool.noConfusion z)) using 1; rfl; ext; simp [J,CK,cw] -- maybe more
    intro p v hK; let μ:= ( Mu p ); have hx : Mu p=volume.restrict (Set.Icc (-T) ( tstart p )):= by unfold Belt.Mu; rw [cap0 T]
    rw [hx,integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le]; exact swamp ht i _ (-T) hK; exact p.2.property.1
-- next.BT uniforms. 
end YM.MS.Latch.Job
