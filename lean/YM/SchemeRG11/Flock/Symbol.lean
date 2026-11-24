import YM.SchemeRG11.Flock.Coven
import YM.Pert.Align.Cancel
/-! Identify lattice top onto a subspace of physical Maxwell labels, enough
 for triangular conversion. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Flock
open Function Lattice Pert.Bare Tensor Maxwell Analysis
variable {G:Gauge}
def leadT (m:ℕ)(f:Bevy G.Color) : TwoJet G.Color m:= fun i j=> printT m (fun s=> (m.factorial:ℝ)⁻¹ • fleet s (bend f i j) 0)
open ContinuousMultilinearMap
lemma conch (m:ℕ)(f:Bevy G.Color)(h:f∈team G.Color (m+2)):leadT m f∈ onShell G.Color m:=by
 have ht (i j:Axis):Tensor.Sym (leadT m f i j):=print_sym _ _
 have ha i j: leadT m f i j=-leadT m f j i:=by
    apply tipped; intro v; unfold leadT; rw [neg_apply,print_tip,print_tip]; simp [bend,← smul_neg]
 refine ⟨⟨ht,ha,fun i j k x=>?cycle⟩,fun j x=>?dive⟩
 case cycle=>
   cases m with
   | zero=>
     have e (A:T E4 G.Color 0)(b:Axis):grad b (diagonal A) x=0:=by
        rw [show diagonal A=fun _=>diagonal A 0 from funext fun _=> congrArg A (Subsingleton.elim ..)]
        simp [grad,Analysis.D]
     simp [e]
   | succ n=>
     let H (i j k:Axis): T E4 G.Color n:=(leadT (n+1) f j k).curryLeft (basis i)
     have e a b c: grad a (diagonal (leadT (n+1) f b c)) x=(n+1) • diagonal (H a b c) x:=differential_diagonal _ (ht b c) x _
     rw [e,e,e,← smul_add,← smul_add]
     have hz: H i j k+H j k i+H k i j=0:=by
        apply tipped; intro v
        simp only [H,leadT,add_apply, front,← smul_add,zero_apply]
        let s:=clutch v
        have W(a b:Axis)(Q:Plane G.Color): soar a (soar b Q)=soar b (soar a Q):= LinearMap.congr_fun (comm a b) Q
        have C : soar i (bend f j k)+soar j (bend f k i)+soar k (bend f i j)=0:=by
           simp only [bend,map_sub]; nth_rw 1 [W i j,W i k,W j k]; abel
        have hh (a b c:Axis):fleet (a ::ₘ s) (bend f b c)=fleet s (soar a (bend f b c)):=by rw [fleet_cons'];rfl
        simp_rw [show clutch v=s from rfl,hh]
        have hx:=congrFun (congrArg (fleet s) C) (0:Cover); simp only [_root_.map_add,Pi.add_apply,_root_.map_zero,Pi.zero_apply] at hx; rw [hx,smul_zero]
     have hx:=DFunLike.congr_fun hz (fun _=>x)
     have hh: diagonal (H i j k) x + diagonal (H j k i) x + diagonal (H k i j) x=0:=hx; rw [hh,smul_zero]
 case dive=>
   cases m with
   | zero=>
     have e (A:T E4 G.Color 0)(b:Axis):grad b (diagonal A) x=0:=by
        rw [show diagonal A=fun _=>diagonal A 0 from funext fun _=> congrArg A (Subsingleton.elim ..)]
        simp [grad,Analysis.D]
     simp [e]
   | succ m=>
     let C (i:Axis): T E4 G.Color m:=(leadT (m+1) f i j).curryLeft (basis i)
     have e i: grad i (diagonal (leadT (m+1) f i j)) x=(m+1) • diagonal (C i) x:=differential_diagonal _ (ht i j) x _
     have hx i: bend f i j∈cap G.Color (m+2) :=Submodule.sub_mem _ (soar_lower _ _ (team_wing h j) i) (soar_lower _ _ (team_wing h i) j)
     have hh:∑i:Axis,C i=0:=by
        apply tipped; intro v; simp only [C,leadT,sum_apply,front,← Finset.smul_sum,zero_apply]
        have E : ∑ i,rear i (bend f i j)=0:=by rw [pitch,show lap (f j)=0 from h.2.2 _,show dive f=0 from h.2.1,_root_.map_zero,sub_self]
        have H:= congrFun (congrArg (fleet (clutch v) : Module.End ℝ (Plane G.Color)) E) (0:Cover); rw [_root_.map_sum, Finset.sum_apply,_root_.map_zero] at H
        simp_rw [← tip m _ (hx _) (clutch v) (cargo v) _ 0 0]
        rw [H]; exact smul_zero _
     simp_rw [e]; rw [←Finset.smul_sum]; unfold diagonal; rw [←sum_apply,hh]; apply smul_zero
lemma solver_grad (m:ℕ)(f:Bevy G.Color)(h:f∈team G.Color (m+2))(he:gaugeJet ⟨leadT m f,conch m f h⟩=0): skim (m+1) f:=by
 have hx : (⟨leadT m f,conch m f h⟩: Shell G m)=0:= Maxwell.leg_injective (he.trans gaugeJet.map_zero.symm)
 intro i j s hs; obtain ⟨r,rfl⟩:=gather s (show s.card=m by omega)
 have hz := DFunLike.congr_fun (congrFun (congrFun (congrArg Subtype.val hx) i) j) (basis ∘ r)
 change printT _ _ _=0 at hz; rw [print_tip] at hz
 exact (smul_eq_zero.mp hz).resolve_left (by positivity)
end YM.SchemeRG11.Flock
