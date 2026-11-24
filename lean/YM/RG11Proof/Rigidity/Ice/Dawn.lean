import YM.RG11Proof.Rigidity.Ice.Aurora

/-!
# Normalize and withdraw the deficit sequence
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Fields Labels Maxwell Function Extra.FD Reads Maxwell.Free Set Filter Pert.Position Gauge
open scoped Classical BigOperators Topology ContDiff InnerProductSpace
variable {G:Gauge}{F:Frames G}{d:ℕ}
local notation "V"=>G.Color
local notation "Y"=>V→L[ℝ] V

local notation "†"=> (ContinuousLinearMap.adjoint (E:=V) (F:=V) (𝕜:=ℝ))
lemma adjR (W:Wheel G): † (steers W)=steers W.symm:=(ContinuousLinearMap.eq_adjoint_iff ..).mpr W.symm.inner_map_eq_flip|>.symm

lemma steeper {b:Buffer F d}{u:ℕ→ℝ}{U:ℕ→Y}(h : ∀ i, Winner b (u i) (U i))(ht:Tendsto U atTop (𝓝 1))
    {r:ℕ→ℝ}{D:Y}(hD:Tendsto (fun i=>r i • (U i-1)) atTop (𝓝 D)) : † D = - D:=by
  -- differentiate UU^t by a single telescoping difference
  have he (i): † (U i)*U i=1:=by obtain ⟨W,hW⟩:=(h i).1.folds; rw [hW,adjR]; exact ContinuousLinearMap.ext fun x=>W.symm_apply_apply x
  have hs: († D)*1+1*D=0:=by
    have hT := (†).continuous.continuousAt.tendsto.comp hD
    have hL := (hT.mul ht).add ((tendsto_const_nhds (x:=(1:Y))).mul hD)
    refine tendsto_nhds_unique hL ?_
    convert_to Tendsto (fun _ : ℕ => (0:Y)) atTop (𝓝 0); swap; exact tendsto_const_nhds
    ext1 i; simp only [Function.comp_apply]
    rw [map_smulₛₗ,map_sub, ContinuousLinearMap.adjoint_one]
    change (r i • († _-1))*U i+1*(r i • (U i-1))= _
    rw [one_mul, smul_mul_assoc,← smul_add,sub_mul,he,one_mul,sub_add_sub_cancel,sub_self,smul_zero]
  rw [one_mul,mul_one] at hs; exact eq_neg_of_add_eq_zero_left hs

private lemma distribute_y (t : ℝ)(A B:Y) : (t • A)*B=t • (A*B):= ContinuousLinearMap.ext fun _=>rfl
private lemma distribute_Y (t : ℝ)(A B:Y) : B*(t • A)=t • (B*A):= ContinuousLinearMap.ext fun a=> B.map_smul t (A a)
lemma rises {b:Buffer F d}{u:ℕ→ℝ}{U:ℕ→Y}(hd:6≤d)(hG:G.Simple)(h : ∀ i, Winner b (u i) (U i))(ht:Tendsto U atTop (𝓝 1))
    {r:ℕ→ℝ}{D:Y}(hD:Tendsto (fun i=>r i • (U i-1)) atTop (𝓝 D)) : D=0:=by
  have hS:= steeper h ht hD
  have hu : Celestial D.toLinearMap:=by
    intro i j
    change inner ℝ (D i) j = -inner ℝ i (D j)
    rw [← ContinuousLinearMap.adjoint_inner_right D i j,hS]
    exact inner_neg_right ..
  have hp (v:V): ∃ t:V,D.toLinearMap*G.ad v-G.ad v* D.toLinearMap=G.ad t:=by
    let W := LinearMap.range (LinearMap.toContinuousLinearMap.toLinearMap.comp G.ad)
    let S:=spinY v
    have he (i): † (U i)* S * U i∈ W:=by
      obtain ⟨Q,hQ⟩:= (h i).1.folds
      rw [hQ,adjR]
      obtain ⟨w,hw⟩:= Feasible.carriage hd hG (hQ ▸ (h i).1) v
      refine ⟨w,?_⟩; exact ContinuousLinearMap.ext fun a=> congrArg (fun f:Y=>f a) hw.symm
    have hx : † D * S * 1 + S * D∈ W:= by
      have hT := (†).continuous.continuousAt.tendsto.comp hD
      refine W.closed_of_finiteDimensional.mem_of_tendsto (((hT.mul_const S).mul ht).add ((tendsto_const_nhds (x:=S)).mul hD))
        (Eventually.of_forall (fun i=>?_))
      change († (r i • (U i-1))* S* _ + S * (r i • (U i-1)))∈ W
      rw [map_smulₛₗ,map_sub,ContinuousLinearMap.adjoint_one,distribute_y,distribute_y,distribute_Y]
      change r i • _ + r i • _ ∈W
      rw [← smul_add,sub_mul,sub_mul,one_mul,mul_sub,mul_one,sub_add_sub_cancel]
      exact W.smul_mem _ (W.sub_mem (he i) (LinearMap.mem_range_self _ v))
    obtain ⟨t,ht'⟩:=hx
    refine ⟨-t,LinearMap.ext (fun a=>?_)⟩
    have hr := congrArg (fun f:Y=>f a) ht'
    rw [hS,mul_one,neg_mul, _root_.add_apply,_root_.neg_apply] at hr
    rw [map_neg,LinearMap.neg_apply]; change _-_= -G.ad t a; change G.ad t a= -_ + _ at hr; rw [hr]; change D _-G.ad v (D a)= -(-D (G.ad v a) + G.ad v (D a)); abel
  exact ContinuousLinearMap.ext fun a=> LinearMap.congr_fun (off_kills_dawn hu (flare h ht hD) hG hp) a
end YM.RG11.Rigidity.Ice
