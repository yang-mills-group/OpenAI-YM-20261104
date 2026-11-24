import YM.Contacts.Pulse.Spine
import YM.Extra.ITERATION_NO_LOSS.Columns
namespace YM.Pulse.Spine
open Function Set Finset Filter Lattice RG Wilson Precision Stationary Exterior
open Bloch Laurent Push.AbsoluteSums Extra.Iteration
open scoped Classical Topology BigOperators NNReal
noncomputable section
variable {α β X Y Z : Type}{L c f: Side}{σ η:ℝ≥0}{u v:Cover}{k:Axis}
def portal (L:Side) (x a:Cover) : Prop := a=rent L x
def install (R:Cross L α β) (x:Node α)(y:Node β) := R (wrap L x.1,x.2) y.2 (y.1-rent L x.1)
def access (L:Side)(σ:ℝ≥0)(x:Node α)(y:Node β):ℝ:= Real.exp (σ * (size (y.1-rent L x.1)+2:ℝ))
lemma ramp (L:Side)(x v:Cover): rent L (x+v)=rent L x + YM.Work.F08.carry (wrap L x) v := by
  symm; apply rent_unique; have h:= YM.Work.F08.carry_spec (wrap L x) v
  rw [map_add, smul_add]
  conv_lhs => lhs; rw [rent_balance L x]
  simp only [YM.Work.F08.arrives,map_add,wrap_lift] at h; rw [add_right_comm, h]; abel
lemma stride (L:Side)(x y:Cover) : (size (rent L x - rent L y):ℝ) ≤ (size (x-y):ℝ) / (L.val:ℝ) + 4 := by
  apply le_trans ?_ (Extra.Iteration.carry_bound (wrap L y) (x-y)); rw [← show rent L x-rent L y=YM.Work.F08.carry (wrap L y) (x-y) from ?_]
  have he := ramp L y (x-y); rw [show y+(x-y)=x from by abel] at he; rw [he]; abel
lemma influx (h: (σ:ℝ)/(L.val:ℝ) ≤ η): Ripple (terrain η α) (terrain σ β) (access L σ) := by
  refine ⟨fun x y=> Real.one_le_exp (by positivity),fun x y u v=> ?_⟩
  simp only [access,terrain_step,← Real.exp_add]; apply Real.exp_monotone
  have he : size (v.1-u.1) ≤ size (u.1-rent L x.1)+ size (rent L y.1-rent L x.1) + size (v.1-rent L y.1) := by
    calc
      _ = Laurent.size ((-(u.1-rent L x.1)+(rent L y.1-rent L x.1))+(v.1-rent L y.1)) := by rw [show (-(u.1-rent L x.1)+(rent L y.1-rent L x.1))+(v.1-rent L y.1)=v.1-u.1 by abel]
      _ ≤ _:= (size_add ..).trans (by gcongr; exact (size_add ..).trans_eq (by rw [size_neg]))
  have H : (σ:ℝ)*(size (rent L y.1-rent L x.1):ℝ) ≤ η*(size (y.1-x.1):ℝ)+4*σ := by
    apply (mul_le_mul_of_nonneg_left (stride L y.1 x.1) (by positivity : 0≤(σ:ℝ))).trans; rw [mul_add,← mul_div_assoc,mul_comm _ 4,mul_div_right_comm]; gcongr
  replace he := mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr he) (show 0≤(σ:ℝ) by positivity); push_cast at he; linarith
lemma scraps (L:Side)(x:Cover)(i:Axis)(hl:Odd L.val) : rent L (x+Lattice.step i)=rent L x + (if lift (wrap L x) i=↑(L.val/2:ℕ) then Lattice.step i else 0) := by
  rw [ramp, ← earn_delta L hl]; congr 1
lemma install_forward (R:Cross L α β)(h:Odd L.val)(i:Axis)(x:Cover)(a:α)(y: Node β):
    install (forwardC L R i) (x,a) y=install R (x+Lattice.step i,a) y-install R (x,a) y:= by
  simp only [install,forwardC,scraps L x i h,map_add,wrap_step]; rw [sub_add_eq_sub_sub]

variable [Fintype α] [Fintype β]{R:Cross L α β}{C:ℝ}
abbrev beamPrice (σ:ℝ≥0) (C:ℝ) := Real.exp (σ*2)*C
lemma ledgers (h:Row.strip R σ C) (he:0≤C): Weirs (access L σ) (install R) (Fintype.card (Co L α)*beamPrice σ C) (Fintype.card β*beamPrice σ C):= by
  let c:= beamPrice σ C; have hc : 0≤ c := by unfold c beamPrice; positivity
  refine ⟨mul_nonneg (Nat.cast_nonneg _) hc,mul_nonneg (Nat.cast_nonneg _) hc,fun y=>?_,fun x=>?_⟩
  · let g (x:Node α): Co L α×Cover:= ((wrap L x.1,x.2),y.1-rent L x.1)
    have hg : Injective g:= by
      rintro ⟨p,a⟩ ⟨q,b⟩ hu; simp only [g,Prod.mk.injEq,sub_right_inj] at hu
      suffices h:p=q by rw [h,hu.1.2]
      rw [rent_balance L p,hu.1.1,hu.2]; exact (rent_balance L q).symm
    let w (p:Co L α×Cover) := Real.exp ((σ:ℝ)*2)*(Real.exp (σ* (size p.2:ℝ))* ‖R p.1 y.2 p.2‖)
    refine budget_map (f:=fun x=>_) (show SumBudget w _ from Cost.product (Cost.finite c hc) (fun z => budget_scale (x:=Real.exp ((σ:ℝ)*2)) (by positivity) (h z y.2))) _ hg ?_
    intro i; unfold g w install access; rw [mul_add,Real.exp_add]; ring
  let g (y:Node β): β × Cover:= (y.2,y.1-rent L x.1)
  refine budget_map (f:=fun y=>_) (show SumBudget (fun p:β×Cover=> Real.exp ((σ:ℝ)*2)*(Real.exp (σ* (size p.2:ℝ))* ‖R (wrap L x.1,x.2) p.1 p.2‖)) _ from Cost.product (Cost.finite c hc) (fun z=> budget_scale (x:=Real.exp ((σ:ℝ)*2)) (by positivity) (h (wrap L x.1,x.2) z))) _ (show Injective g from fun p q h=> by simp [g] at h; exact Prod.ext h.2 h.1) fun i=> ?_
  simp only [g,install,access,mul_add,Real.exp_add]; ring

-- block side already absorbed in card_site
lemma flow_price (h:Row.strip R σ C) (he:0≤C): Weirs (access L σ) (install R) ((L.val:ℝ)^4*Fintype.card α*beamPrice σ C) (Fintype.card β*beamPrice σ C):= by
  convert ledgers h he using 1; simp [Bloch.Co,Lattice.Site,Fintype.card_pi,Lattice.Per]
end
end YM.Pulse.Spine
