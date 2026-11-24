import YM.Integration.WilsonOriginalJointDeckMotion

/-! A nonzero angular slot pins the full ordered mixed tuple. Pure thermal slots have an exact zero signed difference. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalJointDeckLocality
open Function Finset Lattice RG Stationary
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalConnectedPeriodPage WilsonEmittedRootedJetWage WilsonOriginalJointDeckMotion
open scoped BigOperators Classical ContDiff
variable {G:Gauge}{n N:Side}{r:ℕ}
abbrev Mix (G:Gauge) (N:Side) (r:ℕ):=Fin r→Slot G N

def indices (u:Mix G N r):Finset (Fin r):=univ.filter fun i=>(u i).isSome
abbrev Seated (G:Gauge) (N:Side) (r:ℕ):={u:Mix G N r // (indices u).Nonempty}

theorem indices_turn (a:Site N) (u:Mix G N r):indices (turn a u)=indices u:=by
  ext i
  simp only [indices,mem_filter,mem_univ,true_and]
  change (color a (u i)).isSome=true ↔ (u i).isSome=true
  cases u i <;> rfl

def move (a:Site N): Seated G N r≃Seated G N r where
  toFun u:=⟨turn a u.val,by rw [indices_turn];exact u.prop⟩
  invFun u:=⟨turn (-a) u.val,by rw [indices_turn];exact u.prop⟩
  left_inv u:=Subtype.ext ((turn a).left_inv u.val)
  right_inv u:=Subtype.ext ((turn a).right_inv u.val)

def first (u:Seated G N r):Fin r:=(indices u.val).min' u.prop

def site:Slot G N→Site N
  | none => 0
  | some x => x.1

def positioned (u:Seated G N r):Site N:=site (u.val (first u))

theorem pinned (a:Site N) (u:Seated G N r):positioned (move a u)=a+positioned u:=by
  have chosen:first (move a u)=first u:=by
    change (indices (turn a u.val)).min' _=(indices u.val).min' _
    congr 1
    exact indices_turn a u.val
  unfold positioned
  rw [chosen]
  let i:=first u
  have occupied:(u.val i).isSome=true:=(mem_filter.mp ((indices u.val).min'_mem u.prop)).2
  change site (color a (u.val i))=a+site (u.val i)
  cases z:u.val i with
  | none => simp [z] at occupied
  | some q => rfl

theorem fixed (a:Site N) (u:Mix G N r) (empty:¬(indices u).Nonempty):turn a u=u:=by
  funext i
  change color a (u i)=u i
  cases z:u i with
  | none => rfl
  | some q =>
    exfalso
    exact empty ⟨i,mem_filter.mpr ⟨mem_univ _,by simp [z]⟩⟩

theorem original (h:n.val∣N.val) (root:Site N) (K:Mix G N r→ℂ) (span:Mix G N r→ℝ) {D ρ M:ℝ}
    (reach:∀x:Seated G N r,(separation root (positioned x):ℝ) ≤ span x.val+D)
    (cable:D≤(n.val:ℝ)/8)(strip:0≤ρ)
    (orbit:∀u:Mix G N r,∑c:Deck h,K (turn c.val u)=0)
    (income:(∑u,Real.exp (ρ*span u)*‖K u‖)≤M):
    (∀u:Mix G N r,¬(indices u).Nonempty→K u=0) ∧
    (∑u,Real.exp (ρ*span u/2)*‖K u‖)≤2*Real.exp (-(ρ*n.val)/8)*M:=by
  have thermal (u:Mix G N r) (flat:¬(indices u).Nonempty):K u=0:=by
    apply WilsonOriginalConnectedPeriodPage.constant h
    simpa only [fixed _ u flat] using orbit u
  refine ⟨thermal,?_⟩
  have tot (b:ℝ): (∑u:Mix G N r,Real.exp (b*span u)*‖K u‖)=
      ∑x:Seated G N r,Real.exp (b*span x.val)*‖K x.val‖:=by
    rw [←Fintype.sum_subtype_add_sum_subtype (fun u:Mix G N r=>(indices u).Nonempty)]
    have gone:(∑x:{u:Mix G N r // ¬(indices u).Nonempty},Real.exp (b*span x.val)*‖K x.val‖)=0:=by
      apply sum_eq_zero
      intro x _
      simp [thermal x.val x.prop]
    rw [gone,add_zero]
  have numerical:=(WilsonOriginalConnectedPeriodPage.original h root positioned (fun c:Deck h=>move c.val)
    (fun x=>Subtype.ext (home x.val)) (fun c x=>pinned c.val x) (fun x=>K x.val) (fun x=>span x.val)
    reach cable strip (fun x=>orbit x.val) ((tot ρ).symm.trans_le income))
  have half:=tot (ρ/2)
  simp only [div_mul_eq_mul_div] at half
  exact half.trans_le numerical

end YM.Integration.WilsonOriginalJointDeckLocality
