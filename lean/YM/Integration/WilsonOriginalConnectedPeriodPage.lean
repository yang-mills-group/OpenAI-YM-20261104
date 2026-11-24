import YM.Integration.WilsonOriginalConnectedDeckLocality
import YM.Integration.FVA1Physical.TwoReset.Copies

/-! The deck of the original period on a booked auxiliary torus.
A positive angular address distinguishes its translates before grouping the
pair and its third arm. A separate original enumeration is reindexed at each
centre using one chosen lift. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalConnectedPeriodPage
open Lattice Finset Function Further.PhysicalPeriodLimitF933 Macrame Shingle
open FVA1Physical TwoReset
open scoped BigOperators Classical
variable {n N:Side}
abbrev Deck (h:n.val∣N.val) := (splitter h).ker

def recenter (h:n.val∣N.val) (root:Site N) : Deck h≃↑(parcel (splitter h) (splitter h root)) where
  toFun c:=⟨c.val+root,by
    apply (Shingle.posted _ _ _).mpr
    have hc:(splitter h) c.val=0:=c.prop
    rw [map_add,hc,zero_add]⟩
  invFun z:=⟨z.val-root,by
    change splitter h (z.val-root)=0
    rw [map_sub,((Shingle.posted _ _ _).mp z.prop),sub_self]⟩
  left_inv c:=by apply Subtype.ext;exact add_sub_cancel_right .. 
  right_inv z:=by apply Subtype.ext;exact sub_add_cancel ..

theorem pages (h:n.val∣N.val) (root:Site N) {E:Type*} [AddCommMonoid E] (f:Site N→E) :
    (∑i:Fin (Pages n N),f (page h (splitter h root) i).val)=∑c:Deck h,f (c.val+root):=by
  calc
    _ = ∑z:↑(parcel (splitter h) (splitter h root)),f z.val := Equiv.sum_comp (page h (splitter h root)) _
    _ = _ := (Equiv.sum_comp (recenter h root) (fun z=>f z.val)).symm

theorem constant (h:n.val∣N.val) {k:ℂ} (orbit:(∑_:Deck h,k)=0) : k=0 := by
  have non:(Fintype.card (Deck h):ℂ)≠0:=by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0:Deck h)⟩).ne'
  have sum:(Fintype.card (Deck h):ℂ)*k=0:=by simpa only [sum_const,card_univ,nsmul_eq_mul] using orbit
  exact (mul_eq_zero.mp sum).resolve_left non

theorem original (h:n.val∣N.val) {X:Type*} [Fintype X] (root:Site N) (read:X→Site N)
    (roll:Deck h→X≃X) (home:∀x,roll 0 x=x)
    (translate:∀c x,read (roll c x)=c.val+read x)
    (K:X→ℂ) (span:X→ℝ) {diameter ρ M:ℝ}
    (reach:∀x,(separation root (read x):ℝ) ≤ span x+diameter)
    (cable:diameter ≤ (n.val:ℝ)/8) (strip:0 ≤ ρ)
    (orbit:∀x,∑c:Deck h,K (roll c x)=0) (income:(∑x,Real.exp (ρ*span x)*‖K x‖) ≤ M) :
    (∑x,Real.exp (ρ*span x/2)*‖K x‖) ≤ 2*Real.exp (-(ρ*n.val)/8)*M:=by
  refine WilsonOriginalConnectedDeckLocality.original 0 roll home K span (by positivity) cable strip ?_ orbit income
  intro c d x y different equal
  have sites:c.val+read x=d.val+read y:=(translate c x).symm.trans ((congrArg read equal).trans (translate d y))
  have cc:splitter h c.val=0:=c.prop
  have dc:splitter h d.val=0:=d.prop
  have same:splitter h (read x)=splitter h (read y):=by simpa only [map_add,cc,dc,zero_add] using congrArg (splitter h) sites
  have diff:read x≠read y:=by
    intro identical
    exact different (Subtype.ext (add_right_cancel (sites.trans (by rw [identical]))))
  have gap:= (blocks_at_floor h).apart (read x) (read y) same diff
  have tri:=separation_triangle (read x) root (read y)
  rw [separation_comm (read x) root] at tri
  have distance:(n.val:ℝ) ≤ (separation root (read x):ℝ)+(separation root (read y):ℝ):=by
    exact_mod_cast gap.trans tri
  linarith only [distance,reach x,reach y]

end YM.Integration.WilsonOriginalConnectedPeriodPage
