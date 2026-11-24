import YM.Contacts.Poetry.Plash
import YM.Contacts.Lintel.Ever
/-! Cover-finite alignment at compact physical support. Auxiliary only. We
 prove without assuming `AsDivisors` a locality-template criterion
 with exact reflection/orientation transport at all periods, without requiring
 Gauge for any of the interpolation probes. -/
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m c C:Side}{w r z:ℕ}
abbrev Story (G:Gauge):= Links ℤ G.El → ℝ
variable (F: Story G)
def pass (n:Side) : Offer G n := fun x U=> F (expandAt x U)
def Adapted (F: Story G):= ∀ (s:Signed)(U),F (pull s 0 U)= F U
lemma reflects (h: Adapted F) : Mirrors (pass F n) := fun x s b U=> by rw [pass,expandAt_pull,h s]; rfl
lemma restrict_launch {K:Type}[Group K] {t:ℕ} {U V:Links ℤ K} (h:Agrees (Lattice.box t) U V)(s:Signed) : Agrees (Lattice.box t) (pull s 0 U) (pull s 0 V):= by
  rintro ⟨x,i⟩ hx hy
  have he (x:Cover)(hx:x∈Lattice.box t): affine s 0 x∈ Lattice.box t:= by rw [affine,add_zero]; exact box_covariant t s ▸ mem_image_of_mem s.act hx
  have hh:= he x hx; have hr:= he (x+step i) hy; rw [show affine s 0 (x+step i)= affine s 0 x+((posDir i).rotate s).vec by rw [Lattice.Step.vec_rotate, Lattice.Step.vec_pos, affine,affine,s.act_add, add_right_comm]] at hr
  unfold pull; cases hb: ((posDir i).rotate s) with| mk a y=>
  rw [hb] at hr; cases y; exact h (affine s 0 x,a) hh hr
  exact congr_arg Inv.inv (h (affine s 0 x-step a,a) (by simpa only [Finset.mem_coe,show (⟨a,true⟩ : Lattice.Step)=negDir a from rfl,Lattice.Step.vec_neg, sub_eq_add_neg] using hr) (by change affine s 0 x-step a+step a ∈ Lattice.box t; rw [sub_add_cancel]; exact hh))
lemma locality (h:LocalOn (Lattice.box r) F) (i:Site c) : LocalOn (neighbors r i) (pass F c i):= by
   intro U V hw; apply h; rintro ⟨x,b⟩ hb hx; exact hw (wrap c x+i,b) ((neighbors_mem ..).mpr (Slide.sep x i hb)) ((neighbors_mem ..).mpr (by rw [show wrap c x+i+step b=wrap c (x+step b)+i by rw [map_add,wrap_step]; abel]; exact Slide.sep _ i hx))
variable {D: Stars→Side}
lemma interviews (h:LocalOn (Lattice.box r) F) (hp:Adapted F) (D:Stars→Side)(B:BudgetPoint)(n:Side) : Trio.CompatibleP B r (pass F n) (fun i=> pass F (D i)):= ⟨fun _i => reflects _ hp, fun _ _ _ _ _ _ _ _ he=> h _ _ he, fun _ _ _ _ _ _ _ he=>h _ _ he,locality _ h⟩
variable (Q:∀ i:Stars,(D i).val=2*(w+i.val))
def shape (A:Slide.Track c) (U:Links ℤ G.El): Config G c:= fun i=> if Slide.grade A i=1 then U (Slide.stage A i.1,i.2) else if Slide.grade A i= -1 then (U (Slide.stage A (i.1+step i.2),i.2))⁻¹ else 1
lemma explodes (A:Slide.Track c)(x:Site n)(U:Config G n) : Slide.shape A x U= Model.shape A (expandAt x U):= rfl
-- local *full* Lattice.box launch
lemma shape_loc (A:Slide.Track c)(u:Finset Cover)(hB:∀ i,Slide.stage A i∈u): LocalOn u (shape (G:=G) A):= by
   intro x y hx; funext ⟨v,w⟩; unfold shape; dsimp only; split
   next h=>
    have ht := hB (v+step w); rw [Slide.tops,h,one_smul] at ht; exact hx (Slide.stage A v,w) (hB v) ht
   split
   next h=>
    have ht:(Slide.stage A (v + step w))+step w=Slide.stage A v:= by rw [Slide.tops,h,neg_one_smul,add_assoc,neg_add_cancel,add_zero]
    exact congr_arg Inv.inv (hx (Slide.stage A (v+step w),w) (hB _) (by erw [ht]; exact hB v))
   rfl

def clock (Y:∀ i:Stars,Config G (D i)→ℝ) : Story G:= fun U=>∑ i:Stars, Slide.ray i*Y i (Model.shape (Trio.pad Q i) U)
lemma local_clock (Y:∀ i:Stars,Config G (D i)→ℝ) (h:w+4≤z): LocalOn (Lattice.box z) (Model.clock Q Y):= by
   intro x v hv; refine sum_congr rfl fun i _=> congr_arg (_ * ·) (congr_arg _ (shape_loc _ _ ?_ _ _ hv)); intro j; apply le_trans (show (Slide.crystal (w+i.val)) ⊆ _ from Slide.crystal_le _) ?_ (Slide.stamp _ j) -- fix
   intro k hk; exact box_test.mpr ⟨fun l=> by have hp:= (box_test.mp hk).1 l; have ht:=i.isLt; omega,fun l=> by have hp:= (box_test.mp hk).2 l; have ht:=i.isLt; omega⟩
variable {Q}
def hue (F:Story G): Story G:= fun U=> (VerifiedReset.factor*∑ s:Signed,F (pull s 0 U))
lemma paints (F:Story G): Adapted (hue F):= by
   intro s U; unfold hue; congr 1; rw [← Equiv.sum_comp (Equiv.mulLeft s) (fun x=>F (pull x 0 U))]; apply sum_congr rfl; intro i _; rw [pull_pull]; simp [affine]
lemma hue_loc (F:Story G)(h:LocalOn (Lattice.box r) F): LocalOn (Lattice.box r) (hue F) := fun _ _ he=>congr_arg (VerifiedReset.factor * ·) (sum_congr rfl fun i _=> h _ _ (restrict_launch he i))

-- near-identity germs without needing passage between Slide appointments.
lemma sideSum (hl:LocalOn (Lattice.box r) F)(ha:Adapted F)(hr:0<r)(hs:w+4≤z)(hw:2*r≤w)(hc:4*r+16≤c.val)(B:BudgetPoint)(V:Config G c)(hv:flags B.threshold V=∅) (Q:∀ i:Stars,(D i).val=2*(w+i.val)) : froth (pass (Model.clock Q (fun i=> froth (pass F (D i)))) c) V= froth (pass F c) V := by
   let F' i:=pass F (D i); let v x:= pass (Model.clock Q (fun i=> froth (pass F (D i)))) c x
   have H X:Healthy B.threshold X V:= by unfold Healthy; simp [hv];
   have ht x: v x= Trio.beacon Q F' x := rfl
   unfold froth; -- may overexpand ;
   erw [show (∑ i:Site c,v i V)=_ from (sum_congr rfl (fun i _=> (masked_eq B.threshold (neighbors z i) (Trio.beacon Q F' i) V (H _)).symm))]; rw [Trio.parade]; apply sum_congr rfl; intro i _
   exact Trio.cruising B Q z F' V i hs hw le_rfl hc (H _) _ (interviews F hl ha D B c) hr -- metavars
lemma from_home (F:Story G)(U: Config G c) : froth (pass (hue F) c) U=VerifiedReset.factor*∑ s: Signed, froth (pass F c) (pull s 0 U) := by
   unfold pass hue froth; rw [← mul_sum,sum_comm]; apply congr_arg; apply sum_congr rfl; intro i _; simp_rw [expandAt_pull]; simp only [affine,add_zero]; exact (Equiv.sum_comp i.actEquiv.toEquiv (fun x=>F (pull i (0:Cover) (expandAt x U)))).symm -- orientation check
end YM.Contacts.Model
