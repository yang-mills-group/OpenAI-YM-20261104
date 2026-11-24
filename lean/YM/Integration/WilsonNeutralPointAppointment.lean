import YM.Integration.WilsonNeutralPointSalary
import YM.Integration.WilsonWindowFormalPurchase

/-! The extra digit-wise purchase is made before choosing the physical block
length and cutoff. Its true post-block allowance covers every lodge and digit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPointAppointment
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Quire Palm Grail Chapel Borough Series Work.F03 Work.F05 Work.F08
open WilsonNeutralPointSalary Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical

structure Request (G:Gauge)(j:ℕ) where
  field : Fin (j+1)
  test : Fin (j+1)
  grade : Fin (j+1)
  rank : Fin (j+1)
  slots : Fin (j+1)
  stage : Fin (j+1)
  root : Loc G 1

instance (G:Gauge)(j:ℕ):Finite (Request G j):=Finite.of_injective
  (fun c:Request G j=>(c.field,c.test,c.grade,c.rank,c.slots,c.stage,c.root)) (by
    rintro ⟨d,D,e,r,l,t,o⟩ ⟨d',D',e',r',l',t',o'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩:=h
    rfl)

variable {G:Gauge}(K:KernelChoices)(F:∀ d,Frame G d)(H:Hol G)(W:Borough.Window G K)
variable {j:ℕ}(c:Request G j)

def ready:Prop:=c.field.val<c.test.val ∧ 4≤j ∧ c.field.val+1≤j-2 ∧
  4≤c.stage.val ∧ 0<W.width j ∧ 0<W.width c.stage.val ∧ W.width c.stage.val≤coverPrice G K j c.stage.val

/-- The finite stage need on the actual previously selected post-block lodge. -/
def fits (P:Patch)(S:Lodge P)(b:ℝ):Prop:=
  ∀ Z:Flight j c.stage.val,∀ U:Lodge Z.patch,∀ hz:Z.patch=P,hz ▸ U=S →
  ∀ T:Anthem c.test.val G,Clef c.root T c.slots.val → ∀ B:ℝ,
  Deposit c.root (W.width j) T c.grade.val B →
  (∀ i,‖coeff c.grade.val (echo (F c.field.val) T i)‖≤B) →
  ∀ A:ℝ,0≤A → (∀ p,Knoxville (fame _) (W.width j) (0,c.root) (T p c.grade.val c.rank.val) (A*‖p‖)) →
  ∀ x:Site Z.L,∀ hL:2≤Z.L.val,
  (∀ i:Letter (F c.field.val),Pose.slots (F c.field.val) i=c.rank.val →
    ‖pearlJ (F c.field.val) (land Z K U T c.field.val c.grade.val c.rank.val x hL
      (inside (F c.field.val) i c.test.val)) (mint (F c.field.val) i)‖≤b*B) ∧
  (∀ p:Studio c.test.val, Knoxville (fame _) (W.width c.stage.val) (0,c.root)
    (land Z K U T c.field.val c.grade.val c.rank.val x hL p) ((Dove.Mulct Z.L*A+b*B)*‖p‖))

include H in
theorem purchase (h:ready K W c):∃ X:ℝ,0≤X ∧ ∀ P:Patch,X≤(P.L.val:ℝ)→
    ∀ S:Lodge P,∃ b:ℝ,0≤b∧fits K F W c P S b:=by
  obtain ⟨depth,hj,room,ht,hw,he,allowed⟩:=h
  rw [coverPrice,dif_pos ⟨hj,ht⟩] at allowed
  obtain ⟨C,hC,hfee,quote,-⟩:=(may_use G K j c.stage.val hj ht).choose_spec
  obtain ⟨X,nonneg,buy⟩:=WilsonNeutralPointSalary.purchase c.root (F c.field.val) H
    c.rank.val c.slots.val c.grade.val c.test.val depth hj room ht hw he hfee.le K
  refine ⟨X,nonneg,fun P hX S=>?_⟩
  obtain ⟨b,hb,pay⟩:=buy P hX S
  refine ⟨b,hb,fun Z U eq cast=>pay Z U eq cast ?_⟩
  intro l hl
  exact ⟨strip_mono (quote Z l hl).1 allowed le_rfl,strip_mono (quote Z l hl).2 allowed le_rfl⟩

def before:ℝ:=if h:ready K W c then (purchase K F H W c h).choose else 0

theorem offered (h:ready K W c)(P:Patch)(gate:before K F H W c≤(P.L.val:ℝ))(S:Lodge P):
    ∃ b:ℝ,0≤b∧fits K F W c P S b:=by
  rw [before,dif_pos h] at gate
  exact (purchase K F H W c h).choose_spec.2 P gate S

def after (P:Patch)(S:Lodge P):ℝ:=if h:ready K W c ∧ before K F H W c ≤ (P.L.val:ℝ)
  then (offered K F H W c h.1 P h.2 S).choose else 0

theorem paid (h:ready K W c)(P:Patch)(gate:before K F H W c≤(P.L.val:ℝ))(S:Lodge P):
    fits K F W c P S (after K F H W c P S):=by
  rw [after,dif_pos ⟨h,gate⟩]
  exact (offered K F H W c h P gate S).choose_spec.2

def floor (j:ℕ):ℕ:=Nat.ceil (bddBill (fun c:Request G j=>before K F H W c)).choose
theorem floor_pays:before K F H W c ≤ (floor K F H W j:ℝ):=by
  exact (le_abs_self _).trans (((bddBill (fun c:Request G j=>before K F H W c)).choose_spec.2 c).trans (Nat.le_ceil _))

/-- One invoice for the planted digit at every true root and lodge, at this stage. -/
theorem buy_after (L:Side)(j:ℕ):∃ B:ℝ,0≤B ∧ ∀ c:Request G j,∀ P:Patch,∀ S:Lodge P,
    P.L=L → P.J=j → |after K F H W c P S|≤B:=by
  let Pat:={P:Patch // P.L=L ∧ P.J=j}
  let _ : Finite Pat:=Borough.patch_owned
  let _ (P:Patch):Finite (Lodge P):=Borough.lodge_owned P
  let _ : Finite ((p:Pat) × Lodge p.val):=inferInstance
  obtain ⟨B,hb,pay⟩:=bddBill (fun z:(Request G j) × ((p:Pat) × Lodge p.val)=>
    after K F H W z.1 z.2.1.val z.2.2)
  exact ⟨B,hb,fun c P S hL hJ=>pay (c,⟨⟨P,hL,hJ⟩,S⟩)⟩

end YM.Integration.WilsonNeutralPointAppointment
end
