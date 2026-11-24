import YM.LocalLTE.Bonnet.Quiet
/-! Common level atlas.Declared Ready for later mark Ports as geometry. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost
open UVNext.CouplingReset Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open YM.LocalLTE.Inset ClockB Urns Trio Slide Marlin
-- NOTE scope. factor uses `T` Launch.
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A: Alloy X D} (R: Roost.Factor A){p0:ℕ} -- use eta
variable {R} {ε : ℝ} (H:Funding R p0 ε)
local notation "Wf"=> H.w
variable {N m n k:ℕ} {s:Set ℝ} {a:ℝ} {Q:In A.B.a m n}(F:Career H N m n s a Q)
local notation "T" => A.B.a
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "C₀" => R.target
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "s₀"=> ClockB.lanternPay G (D.L J) (X.p.profile I) H.w.q x₀
local notation "z" => Trio.base (Trio.resize H.w.ℓ (Rain.lint R.target A m)) (radiusB x₀)
local notation "A₀" => A.B.a.S.side m n
local notation "O" => Chi.canonical
local notation "γ" => A.B.kin.alpha N m
open Progress.DirectedRecipe Extra.Histories Graces
/- signatures intended later.Before V. -/
structure Preview where
  maps (N m :ℕ):m<N→ Urns.Maps (A:=A) (C:=R.target) H.w m N
lemma previews : Nonempty (Preview H):= by
  let b:=R.pledging.conducts.income.grow.1; let c:=R.pledging.conducts.full
  exact ⟨⟨fun N m h=> Classical.choice (known H.w (R:=R.shape) h c b)⟩⟩
-- marks support proofs will be transported w Nest contract (via Season replacement). old Nest legacy not asserted!
variable (M:Preview H)
def Formed (N m n:ℕ) (u:Rep G (A.B.a.S.side m n))(v:Rep G (A.B.a.S.side (m+1) n)):= ∃ s a Q, ∃ F:Career H N m n s a Q,
    ∃ (h:m<N),F.maps=M.maps N m h ∧ ∃ k, F.Accepts H k∧∃ x,x∈s∧v=Q x∧u=F.result H k x
variable (g:G.Simple)
structure Canopy (V:Bolt A): Prop where
   born N p : HasSlots (V.history N p N).p (V.history N p N).activities
   held N m p : m<N→ Formed H M N m p (V.history N p m) (V.history N p (m+1))∧Accurate A.B R.post N m p (V.history N p m) (V.history N p (m+1))
include g
lemma onwards :∃ V:Bolt A,Canopy H M V:=by
  let Y:= { A.B.bake with next:= fun N m p u v=> A.B.Move N m p u v∧Formed H M N m p u v∧Accurate A.B R.post N m p u v,
                          first:=fun N p v=> A.B.bake.first N p v∧HasSlots v.p v.activities}
  have he N m p u:Lives Y N m p u↔ Lives A.B.bake N m p u:= by constructor <;> rintro ⟨a,b,c,d,e⟩ <;> exact ⟨a,b,c,d,e⟩
  have hp N p:Y.Issues N p:=by
    constructor
    · obtain ⟨F,h,hF⟩:= Graces.hops R N p
      exact ⟨F,h,fun x hx=>by obtain ⟨hv,hB,ht,hZ⟩:= hF _ hx; exact ⟨hv,(he ..).2 hB,ht.scalars,ht.raw,ht.inits,hZ⟩⟩
    intro m hm l v hv Q hc hh
    have hz: ∀ x∈Icc l v,Lives A.B.bake N (m+1) p (Q x)∧(Q x).beta∈band A.B.a (m+1):=fun i hi=> ⟨(he ..).1 (hh i hi).1,(hh i hi).2⟩
    obtain ⟨J'⟩:= Roof.arches R.pledging.conducts hm hz hc (Set.left_mem_Icc.mpr hv)
    let L (i : band A.B.a (m+1)):= Classical.choice (Urns.exhibits H.w (R:=R.shape) hm R.pledging.conducts.full R.pledging.conducts.income.grow.1 i.val i.2)
    let F:Career H N m p (Icc l v) l Q:= ⟨hc,hz,J',L,(M.maps N m hm),Classical.choice (Tree.select _ (A.B.a.clock.op m p).patch.odd_side)⟩
    obtain ⟨k,ht⟩:= (F.horizon H hm isCompact_Icc).exists
    obtain ⟨hk,hK⟩:= F.direction H hm ht g
    refine ⟨F.result H k,hk,fun x hx=>?_⟩; obtain ⟨hy,hp,-⟩:=hK x hx; exact ⟨(he ..).2 hy.bundle,hy.ident,(A.B.links hm hy).drift,hy,⟨_,_,_,F,hm,rfl,k,ht,x,hx,rfl,rfl⟩,hp⟩
  obtain ⟨X',hT,hU⟩:=Y.races g hp (Drifting.pay A.B.valid)
  have hM(N m p:ℕ)(hm:m<N):A.B.Move N m p (X' N p m) (X' N p (m+1)):= ((hT N p).persists m (Nat.zero_le _) hm).continues.1
  have hh:A.B.bake.Stays X':= by intro N p; have hf:= (hT N p).fromTop; exact ⟨fun i hi hj=> ⟨(he ..).1 ((hT N p).prices i hi hj).1,((hT N p).prices i hi hj).2⟩,⟨hf.scalars,hf.raw,hf.inits.1⟩,fun i hi hi'=> A.B.links hi' (hM _ _ _ hi')⟩
  refine ⟨⟨R.worksNow g,X',hh,hU,hM⟩,fun N p=>?_,fun N m p hm=> ((hT N p).persists m (Nat.zero_le _) hm).continues.2⟩
  exact (hT N p).fromTop.inits.2
end YM.PhysicalNext.Repeat.Mallow
