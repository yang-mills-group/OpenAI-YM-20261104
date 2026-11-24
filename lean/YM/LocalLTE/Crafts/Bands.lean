import YM.LocalLTE.Crafts.Release
import YM.LocalLTE.Pool.Dawn
import YM.LocalLTE.Bonnet.Canopy
/-! Curve witness & receipts. -/
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
open Coup Scarf East LocalLTE.Fan Pastel
-- Tag for outputs. Function for any Era. Layer J. `ψ` pre-general as low as needed at all stages.
variable {p:ℕ} (W : Trail H p) (hm:m<N)
-- Career lift. uniform Θ with Horites
variable (k':ℕ) (tag:ℕ→ℕ)
-- permits initial Loft post l_b. Needs W.l<chip.I ad.
local notation "P"=>X.p.profile I
local notation "L"=>D.L J
open Collection.Price LocalLTE.FrameBox Progress.DirectedRecipe Averaging
variable (hp: Cready H W) (M : Preview H) (Jw:Adorn H W)
open Progress.DirectedRecipe Extra.Histories WilsonStartup
-- issue EXACT cinematics, literal. Choose common station.
-- use formula tag N. Expose Payments.F.Path product. Boot sampled too
abbrev spread (a:Levels G) (N p n m:ℕ) :ℕ→ℕ:= if m=N then Frost.trunkTag (a.S.side m n) p else Price.grade (a.S.side m n) p
abbrev Grain (N m n:ℕ)(V:Rep G (A.B.a.S.side m n)) := Coup.License p V H.κ (A.B.a.clock.hatBeta m) (spread A.B.a N p n m) (Trail.extent H W m)
structure Film {N m n:ℕ}{s:Set ℝ}{a:ℝ}{Q: In A.B.a m n}(F:Career H N m n s a Q)(k k':ℕ) (hm:m<N) : Prop where
   sets : F.maps= M.maps N m hm
   motion : F.Accepts H k
   cards : ∀ x∈s, Grain H W N (m+1) n (Q x)
   spring : ∀ x∈s, Trail.Keeps H (F.hearth H x) (Mallow.spread A.B.a N p n (m+1)) p k'
-- book κT
local notation "kT"=> Mallow.spread A.B.a N p n (m+1)
structure Made (V:Bolt A) : Prop where
   seeds N n: let T':=V.history N n N; T'=chorus H (p:=p) T'.beta N n ∧ Grain H W N N n T'
   held N m n (hm:m<N):∃ s a Q,∃ F:Career H N m n s a Q, ∃ k k' x,x∈s ∧ Film H W M F k k' hm ∧ V.history N n (m+1)=Q x∧ V.history N n m=F.Voy H W k' (Mallow.spread A.B.a N p n (m+1)) k x -- order
variable (g:G.Simple)
include M hp Jw g
set_option maxHeartbeats 600000 in
lemma emerging :∃ V:Bolt A, Made H W M V:=by

    let Y := { A.B.bake with
        next:=fun N m n u v=> A.B.Move N m n u v ∧ ∃ s a Q,∃ F:Career H N m n s a Q, ∃ k k' x, ∃ (h:m<N),x∈s ∧ Film H W M F k k' h ∧ v=Q x∧ u=F.Voy H W k' (Mallow.spread A.B.a N p n (m+1)) k x,
        first:=fun N p' v=> A.B.bake.first N p' v∧ v=chorus H (p:=p) v.beta N p',
        retain:=fun N m n u=> A.B.bake.retain N m n u ∧ Grain H W N m n u }
    have he N m p u: Lives Y N m p u ↔ Lives A.B.bake N m p u ∧ Grain H W N m p u := by
       constructor; swap
       · rintro ⟨⟨a,b,c,d,e⟩,hx⟩; exact ⟨a,b,c,d,e,hx⟩
       rintro ⟨a,b,c,d,h⟩; exact ⟨⟨a,b,c,d,h.1⟩,h.2⟩
    have hs N n:Y.Issues N n:=by
       constructor
       · obtain ⟨h,hF⟩:= Mallow.beginning H N n W hp g; exact ⟨_, h,fun x hx=> by
             obtain ⟨hy,hP,h,hZ,hX⟩:= hF x hx
             exact ⟨hy,(he ..).mpr ⟨hP,show Grain H W N N n _ from (by unfold Grain spread; rw [if_pos rfl]; exact hX)⟩, ⟨h.scalars, h.raw,h.inits,rfl⟩⟩ -- edit
          ⟩
       intro m hm l v hv Q hc hx
       have hz x (h:x∈Icc l v): Lives A.B.bake N (m+1) n (Q x) ∧ (Q x).beta ∈ band A.B.a (m+1):= ⟨((he ..).1 (hx _ h).1).1,(hx _ h).2⟩
       obtain ⟨U⟩:= Roof.arches R.pledging.conducts hm hz hc (Set.left_mem_Icc.mpr hv)
       let Lx (i : band A.B.a (m+1)):= Classical.choice (Urns.exhibits H.w (R:=R.shape) hm R.pledging.conducts.full R.pledging.conducts.income.grow.1 i.val i.2)
       let F:Career H N m n (Icc l v) l Q:= ⟨hc,hz,U,Lx,M.maps N m hm,Classical.choice (Tree.select _ (A.B.a.clock.op m n).patch.odd_side)⟩
       obtain ⟨k,hk⟩:= (F.horizon H hm isCompact_Icc).exists
       let f:= Mallow.spread A.B.a N p n (m+1); obtain ⟨k',hX⟩:= (F.curtainX H hm f p isCompact_Icc).exists
       let X':= F.Voy H W k' f k; have ht(x:ℝ)(h:x∈ Icc l v): Grain H W N (m+1) n (Q x):=((he ..).1 (hx _ h).1).2
       have hy:= hp.peers _ _ (step_paid A.B.a m) _ (A.B.valid.pays m)
       let V':= Opera.forum A.B R.shape (m:=m) (n:=n)
       refine ⟨X',F.plot H W hm k' f Jw hk ht hX g hy V',fun x hx=>?_⟩
       obtain ⟨hK,hV,hb,hα⟩:= F.accepted H W hm k' f Jw hk ht g x hx (hX x hx) V'
       have hp: Grain H W N m n (X' x):= by unfold Grain spread; rw [if_neg hm.ne]; exact hα
       exact ⟨(he ..).2 ⟨hK.bundle,hp⟩,hK.ident,(A.B.links hm hK).drift,hK,⟨_,_,_,F,k,k',x,hm,hx,⟨rfl,hk,ht,hX⟩,rfl,rfl⟩⟩
    obtain ⟨V,hT,H⟩:= Y.races g hs (Drifting.pay A.B.valid)
    have hM (N m p:ℕ)(hm:m<N): A.B.Move N m p (V N p m) (V N p (m+1)):= ((hT N p).persists m (Nat.zero_le _) hm).continues.1
    have hz : A.B.bake.Stays V := by intro N n; have hf:= (hT N n).fromTop; exact ⟨fun i hi hj=> ⟨((he ..).1 ((hT N n).prices i hi hj).1).1,((hT N n).prices i hi hj).2⟩,⟨hf.scalars,hf.raw,hf.inits.1⟩,fun i hi hi'=>A.B.links hi' (hM N i n hi')⟩
    refine ⟨⟨R.worksNow g,V,hz,H,hM⟩,fun N n=>⟨(hT N n).fromTop.inits.2,((he ..).1 ((hT N n).prices N (Nat.zero_le _) le_rfl).1).2⟩,fun N m n hm=>?_⟩
    obtain ⟨s,a,Q,F,k,k',x,h',hx,h⟩:= ((hT N n).persists m (Nat.zero_le _) hm).continues.2; exact ⟨s,a,Q,F,k,k',x,hx,h⟩
end YM.PhysicalNext.Repeat.Mallow
