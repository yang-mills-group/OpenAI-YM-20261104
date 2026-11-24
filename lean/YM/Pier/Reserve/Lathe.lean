import YM.Pier.Reserve.Local
/-!
# The canonical cast retains both kinds of reserve, stronger on forced input

Use the producer from `Panel` at the strength *before* it weakens (same representatives).
Both the unrotated price on each ticket and anticipated turn prices in Lathe are needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Circlet
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury Graces
open Planned.PrimaryIntegral295 WaterLevels
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{M : Metals G}{D:Rolls M.p}{A:Alloy M D}{Q:ℕ→ℕ→ Teller G}{C: Programs M.p}
   {r p:ℕ→ℕ} {R:ℕ→ℕ→Record}{B:Factor A}{V:Bolt A}
local notation "cc"=> A.B.a
variable {m N n d:ℕ} (hm:m<N)
local notation "J"=> A.B.a.clock.J (m+1)
local notation "T"=> A.B.a.clock.J m
local notation "B₁"=> A.B.a.budget m
local notation "B₂"=> A.B.a.budget (m+1)
local notation "X"=> A.B.a.clock.op m n
local notation "V0"=> ships A.B N m n
local notation "V1"=> forecast V m N n
local notation "L"=> D.L J
local notation "y"=> A.B.a.clock.hatBeta m
local notation "v"=> R J T
local notation "u"=> C J T
local notation "vT"=> M.p.profile J
local notation "vB"=> M.p.profile T
local notation "r'"=> B.span J T
set_option quotPrecheck false
variable (hP:Circlet.Pitch M.p M.K Q C r) (hp: Pads D R Q M.K C A.delay) (hc: Decked C D R B.span B.shape A.delay) (hb:goodD M.p (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) d)(hV:Nest B V) (hC:Mallow.Arrives B.shape A.delay)
local notation "F"=> (Labels.frames G).level d
local notation "n₀"=> A.B.a.S.side m n
local notation "n₁"=> A.B.a.S.side (m+1) n
variable {K:In A.B.a m n} {meshT:ℕ→∀ p, Trail A.B.a p} {x t:ℝ} (H: Spring B N m n x t K)(z: Icc x t)
local notation "Z"=> houseS H z
set_option quotPrecheck false
open PPX MergeProof Next.Free Bid
variable (he : (A.B.bake.make meshT).rep N n m=H.result z.val) (ht: (A.B.bake.make meshT).rep N n (m+1)=K z.val) (g:G.Simple)
   (hC': Graces.Moms B.prices M.K B.span M.p.floorL)(hw: Graces.Cruise B.prices D B.recordP B.span B.shape A.delay) (hT: Cub.MainTest B.target B.expense B.span D B.shape C R A.delay)
   {E:ℕ→ℝ}(h' : Chop M.p E B.span) {W:Bid.Worth}(hY:Doors.Budget A.B.a E W) (hκ:Comply B.shape A.delay)
local notation "H!"=> A.B.bake.make meshT
local notation "DO"=> duet (A.B.bake.make meshT) N n m he ht (sandboxK H z)
local notation "Rt"=> K z
local notation "ε0"=> Cub.title G vT
local notation "Πt"=> localSection G d
open MergeProof.Matric
variable (choice : (A.B.bake.make meshT).Selected)(hs: HasSlots ((A.B.bake.make meshT).rep N n m).p ((A.B.bake.make meshT).rep N n m).activities)(hr : HasSlots (K z).p (K z).activities)
local notation "sk"=> Guard.Keeper.sufficient hs

variable (hsBlend: Push.Local.Readable (hol G) (localSection G d) (K z).p (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (A.B.a.clock.J (m+1)))))
local notation "tap"=> Cub.shade H z hs hr hsBlend
local notation "ζ0"=> (2*(Real.exp ((H!).rep N n (m+1)).p.supportExponent*ε0))
include g choice hs hr hP hp hc hb hV hC hC' hw hT he ht h' hY hκ hm

set_option maxHeartbeats 650000 in
theorem reserveLathe (hd: d+3≤ T):
    Pier.Lathe (H!) N n m (hol G) Πt (K z) tap DO (E J) (Doors.rate ((H!).S.block m)) := by
  let Tx:= A.B.a
  let i:= Tx.clock.J m
  have hq: d ≤ i:= (Nat.le_add_right d 3).trans hd
  have hh: (H!).S.block m=L:=PriceCompiler.block_eq A.B.valid m
  constructor
  case main =>
    intro k xk
    rw [hh]
    change Pier.Room (tell (Cub.border H z hs hr hsBlend k)) _ _ _ _ _
    unfold Cub.border
    split
    next hi' =>
      subst k
      have hj : (F).core xk = 0 := by
        simp only [xk, Size.core_axis, if_true]
      have hfmt : (Extra.Histories.primary (0:Site n₀) (((L).val:ℂ)^d • (F).e0)).Format 0 (hol G) ((H!).rep N n m):=primary_format ..
      apply Pier.Room.close _ hfmt _
      apply Pier.Room.base
      · simp [hj,Frame.coeffSize,vowel]
      exact Real.sqrt_pos.mpr (forcedPos ..)
    next hi' =>
      have hstage := step_paid A.B.a m
      have hj:d ≤ J:= hq.trans hstage.1
      have hz:Heir.Release.accepts (B.span J T) (M.p.profile J).supportExponent ((M.p.profile T).supportExponent+2) L:= hC' _ _ d hb _ (D.large _).need|>.1
      obtain ⟨T'⟩:= hT _ _ (A.B.valid.pays m) _ d (first_le A.B.valid m) hstage hd
      have hB : Blend 2 (B₂).threshold (B₁).threshold := T'.scaleP _ _ rfl (Circlet.shifting (A:=A) (m:=m)).1
      have hf := primaryJ hm hP hp hc hb hV hC H z hsBlend hr k g he ht hs hd h' hY hκ hi'
        T' (A.B.a.clock.adm m) hj hB hz
      obtain ⟨ha,hg⟩ := turnPier hm choice H z hY hq (lark (K z) k hsBlend hr) (Guard.Keeper.sufficient hs) hf
      exact Pier.Room.close hg ha _
  case regular =>
    intro i' f x' S' hR hpB
    obtain ⟨cost,hu,hU,hY'⟩:= grave H z hs hr i' f hR hpB
    have hf:= regularJ g hm hs hC hC' hw hd hY hκ H z ht he hr S' cost f hR hU
    let T' := float (K z) 0 S' (spot _ _) f cost hR.smooth hU hr
    obtain ⟨hv,hB⟩:= turnPier hm choice H z hY hq T' (Guard.Keeper.sufficient hs) hf
    rw [hh]
    change Pier.Room (tell (cologne H z hs hr i' f)) _ _ _ _ _
    rw [hY']
    have hF:(K z).p.mass S' cost ≤ (K z).p.mass S' x':= mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le
    exact ((Pier.Room.close hB hv _)).larger (mul_le_mul_of_nonneg_left hF (Doors.rate_pos L).le)
  case forced =>
    intro i' f x' Wg qF hx' hN hf' hbd
    obtain ⟨cost,hu,hU,hY'⟩:= haunted H z hs i' f hN hf' hbd (d:=d)
    obtain ⟨heF,hRoom⟩:= heavyPier g hm hs choice hC H z he ht hY hκ hq Wg i' f cost hx' hN hf' hU
    rw [hh]
    let V':=(K z).p.mass ((K z).activities.forced i').support cost
    have hL: V' ≤ qF:= mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le
    have hv:=mul_le_mul_of_nonneg_left hL (Doors.rate_pos L).le
    rw [show (tap).ink i' f= _ from hY']
    exact ⟨Pier.Room.larger (Pier.Room.close hRoom heF.earns.format (Guard.Keeper.sufficient hs)) hv,
      (Span.close (Guard.Keeper.sufficient hs) heF choice hm.le).weaken hv hv
        (mul_le_mul_of_nonneg_left hL zero_le_two)⟩
end YM.PhysicalNext.Repeat.Cub

namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple)
namespace Bandage
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
open YM.MergeProof
local notation "H"=> Issue.trail Y
set_option quotPrecheck false
local notation "G'"=> Labels.frames G
open Matric
open Guard
-- anchor at Q reference state. annotations only; analytic transport via Fortune.
variable {Y}
namespace Boutique
variable {meshT:ℕ→∀ p,RG.Shoot.Trail A.B.a p}{N p m d:ℕ}
local notation "H!"=> A.B.bake.make meshT
local notation "μ"=> (0:ℝ)
variable (U: Boutique X meshT N p m)(choice: (A.B.bake.make meshT).Selected)(hd:d+3 ≤ A.B.a.clock.J m)
local notation "ris"=> (H!).rep N p (m+1)
local notation "R'"=> (H!).rep N p m
local notation "fa"=> (Labels.frames G).level d
local notation "J"=> A.B.a.clock.J (m+1)
local notation "t"=> A.B.a.clock.J m
open Motion
include hG Y

theorem pierTables (hz:Nest X Y):
    Pier.Lathe (H!) N p m (hol G) (localSection G d) ((H!).rep N p (m+1))
      (U.castT b choice hd).plate U.gate (C (A.B.a.clock.J (m+1))) (Doors.rate ((H!).S.block m)) :=
  reserveLathe U.hx b.songs b.PStage b.wait (Graces.feet hd b.clock) hz b.r U.stock center
    U.taught rfl hG b.tunes b.furthering b.corners b.shape b.clock b.stamp choice U.down U.up (okC b U choice hd) hd

end Boutique
end Bandage
end YM.PhysicalNext.Repeat.Legato
