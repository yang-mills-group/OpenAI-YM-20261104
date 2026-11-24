import YM.LocalLTE.Ballot.Buttons
import YM.LocalLTE.Vinca.Key
import YM.LocalLTE.Georges.Mile
import YM.LocalLTE.Georges.BeaconT
import YM.LocalLTE.Georges.BasalT
import YM.LocalLTE.Georges.RosinT
/-! Adaptation of YM/MergeProof/Crowding; same budget on Career. -/
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
variable (hP:Circlet.Pitch M.p M.K Q C r) (hp: Pads D R Q M.K C A.delay) (hc: Decked C D R B.span B.shape A.delay) (hb:goodD M.p (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) d)(hV:HasSlots ((Issue.trail V).rep N n m).p ((Issue.trail V).rep N n m).activities) (hC:Mallow.Arrives B.shape A.delay)
local notation "F"=> (Labels.frames G).level d
local notation "n₀"=> A.B.a.S.side m n
local notation "n₁"=> A.B.a.S.side (m+1) n
local notation "w0"=> ((M.profile T).supportExponent+2) -- wrong
variable {K:In A.B.a m n} {x t:ℝ} (H: Turf B N m n)
local notation "Z"=> H.houseB
set_option quotPrecheck false
open PPX MergeProof Next.Free Bid
variable (he : (Issue.trail V).rep N n m=H.output) (ht: (Issue.trail V).rep N n (m+1)=H.inPort) (g:G.Simple)
   (hC': Graces.Moms B.prices M.K B.span M.p.floorL)(hw: Graces.Cruise B.prices D B.recordP B.span B.shape A.delay) (hT: Cub.MainTest B.target B.expense B.span D B.shape C R A.delay)
   {E:ℕ→ℝ}(h' : Chop M.p E B.span) {W:Bid.Worth}(hY:Doors.Budget A.B.a E W) (hκ:Comply B.shape A.delay)
local notation "H!"=> Issue.trail V
local notation "DO"=> duet (Issue.trail V) N n m he ht (H.door)
local notation "Rt"=> H.inPort
local notation "ε0"=> Cub.title G vT
local notation "Πt"=> localSection G d
-- Strengthening enrollment relative to B-author.C.Map. Universally uses payroll at canonical M.Place.This horizon or narrower masks. z.Uniform.
variable (hd:d+3 ≤ A.B.a.clock.J m)
local notation "h0"=> H.inPort
variable (h₀: HasSlots H.inPort.p H.inPort.activities)(hZ: Local.Readable (hol G) (localSection G d) H.inPort.p (A.B.a.S.side (m+1) n) (title G (M.p.profile (A.B.a.clock.J (m+1))))) (i: ((Labels.frames G).level d).Index)
local notation "T2"=> lark (H.inPort) i hZ h₀
local notation "M1"=> Blush.screen H.houseB T2 (H.lamp T2.live) (H.lamp T2.pale) (((L).val:ℂ)^d) F -- notation macro.T2
local notation "Y1"=> Blush.scope H.houseB T2 (0:Site (A.B.a.S.side m n))
variable (hy:i≠ 0)
open YM.LocalLTE.Vinca
include hy hm hP hp hc h' he hd ht hb hC hV g hY hκ hC'
lemma wagesB : ∃ tP:ℝ,YM.Planned.GuardedAtom.Deck (Blush.screen H.houseB (lark (H.inPort) i hZ h₀) (H.lamp (T2|>.live)) (H.lamp (T2|>.pale)) (((L).val:ℂ)^d) F) (0:Site (A.B.a.S.side m n)) Y1 H.output (Real.sqrt (A.B.a.clock.forcedAllowance m)) (Legato.cl0 (M.p.profile (A.B.a.clock.J (m+1))) d (D.L (A.B.a.clock.J (m+1)))) tP:=by
   have hwz:Heir.Release.accepts (B.span J T) (vT).supportExponent ((vB).supportExponent+2) L:= hC' _ _ d hb _ (D.large _).need|>.1
   obtain ⟨a,b,c,hA,hS,hP0,⟨uG,vG,hp0,hU⟩,hR⟩:= Circlet.budgetCardT hm hP hp hc hb hV hC H hZ h₀ i hy g he ht hd h' hY hκ hwz -- order
   obtain ⟨F0,hF0,ha⟩:= hp0.bulk
   rw [he] at hU hR hP0 hp0 hF0 ha
   have ht':1 ≤ Local.factor (hol G) (localSection G d) H.output.p.supportExponent (authors A.B.a m):= YM.LocalLTE.Dilation.factorLarge (livelyCard (n:=n) hY ((Nat.le_add_right d 3).trans hd))
   have hp := Extra.Histories.forcedPos A.B.a m; have hv:1≤Local.turnCost H.output.p.order H.output.p.power:=by unfold Local.turnCost; exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
   have he :=Tare.costs_nonneg hP0 (by exact Real.sqrt_pos.mpr hp)
   have hh:uG ≤ a:= hU ▸ le_mul_of_one_le_left (sumBudget_credit ha) ht'
   refine ⟨vG,⟨⟨F0,hF0,⟨ha.1,ha.2.1,ha.2.2.trans ?_⟩⟩,hp0.packets⟩⟩
   have H0:= hY.room (m+1); have hm0:= hY.fits (Issue.trail V) rfl m d ((Nat.le_add_right d 3).trans hd)
   let S:= A.B.a; let j:= S.clock.J (m+1); let sA:= (S.params (m+1)).columns
   have hW': E j ≤ W.K j:= by
       let k:= Doors.rate ((Issue.trail V).S.block m); have he': 0≤k*sA:= mul_nonneg (Doors.rate_pos _).le (zero_le_one.trans (S.params (m+1)).columns_ge)
       have hd: E j≤(E j+k*sA)*Motion.orbitCost F:= (le_add_of_nonneg_right he').trans (le_mul_of_one_le_right (by linarith only [he',hm0.cost]) (Motion.orbitCost_one_le _))
       exact hd.trans hm0.funds
   have hx:E j ≤ sA:= hW'.trans (by have hf:1 ≤ W.K (j+1):= W.prices _; have hp: W.K j ≤ W.K (j+1):= W.growth (Nat.le_succ j); have he:64*W.K (j+1)^(2:ℕ) ≤ sA := H0; nlinarith only [hf,hp,he])
   have hw:0 ≤ ((L).val:ℝ)^d:= by positivity -- notation λ
   rw [Size.core_axis,if_neg hy] at hR; apply hh.trans ?_
   refine le_trans (le_trans (show a≤ Local.turnCost H.output.p.order H.output.p.power*a+(b+c) from (le_mul_of_one_le_left he.1 hv).trans (le_add_of_nonneg_right (add_nonneg he.2.1 he.2.2))) hR) ?_
   calc _ ≤ E j * (((D.L j).val:ℝ)^d) := by
             have hz:= Work.G08.size_vowel F L (Size.axis F i); rw [Extra.Histories.Size.size_axis,mul_one] at hz; exact mul_le_mul_of_nonneg_left hz.2 (zero_le_one.trans hm0.cost)
        _ ≤ _ := mul_le_mul_of_nonneg_right (hx.trans_eq (by unfold sA S; rw [params_eq A.B.valid])) hw
end YM.PhysicalNext.Repeat.Cub
