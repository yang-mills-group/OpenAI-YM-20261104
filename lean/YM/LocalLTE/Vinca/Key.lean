import YM.LocalLTE.Vinca.Gas
import YM.LocalLTE.Vinca.Live
import YM.LocalLTE.Vinca.Stem
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
open YM.LocalLTE YM.LocalLTE.Vinca Source
set_option quotPrecheck false
variable (hz:Push.Local.Readable (hol G) (localSection G d) H.inPort.p (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (A.B.a.clock.J (m+1))))) (h!:HasSlots (H.inPort|>.p) (H.inPort|>.activities)) (l':ℕ)(Kt:Guard.Keeper H.output.p H.output.activities)
noncomputable def lightPlant : Vinca.Gateway ((Labels.frames G).level d) (hol G) H.inPort (A.B.a.S.side m n) where
    core i:= Graces.canvasB d H (lark H.inPort i hz h!) l' Kt
    reader f b x h hp:= Graces.canvasB d H (Blush.float H.inPort 0 b h.anchor f x h.smooth hp h!) l' Kt
    flag f j yK ht hf:= Graces.canvasB d H (Blush.fan H.inPort 0 j f yK hf ht) l' Kt
-- construct common semantics. M.Destructor. Note size hY fits for later. Transfer permission uses BEFORE allowance C.P.
include g hP hp hc hb hV hC hC' hw hT he ht h' hY hκ hm
variable (hd: d+3≤ A.B.a.clock.J m) (Xk:Wing→Prop)(hk:∀ (i:Support (A.B.a.S.side (m+1) n))(he:0∈i), Xk (.logKey (Blush.found 0 i he)))
local notation "A₁"=> 4*LocalLTE.Dilation.sill (M.p.profile (T)).supportExponent l'
local notation "ε₁"=> (A₁ * Doors.rate L)
local notation "τ₁"=> A₁* E J
include hk hd
lemma chordsP : ∃ Λ: Heading ((Labels.frames G).level d), Vinca.Key (localSection G d) H! N n m (hol G) DO (Vinca.sway H! N n m (hol G) Rt ht (Cub.lightPlant H hz h! l' Kt)) τ₁ ε₁ (2*(Real.exp ((H!).rep N n (m+1)).p.supportExponent* Cub.title G vT)) Λ Xk:=by
  let Tx:= A.B.a; let i:= Tx.clock.J m; let j:=Tx.clock.J (m+1); let L':=D.L j; let K₀:= Tx.budget m; let K':= Tx.budget (m+1)
  let R₀:= localSection G d; let H':= (Issue.trail V); let V₀ :=H'.rep N n m; let V₁:=H'.rep N n (m+1); let a:= K'.threshold; let b:= K₀.threshold
  have hβ := step_paid A.B.a m; have hz' := hz
  have hδ : d+3≤ i:=hd; have hq: d ≤ i:= (Nat.le_add_right d 3).trans hδ; have hj:d ≤ j:= hq.trans hβ.1
  obtain ⟨T'⟩:= hT _ _ (A.B.valid.pays m) i d (first_le A.B.valid m) hβ hδ
  let V':= M.p.kernel; have hb' : Blend 2 a b:= T'.scaleP _ _ rfl (Circlet.shifting (A:=A) (m:=m)).1
  have hi:= Tx.clock.adm m; have hj':=Tx.clock.adm (m+1); let P':=Warehouse.flight (Issue.trail V) N m; let k':= Seal.donne R₀ (sound G d) V'.penalty_pos hi (Next.Foundations.valuation G d) P' hj hb'
  let uP:= matrix R₀ (sound G d) (Carrier.stored P' V'.penalty V'.penalty_pos hi) a b
  let cap:= Seal.cap R₀ (sound G d) V'.penalty_pos hi (Next.Foundations.valuation G d) hj' hj (one_le_two (α:=ℝ))
  have hℓ: Real.exp ((H!).rep N n (m+1)).p.supportExponent = Real.exp (Rt).p.supportExponent:= by rw [ht]
  have ht' : (H!).S.block m=L:= PriceCompiler.block_eq A.B.valid m
  refine ⟨k', kindles _ _ _ _ _ _ ht ht' _ ?_⟩
  rw [hℓ]; have he1:1 ≤ A₁:= one_le_mul_of_one_le_of_one_le (by norm_num) (Real.one_le_exp (mul_nonneg (add_nonneg ((M.p.profile i).price_pos.le) zero_le_two) (by positivity)))
  have hwz:Heir.Release.accepts (B.span J T) (vT).supportExponent ((vB).supportExponent+2) L:= hC' _ _ d hb _ (D.large _).need|>.1
  have hv: Doors.rate L ≤ ε₁:= le_mul_of_one_le_left (Doors.rate_pos _).le he1
  refine ⟨fun i' hi'=>?_,fun f b c' hP hf=>?_,fun f j c' hcc hQ hF hS=> ?_,?_⟩
  · have hv':=jewelfolk hm hP hp hc hb hV hC H hz h! i' g he ht hd h' hY hκ hi' l' Kt T' hi hj hb' Xk (hk _ ankle) hwz -- order!
    exact Ink.weaken hv' (mul_le_mul_of_nonneg_right hv (Work.G08.size_nonneg ..)) (le_of_eq (by simp only [mul_assoc])) le_rfl
  · have hv':= basalH g hm hV hC hC' hw hd hY hκ H ht he h! l' Kt b c' f hP hf Xk (hk b hP.anchor)
    exact Ink.weaken hv' (mul_le_mul_of_nonneg_right hv (mul_nonneg (Real.exp_nonneg _) hf.1)) (le_of_eq (by simp only [mul_assoc];rfl)) le_rfl
  · have hv':= heavyP g hm hV hC H he ht hY hκ hq l' Kt Xk j f c' hQ hcc hF hS -- order.
    have he: 0 ≤ c':= (norm_nonneg _).trans (hS 1)
    exact Ink.weaken hv' (mul_le_mul_of_nonneg_right hv (div_nonneg (mul_nonneg (Real.exp_nonneg _) he) (Real.sqrt_nonneg _))) (le_of_eq (by simp only [mul_assoc]; rfl)) le_rfl
  have hσ: Planned.GuardedAtom.Forecast uP cap:= Cub.leading P' R₀ (sound G d) (Next.Foundations.valuation G d) V' hi hj hb'
  have hh: Local.triangularPrice F cap ≤ E J:= (h' _ _ hβ (first_le A.B.valid m) d hd).2 hj' hi hj
  have ht:1≤ E j:= (hY.fits (Issue.trail V) rfl m d hq).cost
  intro i'; exact hσ.quote (hh.trans (le_mul_of_one_le_left (zero_le_one.trans ht) he1)) i'
end YM.PhysicalNext.Repeat.Cub
