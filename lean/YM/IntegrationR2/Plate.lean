import YM.FullVolume.Panel.Beam
import YM.IntegrationR2.Undivided
import YM.OPE.Columns.Accounts

/-!
Keep a support +2 Blown reserve before reorientation and the *undivided*
full output mass bound on incoming forces, using the *same* paid facilities
as those for `Leading` estimates. Adapted from RG17/Heading. This is on the *actual* finite-tool ledger. Strengthens
`YM/FullVolume/Panel/{Port,Beam}` using their actual proofs (and
`YM/OPE/Columns/Clock.lean` served as a model for RG17/Heading).
No new model, no rechoice of castT.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric.R2
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}

/-- Prints *additional* receipts: no new rep. At zero input to a forced
channel no Span assertion needed (blank already guaranteed by Tool.Cap). -/
structure ReservePlate (B:SectionData F) (H:History G) (N p i:ℕ) (Y:Hol G) (Z:Rep G (H.S.side (i+1) p)) (L:Side) (P:MergeProof.Matric.Plate F (H.S.side (i+1) p) (H.S.side i p)) (u ζ:ℝ) (S:GaugeDoor (H.rep N p (i+1)) (H.rep N p i)) : Prop where
   main j: let x:=Size.axis F j
           Plus (H.rep N p i) (tell (P.main j)) (u*F.coeffSize (vowel F L (F.core x)))
   regular j U t: let b:= mapSeat (n:=H.S.side (i+1) p) j
                  RegFit Z 0 d Y b U → Z.p.supBounds 0 b U t → Plus (H.rep N p i) (tell (P.tint j U)) (ζ*(Z.p.mass b t))
   forced (X:Wing→Prop) j U t: let a:= Z.p.mass (Z.activities.forced j).support t
       U≠0→ X (.gasKey j)→ SlotFit Z 0 j U→ (∀ V, ‖U V‖ ≤ t) →
           Span B H N p i Y (tell (P.ink j U)) 0 (exactGas Z.activities j U) 0 S X (Extra.Histories.fare Z j U) 0 (ζ*a) (ζ*a) (2*a) ∧
           Plus (H.rep N p i) (tell (P.ink j U)) (ζ*a)
end YM.MergeProof.Matric.R2

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

private lemma seek18 {G':Gauge}{n:Side}(B:BudgetPoint)(X_:Support n)(F_:Config G' n→ℂ)(h:∃ c,B.supBounds 0 X_ F_ c): B.supBounds 0 X_ F_ (sInf {y_| B.supBounds 0 X_ F_ y_}):= ⟨le_csInf h (fun _ hi=> hi.1), fun _ hi l hl ht=> le_csInf h (fun _ hf=> hf.2 _ hi l hl ht)⟩
private lemma doze18 {ι:Type}[Nonempty ι](f:ι→ℂ)(h:∃ y_:ℝ,∀ V,‖f V‖≤y_)(V): ‖f V‖ ≤ sInf {y_|∀ V,‖f V‖≤y_}:= le_csInf h fun _ hu=> hu V
variable (hsBlend: Push.Local.Readable (hol G) (localSection G d) (K z).p (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (A.B.a.clock.J (m+1)))))
local notation "tap"=> Cub.shade H z hs hr hsBlend
local notation "ζ0"=> (2*(Real.exp ((H!).rep N n (m+1)).p.supportExponent*ε0))
include g choice hs hr hP hp hc hb hV hC hC' hw hT he ht h' hY hκ hm
open MergeProof.Matric.R2
set_option maxHeartbeats 1700000 in
lemma plateReserve (hd: d+3 ≤ T):
   ReservePlate Πt H! N n m (hol G) ((H!).rep N n (m+1)) ((H!).S.block m) tap (E J) (Doors.rate ((H!).S.block m)) DO :=by
  let Tx:= A.B.a; let i:= Tx.clock.J m; let j:=Tx.clock.J (m+1)
  have hz := step_paid A.B.a m
  have hδ : d+3≤ i:=hd; have hq: d ≤ i:= (Nat.le_add_right d 3).trans hδ
  have hj:d ≤ j:= hq.trans hz.1
  have he':(H!).S.block m=L:=PriceCompiler.block_eq A.B.valid m
  let Y:= (H!).rep N n m
  have HY := choice.represents N n m hm.le
  have hread: Local.Readable (hol G) (localSection G d) ((H!).rep N n m).p n₀ (authors A.B.a m) := by rw [HY.vac]; exact livelyCard hY hq (n:=n)
  -- Xk never changes inside the conclusion; main and regular unconditional
  suffices h: ReservePlate Πt H! N n m (hol G) (K z) L tap (E J) (Doors.rate L) DO by
     -- cast handles H!.U hidden in DO; transport only this presentation parameter explicitly
     exact (show ∀ Z', (K z) = Z' → ReservePlate Πt H! N n m (hol G) Z' ((H!).S.block m) tap (E J) (Doors.rate ((H!).S.block m)) DO from fun _ he=> by rw [← he,he']; exact h) _ ht.symm
  constructor
  case main=>
    intro i' x'
    change Plus Y (tell (Cub.border H z hs hr hsBlend i')) _
    unfold Cub.border; split
    next hi' =>
       subst i'
       -- avoid `primary` implicit alphabet ambiguity
       have hcost : (E J)*(F).coeffSize (vowel F L ((F).core x'))=0 := by
          rw [show x'=Size.axis (F) 0 from rfl, Size.core_axis, if_pos rfl,show vowel F L 0=0 from funext fun i=>by simp [vowel], show (F).coeffSize 0=0 from by simp [Frame.coeffSize],mul_zero]
       rw [hcost]; apply Plus.captured (Y:=hol G) _ (primary_format _)
       exact Blown.primary _ (by rw [zero_div])
    next hi' =>
       obtain ⟨T'⟩:= hT _ _ (A.B.valid.pays m) i d (first_le A.B.valid m) hz hδ
       have hb' : Blend 2 (B₂).threshold (B₁).threshold := T'.scaleP _ _ rfl (Circlet.shifting (A:=A) (m:=m)).1
       have hwz:Heir.Release.accepts (B.span J T) (M.p.profile j).supportExponent ((M.p.profile i).supportExponent+2) L:= hC' _ _ d hb _ (D.large _).need|>.1
       have hh:= primaryJ hm hP hp hc hb hV hC H z hsBlend hr i' g he ht hs hd h' hY hκ hi' T' (Tx.clock.adm m) hj hb' hwz
       refine Plus.captured (Y:=hol G) _ ?_ (projectPlus ((sk).supply _) hh HY hread)
       exact (MergeProof.growing ((sk).supply _) hh HY hread).1.format
  case regular=>
    intro i' f x₁ t₁ hq hp'
    let t:= sInf {b| (K z).p.supBounds 0 (mapSeat i') f b}; have hg: (K z).p.supBounds 0 (mapSeat i') f t := seek18 _ _ f ⟨_,hp'⟩; have ht' : t ≤ x₁:= csInf_le ⟨0,fun _ h=> h.1⟩ hp'
    have hX : (tap).tint i' f=prepare H z hs (float (K z) 0 (mapSeat i') (spot _ _) f t hq.smooth hg hr):= by unfold shade; dsimp only; unfold cologne; rw [dif_pos ⟨hq,x₁,hp'⟩ ]; rfl
    have hz:= regularJ g hm hs hC hC' hw hd hY hκ H z ht he hr (mapSeat i') t f hq hg
    rw [hX]; refine (Plus.captured (Y:=hol G) _ ?_ (projectPlus ((sk).supply _) hz HY hread)).more (mul_le_mul_of_nonneg_left ?_ (Doors.rate_pos L).le)
    · exact (MergeProof.growing ((sk).supply _) hz HY hread).1.format
    exact mul_le_mul_of_nonneg_left ht' (Real.exp_pos _).le
  case forced=>
    intro Xk i' f c' q' hh hx' hf he''
    let t:=sInf {b|∀ V,‖f V‖ ≤ b}; have hz'(p):‖f p‖ ≤ t:=doze18 _ ⟨c',he''⟩ _
    have hp': t ≤ c':=csInf_le ⟨0,fun y' hy=>le_trans (norm_nonneg (f 1)) (hy _)⟩ he''
    have hX:(tap).ink i' f=prepare H z hs (fan (K z) 0 i' f t hz' hf):= by unfold shade; dsimp only; unfold trick; rw [dif_pos ⟨hf,hh,c',he''⟩]; rfl
    let o:= (K z).p.mass ((K z).activities.forced i').support t
    have hv' : o ≤ (K z).p.mass ((K z).activities.forced i').support c' :=mul_le_mul_of_nonneg_left hp' (Real.exp_pos _).le
    have hv:=mul_le_mul_of_nonneg_left hv' (Doors.rate_pos L).le
    obtain ⟨hα,hβ⟩:= heavyPlusR2 g hm hs choice hC H z he ht hY hκ hq Xk i' f t hx' hh hf hz'
    rw [hX]; exact ⟨(Matric.Span.close sk hα choice hm.le).weaken hv hv (mul_le_mul_of_nonneg_left hv' zero_le_two), (Plus.captured sk hα.earns.format hβ).more hv⟩
end YM.PhysicalNext.Repeat.Cub

