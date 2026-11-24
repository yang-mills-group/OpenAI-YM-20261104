import YM.GapsR2RG.StakeBill
/-! # Enhanced ancillary `Blown` bill on the literal tools of the RG17 Run.
Actual text/identities matched to the RG17/Heading.lean proof. Alignment includes the same Keeper and adopted border (no quotient representation rewrite). -/
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

private lemma seek17R {G':Gauge}{n:Side}(B:BudgetPoint)(X_:Support n)(F_:Config G' n→ℂ)(h:∃ c,B.supBounds 0 X_ F_ c): B.supBounds 0 X_ F_ (sInf {y_| B.supBounds 0 X_ F_ y_}):= ⟨le_csInf h (fun _ hi=> hi.1), fun _ hi l hl ht=> le_csInf h (fun _ hf=> hf.2 _ hi l hl ht)⟩
private lemma doze17R {ι:Type}[Nonempty ι](f:ι→ℂ)(h:∃ y_:ℝ,∀ V,‖f V‖≤y_)(V): ‖f V‖ ≤ sInf {y_|∀ V,‖f V‖≤y_}:= le_csInf h fun _ hu=> hu V
variable (hsBlend: Push.Local.Readable (hol G) (localSection G d) (K z).p (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (A.B.a.clock.J (m+1)))))
local notation "tap"=> Cub.shade H z hs hr hsBlend
local notation "ζ0"=> (2*(Real.exp ((H!).rep N n (m+1)).p.supportExponent*ε0))
include g choice hs hr hP hp hc hb hV hC hC' hw hT he ht h' hY hκ hm
-- choose guard L same. t≈τv. cast valuation map.Record.v
set_option maxHeartbeats 200000 in
set_option maxRecDepth 4096 in
lemma ledgerHereStencil (hd: d+3≤ T): Reserves H! N n m (hol G) tap (E J) (Doors.rate ((H!).S.block m)) :=by
  -- copy Glass
  let Tx:= A.B.a; let i:= Tx.clock.J m; let j:=Tx.clock.J (m+1); let L':=D.L j; let K₀:= Tx.budget m; let K':= Tx.budget (m+1)
  let R₀:= localSection G d; let H':= (A.B.bake.make meshT); let V₀ :=H'.rep N n m; let V₁:=H'.rep N n (m+1); let a:= K'.threshold; let b:= K₀.threshold
  have hz := step_paid A.B.a m
  have hδ : d+3≤ i:=hd; have hq: d ≤ i:= (Nat.le_add_right d 3).trans hδ
  have hj:d ≤ j:= hq.trans hz.1
  obtain ⟨T'⟩:= hT _ _ (A.B.valid.pays m) i d (first_le A.B.valid m) hz hδ
  let W:= M.p.kernel; have hb' : Blend 2 a b:= T'.scaleP _ _ rfl (Circlet.shifting (A:=A) (m:=m)).1
  have hi:= Tx.clock.adm m; have hj':=Tx.clock.adm (m+1); let P':=Warehouse.flight (Issue.trail V) N m; let k:= Seal.donne R₀ (sound G d) W.penalty_pos hi (Next.Foundations.valuation G d) P' hj hb'
  let uP:= matrix R₀ (sound G d) (Carrier.stored P' W.penalty W.penalty_pos hi) a b
  let cap:= Seal.cap R₀ (sound G d) W.penalty_pos hi (Next.Foundations.valuation G d) hj' hj (one_le_two (α:=ℝ))
  have he':(H!).S.block m=L:=PriceCompiler.block_eq A.B.valid m
  let ν:=(H!).rep N n m
  let sk':= Guard.Keeper.sufficient hs; let W':= H!; let P₀:= W'.rep N n m; let P₁:= W'.rep N n (m+1)
  constructor
  · intro i' x
    change Staked (tell (Cub.border H z hs hr hsBlend i')) (P₀) _
    unfold Cub.border; split
    · let F':= Extra.Histories.primary (0:Site n₀) (((L).val:ℂ)^d • (F).e0)
      have hh : Staked F' (P₀) 0:= ⟨0,Blown.primary _ (le_refl _), (mul_zero _).le⟩
      have hE := ((hY.fits W' rfl _ _ hq).cost)
      apply (hh.closes (primary_format (H:=hol G) _) sk').more ?_
      exact mul_nonneg (zero_le_one.trans hE) (Work.G08.size_nonneg ..)
    next he0=>
       have hwz:Heir.Release.accepts (B.span J T) (M.p.profile j).supportExponent ((M.p.profile i).supportExponent+2) L:= hC' _ _ d hb _ (D.large _).need|>.1
       have h1:= primaryJ hm hP hp hc hb hV hC H z hsBlend hr i' g he ht hs hd h' hY hκ he0 T' hi hj hb' hwz
       have hh:= jewelJ hm hP hp hc hb hV hC H z hsBlend hr i' g he ht choice hs hd h' hY hκ he0 T' hi hj hb' (fun _=>True) trivial hwz
       rw [he']; exact (stakeDebit H z hY hq _ _ h1 (choice.represents N n m hm.le)).closes hh.earns.format sk'
  · intro i₁ T₁ v₁ b₂ R₁ hf h₁T
    unfold R₁ at *
    rw [ht] at hf h₁T; rw [ht,he'] -- R₁ let, unfold first
    let a:=sInf {b' | (K z).p.supBounds 0 b₂ T₁ b'}; have ha:=seek17R (K z).p b₂ T₁ (show ∃ b', (K z).p.supBounds 0 b₂ T₁ b' from ⟨v₁,h₁T⟩)
    let T':=float (K z) 0 b₂ hf.anchor T₁ a hf.smooth ha hr
    rw [show (tap).tint i₁ T₁ =prepare H z hs (d:=d) T' by unfold Cub.shade; dsimp only; unfold Cub.cologne; rw [dif_pos ⟨hf,v₁,h₁T⟩];rfl]
    have h1 := regularJ g hm hs hC hC' hw hd hY hκ H z ht he hr b₂ a T₁ hf ha
    have hh:=basalJ g hm hs choice hC hC' hw hd hY hκ H z ht he hr b₂ a T₁ hf ha (fun _=>True) trivial
    refine ((stakeDebit H z hY hq _ _ h1 (choice.represents N n m hm.le)).closes hh.earns.format sk').more (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (csInf_le ⟨0,fun i hi=>hi.1⟩ h₁T) (Real.exp_pos _).le) (Doors.rate_pos _).le)
  · intro i₁ T₁ v₁ R₁ hv hT hv' hT'
    unfold R₁ at *
    rw [ht] at hT; rw [ht,he']
    let a:=sInf {b' | ∀ W, ‖T₁ W‖ ≤ b'}; have ha : ∀ V,‖T₁ V‖ ≤ a:=doze17R T₁ ⟨v₁,hT'⟩
    let T':=fan (K z) 0 i₁ T₁ a ha hT
    rw [show (tap).ink i₁ T₁=prepare H z hs (d:=d) T' by unfold Cub.shade; dsimp only; unfold Cub.trick; rw [dif_pos ⟨hT,hv,v₁,hT'⟩];rfl]
    have h1:= heavyStake g hm hs choice hC H z he ht hY hκ hq i₁ T₁ a hv hT ha
    have hh:= heavyJ g hm hs choice hC H z he ht hY hκ hq (fun _=>True) i₁ T₁ a trivial hv hT ha
    refine (h1.closes hh.earns.format sk').more (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (csInf_le ⟨0,fun i hi=> (norm_nonneg _).trans (hi 1)⟩ hT') (Real.exp_pos _).le) (Real.sqrt_nonneg _)) (Doors.rate_pos _).le)
end YM.PhysicalNext.Repeat.Cub

