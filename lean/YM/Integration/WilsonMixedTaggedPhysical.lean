import YM.Integration.WilsonMixedTaggedCourseEntry
import YM.Integration.WilsonMixedTaggedSession
import YM.Integration.WilsonMixedTaggedCaptureEntries
import YM.Integration.WilsonMixedTaggedReopening
import YM.Integration.WilsonAllDateHarvestTuningModes
import YM.Integration.WilsonMixedTaggedFields

/-! The original, separated finite input roster, its actual Wilson transport
and the stripped old-gas replay run through one and the same lower hierarchy. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMixedTaggedPhysical
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout
open RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open WilsonMixedTaggedRoster WilsonMixedTaggedOutput
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} (R:Run G) {n m N p d k h D₀:ℕ} {W:Type} [DecidableEq W] [Fintype W]
local notation "C₀" => R.family
variable (o:W → Site (R.family.side n p)) (E:W → Motion) (s:W → ℕ) (q:ManyStem R.family o n → Body)
variable {rail:Address.Rail R.family} {worth:Worth} {rates:ℕ → ℕ}
variable (book:OPE.Package R.family worth rates rail) (stock:Storage R.family rail)
variable (P:(v:W) → Sight R.family (s v) p) (S:(v:W) → Emblems R.family (s v)) (x:(v:W) → Palette R.family (s v))
variable (roster:Census W) {Q:ℝ} {capbook:ℕ → ℕ → ℝ}
local notation "A" => Mine.tree o E
local notation "ward" => Mine.ward o E roster
local notation "Y" => (C₀).path.rep N p
local notation "I" => headings o E q
local notation "T" => plants (m:=m+1) s P S x
local notation "rows" => imprint (C:=R.family) R.makes A I T
local notation "rad" => envelope C₀ (m+1) (d+1) k Q
local notation "δ" => Real.exp (-(D₀:ℝ))
local notation "expo" => fun i:ℕ=>if i=m+1 then ((C₀).path.levels.budget i).supportExponent-4
  else ((C₀).path.levels.budget i).supportExponent
local notation "fields" => (i:ℕ) → Config G ((C₀).side i p) → Poly (ward i)
local notation "trueField" => fun i (iN:i ≤ N)=>gust (C₀).path N p N
  (birth (ward i) (Y N) (WilsonMixedTaggedFields.columns o E s q S x (m+1) N i)) i iN
local notation "shifted" => RG05Readout.Many.total C₀ Q (d+1) (m+1)
local notation "rust" => rusty C₀ (m+1) k

include book stock in
theorem original (nm:n ≤ m) (mN:m+1 < N)
    (ready:Warm C₀ n (d+1) k) (room:Fintype.card W*2 ≤ (C₀).path.levels.clock.J n)
    (spine:∀j:W,Spine rail capbook R.makes n p (s j) N (P j) (S j))
    (degree:∀v,s v ≤ d) (caps:∀v:ManyStem C₀ o n,Cap (s v.val.1+2) (q v) 1)
    (qp:0 < Q) (charge:∀v,size (x v) ≤ Q) (qh:Q ≤ ((C₀).path.levels.clock.hatBeta (m+1))^h)
    (clear:Clearance o E s I roster (m+1))
    (span:let B:=((C₀).path.levels.budget (m+1)).B; D₀*(4*B+2)+2*B ≤ B^2) :
    ∃ F L:fields, Replay A s (le_refl n) (m+1) F N ∧ Replay A s (le_refl n) (m+1) L N ∧ 
      (∀j:ℕ,n ≤ j → ∀jN:j ≤ N,F j=trueField j jN) ∧ 
      L (m+1)=restore (Y (m+1)) (fun v=>(rows (m+1) mN.le v).2.1)
        (fun v=>profile (Y (m+1)).activities (rows (m+1) mN.le v).2.2)
        (0:Support ((C₀).side (m+1) p) → Config G ((C₀).side (m+1) p) → Poly (ward (m+1))) 0 ∧ 
      ∀j:ℕ,n ≤ j → ∀jm:j ≤ m+1,WilsonMixedTaggedSession.Matched (B:=ward j)
        (Y j) (rows j (jm.trans mN.le)) ((A).supportX j) (fun _=>rad j) (expo j) δ (F j) (L j) := by
  have nm':n ≤ m+1:=nm.trans m.le_succ
  have purse:Purse C₀ rust shifted n (m+1) (d+1) k:=ignite ready qp (by omega)
  let v:=Launch (m:=m+1) s S x
  have lesson:Lesson (D:=rail) R.makes s n N N p T capbook shifted v:=by
    refine ⟨fun j=>⟨P j,S j,spine j,fun _=>rfl,fun i _ _=>nearpoints (S j) (x j) _,fun i hi hiN=>?_⟩⟩
    exact head_cost (spine j) nm' mN.le (Nat.add_le_add_right (degree j) 1) (charge j) hi hiN
  have lamp:=Lesson.lights s R.makes (lesson.revise s R.makes (le_refl n) mN.le)
  obtain ⟨base,prepared⟩:=headlines (N:=m+1) o E q
  have start:∀v:ManyStem C₀ o n,Cap (s ((A).labelY n v)+2) (I n v) 1:=by
    rw [base];exact caps
  have straight:=WilsonMixedTaggedCourse.toured (m:=m+1) o E ward (f:=rust) (k:=k) (le_refl n) room
    (fun i _ im=>(rust_local (k:=k) (C:=C₀) im).le)
  have manual:Occupancy o ((C₀).path.levels.clock.J n):=fun _=>(Finset.card_le_univ _).trans (by omega)
  obtain ⟨F,run,known,bank⟩:=WilsonMixedTaggedFields.program (m:=m+1) o E s q S x roster R.makes
    book stock P nm' mN.le spine manual caps charge qp ready degree
  have short:Replay A s (le_refl n) (m+1) F N:=⟨fun j nj jm=>run.downhill j nj (jm.trans_le mN.le)⟩
  let inc:=WilsonMixedTaggedSeparatedBoard.admitted o E roster nm' (le_refl (m+1))
  let X:=fun U=>narrow inc (F (m+1) U)
  have paid:MenuBoard (Y (m+1)) (rows (m+1) mN.le) X ((A).supportX (m+1))
      (fun _=>rad (m+1)) ((C₀).path.levels.budget (m+1)).supportExponent 1:=by
    rw [if_neg mN.ne] at bank
    exact bank
  obtain ⟨H,K,cart,actual,_,_,smallH,smallK⟩:=WilsonMixedTaggedCaptureEntries.initial
    (d:=d+1) (k:=k) (h:=h) (L:=Fintype.card W) (D:=D₀) R mN.le span
    (fun _:ManyStem C₀ o (m+1)=>Q) ((A).supportX (m+1)) (rows (m+1) mN.le) X
    (fun _=>qp) (fun _=>qh) paid (WilsonAllDateHarvestTuningModes.cardinal o E roster nm' le_rfl)
    (fun v many=>by
      obtain ⟨u,hu,w,hw,_,_,far⟩:=WilsonAllDateHarvestTuningModes.pair o E roster nm' v many
      exact ⟨u,hu,w,hw,far⟩)
  let dark:=shadow A s I (m+1)
  have dormant (i:ManyStem C₀ o (m+1)) (hi:i∈dark) :
      (rows (m+1) mN.le i).2.1=0 ∧ profile (Y (m+1)).activities (rows (m+1) mN.le i).2.2=0:=by
    have absent : rows (m+1) mN.le i=0 := lesson.cold A s I R.makes mN.le nm' i hi
    have forced := congrArg (fun a:Three G ((C₀).side (m+1) p)=>
      profile (Y (m+1)).activities a.2.2) absent
    refine ⟨congrArg (fun a:Three G ((C₀).side (m+1) p)=>a.2.1) absent,forced.trans ?_⟩
    funext box U
    simp [profile,cram]
  have costed:=WilsonMixedTaggedReopening.original (R:=Y (m+1)) inc dark dormant
    (fun _=>mul_pos (rust_paid _).1 (grantw (totalpos qp _))) (masts_block o E s I nm' roster clear)
    (known (m+1) nm' mN.le).2 (show Served _ _ _ X _ (fun _=>rad (m+1)) _ δ from
      ⟨H,K,cart,smallH,smallK,actual⟩)
  obtain ⟨Z,admitted,top,empty⟩:=WilsonMixedTaggedCourseEntry.original A s I R.makes stock
    (le_refl n) nm (Nat.lt_of_succ_lt mN) purse lamp prepared start
    (straight.high_use m nm (Nat.lt_succ_self _)) paid.fettled (Real.exp_pos _) costed
  have price:‖(δ:ℂ)‖=δ:=by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have norm:‖(δ:ℂ)‖ ≤ 1:=by rw [price,Real.exp_le_one_iff]; exact neg_nonpos.mpr (Nat.cast_nonneg _)
  obtain ⟨L,replay,head,ledger⟩:=WilsonMixedTaggedSession.original A ward s I R.makes stock
    (le_refl n) nm' mN.le purse straight lamp short (fun v=>(degree v).trans d.le_succ) prepared start
    (by linarith : ((C₀).path.levels.budget (m+1)).supportExponent-4 ≤ 
      ((C₀).path.levels.budget (m+1)).supportExponent-1) admitted norm (funext top).symm
  exact ⟨F,L,short,replay,fun j nj jN=>(known j nj jN).1,head.trans (funext empty),price ▸ ledger⟩

end YM.Integration.WilsonMixedTaggedPhysical
