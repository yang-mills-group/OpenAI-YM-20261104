import YM.Integration.WilsonReportHarvestSlabShiftReceipt
import YM.Integration.WilsonSeparatedOriginalSlabReturn
import YM.Integration.WilsonSeparatedOriginalSlabFolio
import YM.Integration.WilsonPositionSeparatedProfileSlabReceipt

/-! The independently held grade-zero coefficient funds the original uncentered wave on all earlier dates of the very same retained history. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabPosting
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open WilsonReportHarvestSlabLabels WilsonAllDateHarvestPropagation
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G){b m t N per:ℕ}

def Dates (b:ℕ):= {u:ℕ // R.family.ref 0 ≤ u ∧ u ≤ b}

private theorem zero (A:Poly (Stock.census (Fin 3))):
    WilsonReportHarvestSlabShiftLabels.translated (0:Fin 3 → ℂ) A=A:=by
  have h:Mach (Stock.census (Fin 3)) (0:Fin 3 → ℂ)=0:=by simp [Mach]
  rw [WilsonReportHarvestSlabShiftLabels.translated,h,Extra.Trajectories.pass_zero,one_mul]

variable (nm:b+1 ≤ m)(mt:m ≤ t)(nt:b+1 < t)(tN:t ≤ N)
variable (s:Fin 3 → ℕ)(S:(i:Fin 3) → Emblems R.family (s i))(P:(i:Fin 3) → Sight R.family (s i) per)
  (x:(i:Fin 3) → Palette R.family (s i))(o:Fin 3 → Site (R.family.side (b+1) per))
local notation "C"=>R.family
local notation "n"=>b+1
local notation "E"=>fun _:Fin 3=>(1,false)
local notation "roster"=>Stock.census (Fin 3)
local notation "A"=>Mine.tree o E
local notation "J"=>Mine.ward o E roster
local notation "Y"=>(C).path.rep N per

/-- Each printed scalar field keeps the actual deposited high history, full low prior and matching vacuum and one-mark entries. -/
def Posted (f:Fin 3 → Body)(printed:Dates R b → ℂ):Prop:=
  let q:=fun z:ManyStem C o n=>f z.val.1
  let rows:=imprint R.makes A (headings o E q) (plants (m:=m) s P S x) t tN
  let colors:=WilsonAllDateHarvestPhysical.columns o E s q S x m N n
  let real:=gust (C).path N per N (birth (J n) (Y N) colors) n (nt.le.trans tN)
  let gate:=WilsonAllDateHarvestEndpointOpening.opening (WilsonMixedTaggedSeparatedBoard.admitted o E roster nm mt) (shadow A s (headings o E q) t)
  let inlet:=fun W=>gate (density (Y t) rows (fun _ _=>0) (fun _ _=>0) W)
  ∃L:∀j,Config G ((C).side j per) → Poly (J j),∃route:Replay A s (le_refl n) t L N,
    L t=inlet ∧
    (∀j (nj:n ≤ j)(jt:j ≤ t) V,((Y j).eval V)⁻¹ • L j V=actualTransport C (N:=N)
      (fun W=>((Y t).eval W)⁻¹ • WilsonReportHarvestEarlierSlab.route route j nj jt (inlet W)) jt V) ∧
    Integrable (fun W=>baseFold o E roster (L n W)) (prior G ((C).side n per)) ∧
    (∀W,(baseFold o E roster (real W)).part (roster).quiet=(baseFold o E roster (L n W)).part (roster).quiet) ∧
    (∀i W,(baseFold o E roster (real W)).part ((roster).fire i)=(baseFold o E roster (L n W)).part ((roster).fire i)) ∧
    ∀a:Dates R b,printed a=WilsonSeparatedOriginalSlabReturn.filed (N:=N) R o E (L n) (a.2.2.trans b.le_succ)

theorem issued (book:OPE.Package C R.w (mutt (C).path.levels R.Q) R.doors)(f:Fin 3 → Body){target:ℝ}
    (purchased:WilsonReportHarvestSlabShiftReceipt.Captured R nm mt nt tN s S P x o E (fun z=>f z.val.1) target):
    ∃printed,WilsonSeparatedOriginalSlabFolio.settled R s (fun i=>Launch (m:=m) s S x i N) o (nt.le.trans tN)
      (fun a:Dates R b=>a.val) (fun a=>(Nat.succ_le_succ a.2.2).trans (nt.le.trans tN)) (fun _=>1)
      (Posted R nm mt nt tN s S P x o) ((1+WilsonPositionSeparatedProfileStableReturn.price)*target) f printed:=by
  obtain ⟨L,route,first,carried,live,quiet,one,shifts⟩:=purchased
  let printed:=fun a:Dates R b=>WilsonSeparatedOriginalSlabReturn.filed (N:=N) R o E (L n) (a.2.2.trans b.le_succ)
  refine ⟨printed,⟨L,route,first,carried,live,quiet,one,fun _=>rfl⟩,?_⟩
  obtain ⟨cost,X,form,cash,unit,paid,seen⟩:=shifts 0 (fun _=>by simp)
  simp only [zero] at seen
  intro a
  let un:=a.2.2.trans b.le_succ
  have read:=WilsonSeparatedOriginalSlabReturn.measured (m:=m) R s S x o (nt.le.trans tN) un
    ((Nat.succ_le_succ a.2.2).trans (nt.le.trans tN)) f (L n) (WilsonSeparatedOriginalSlabReturn.live R o E (L n) live)
  rw [show printed a=WilsonSeparatedOriginalSlabReturn.filed (N:=N) R o E (L n) un from rfl,read]
  simp only [WilsonSeparatedOriginalSlabFold.joint,WilsonSeparatedOriginalSlabReturn.last]
  rw [←seen a.val a.2.2]
  have bound:=WilsonPositionSeparatedProfileStableReturn.original R book a.2.1 a.2.2 (b.le_succ.trans (nt.le.trans tN)) X form cash
  have entry:‖X.x 0‖ ≤ ((C).labels.level 0).coeffSize X.x:=Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ _)
  have nonneg:0 ≤ WilsonPositionSeparatedProfileStableReturn.price:=div_nonneg WilsonPositionSeparatedProfileStableStep.shrink_pos.le
    (sub_pos.mpr WilsonPositionSeparatedProfileStableStep.shrink_lt).le
  calc
    _ ≤ ‖WilsonPositionSeparatedProfileStableReturn.read (N:=N) R a.2.2 X-X.x 0‖+‖X.x 0‖:=norm_le_norm_sub_add _ _
    _ ≤ WilsonPositionSeparatedProfileStableReturn.price*cost+cost:=add_le_add bound (entry.trans unit)
    _ = (1+WilsonPositionSeparatedProfileStableReturn.price)*cost:=by ring
    _ ≤ _:=mul_le_mul_of_nonneg_left paid (by linarith)

end YM.Integration.WilsonSeparatedOriginalSlabPosting
