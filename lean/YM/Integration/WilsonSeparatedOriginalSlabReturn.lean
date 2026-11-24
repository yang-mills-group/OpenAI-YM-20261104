import YM.Integration.WilsonSeparatedOriginalSlabFold
import YM.Integration.WilsonSeparatedOriginalSlabWave

/-! The normalized physical space-time moment and the retained lower joint source are compared under a single transfer. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabReturn
open Function Set MeasureTheory Lattice Wilson RG Source Extraction RG05Readout RG05Readout.Native RG05Readout.Flatten
open RG05Readout.Pulse RG05Readout.Many RG05Readout.Address PhysicalNext.Repeat.Legato
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open RG05Readout.View RG05Readout.Records Extra.Histories
open WilsonReportHarvestSlabLabels WilsonAllDateHarvestPropagation
open scoped Topology Classical BigOperators
variable {G:Gauge}

private theorem step {low high:Side}{op:StepData low high}{β:ℝ}(valid:op.IsKernel β G)
    (F H:Config G high → ℂ)(cf:Integrable F (prior G _))(ch:Integrable H (prior G _)):
    op.push β (fun W=>F W-H W)=fun V=>op.push β F V-op.push β H V:=by
  funext V
  simp only [StepData.push,smul_sub]
  rw [integral_sub (StepData.push_slice valid V F cf) (StepData.push_slice valid V H ch)]

theorem difference (A:History G)(N per:ℕ){u n:ℕ}(un:u ≤ n)
    (F H:Config G (A.S.side n per) → ℂ)(cf:Integrable F (prior G _))(ch:Integrable H (prior G _)):
    pushTo A N per un (fun W=>F W-H W)=fun V=>pushTo A N per un F V-pushTo A N per un H V:=by
  induction n,un using Nat.le_induction with
  | base=>simp
  | succ j uj ih=>
    rw [pushTo_next A N per uj,pushTo_next A N per uj,pushTo_next A N per uj,
      step (A.levels.transition_mass ..) F H cf ch]
    exact ih _ _ (StepData.push_integrable (A.levels.transition_mass ..) _ cf)
      (StepData.push_integrable (A.levels.transition_mass ..) _ ch)

variable (R:Run G){u n m N per:ℕ}(s:Fin 3 → ℕ)(S:(i:Fin 3) → Emblems R.family (s i))(x:(i:Fin 3) → Palette R.family (s i))
variable (o:Fin 3 → Site (R.family.side n per))(E:Fin 3 → Motion)
local notation "C"=>R.family
local notation "R₃"=>Stock.census (Fin 3)
local notation "Ward"=>Mine.ward o E R₃ n

def last (retained:Config G ((C).side n per) → Poly Ward)(W:Config G ((C).side n per)):ℂ:=
  (baseFold o E R₃ (retained W)).part entire

def filed (retained:Config G ((C).side n per) → Poly Ward)(un:u ≤ n):ℂ:=
  pushTo (C).path N per un (last R o E retained) 1/liftVac (C).path N per u 1

private theorem partCost {I X:Type}[DecidableEq I]{B:Census I}[MeasurableSpace X]
    {μ:Measure X}(F:X → Poly B)(v:B.Mode)(cash:Integrable F μ):
    Integrable (fun W=>(F W).part v) μ:=((Poly.get v).restrictScalars ℝ).integrable_comp cash

theorem live (retained:Config G ((C).side n per) → Poly Ward)
    (paid:Integrable (fun W=>baseFold o E R₃ (retained W)) (prior G ((C).side n per))):
    Integrable (last R o E retained) (prior G ((C).side n per)):=
  partCost (fun W=>baseFold o E R₃ (retained W)) entire paid

theorem measured (nN:n ≤ N)(un:u ≤ n)(opened:u+1 ≤ N)(f:Fin 3 → Body)
    (retained:Config G ((C).side n per) → Poly (Mine.ward o (fun _=>(1,false)) R₃ n))
    (paid:Integrable (last R o (fun _=>(1,false)) retained) (prior G ((C).side n per))):
    WilsonSeparatedOriginalSlabWave.scan R s (fun i=>Launch (m:=m) s S x i N) o nN opened 1 (joint Finset.univ f)-
      filed (N:=N) R o (fun _=>(1,false)) retained un=
    pushTo (C).path N per un (fun W=>WilsonSeparatedOriginalSlabFold.joint (m:=m) C o (fun _=>(1,false)) s
      (fun z=>f z.val.1) S x nN W-last R o (fun _=>(1,false)) retained W) 1/liftVac (C).path N per u 1:=by
  let E':Fin 3 → Motion:=fun _=>(1,false)
  let q':ManyStem C o n → Body:=fun z=>f z.val.1
  let old:=last R o E' retained
  let F:=WilsonSeparatedOriginalSlabFold.joint (m:=m) C o E' s q' S x nN
  have pf:Integrable F (prior G ((C).side n per)):=WilsonSeparatedOriginalSlabFold.paid C o E' s q' S x R.makes nN
  have read:=WilsonSeparatedOriginalSlabFold.held (m:=m) C o E' s q' S x R.makes nN un 1
  rw [WilsonSeparatedOriginalSlabWave.clinics]
  change _-pushTo (C).path N per un old 1/liftVac (C).path N per u 1=pushTo (C).path N per un (fun W=>F W-old W) 1/liftVac (C).path N per u 1
  rw [difference (C).path N per un F old pf paid,sub_div,read]
  rfl

end YM.Integration.WilsonSeparatedOriginalSlabReturn
