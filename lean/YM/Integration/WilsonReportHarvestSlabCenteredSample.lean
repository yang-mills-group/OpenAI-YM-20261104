import YM.Integration.WilsonReportHarvestSlabCenteredPhysical

/-! The signed connected three-field observable at the original earlier held gauge. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabCenteredSample
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open WilsonReportHarvestSlabLabels WilsonAllDateHarvestPropagation WilsonReportHarvestSlabCenteredPush
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} (R:Run G){b m t per:ℕ}(nm:b+1 ≤ m)(mt:m ≤ t)(nt:b+1<t)
    (s:Fin 3→ℕ)(S:(i:Fin 3)→Emblems R.family (s i))(P:(i:Fin 3)→Sight R.family (s i) per)
    (x:(i:Fin 3)→Palette R.family (s i))(o:Fin 3→Site (R.family.side (b+1) per))(f:Fin 3→Body)
local notation "C"=>R.family
local notation "n"=>b+1
local notation "topN"=>t+1
local notation "E"=>fun _:Fin 3=>(1,false)
local notation "q"=>fun z:ManyStem R.family o (b+1)=>f z.val.1
local notation "roster"=>Stock.census (Fin 3)
local notation "A"=>Mine.tree o E
local notation "J"=>Mine.ward o E roster
local notation "Y"=>R.family.path.rep (t+1) per
local notation "color"=>WilsonAllDateHarvestPhysical.columns o E s q S x m (t+1) (b+1)

def Measured (target:ℝ):Prop:=
  let rows:=imprint R.makes A (headings o E q) (plants (m:=m) s P S x) t t.le_succ
  let real:=gust (C).path topN per topN (birth (J n) (Y topN) color) n (nt.le.trans t.le_succ)
  let gate:=WilsonAllDateHarvestEndpointOpening.opening (WilsonMixedTaggedSeparatedBoard.admitted o E roster nm mt)
    (shadow A s (headings o E q) t)
  let inlet:=fun W=>gate (density (Y t) rows (fun _ _=>0) (fun _ _=>0) W)
  ∃L:∀j,Config G ((C).side j per)→Poly (J j),∃route:Replay A s (le_refl n) t L topN,
    L t=inlet ∧
      (∀j (nj:n ≤ j) (jt:j ≤ t) V, ((Y j).eval V)⁻¹ • L j V=actualTransport C (N:=topN) (fun W=>
        ((Y t).eval W)⁻¹ • WilsonReportHarvestEarlierSlab.route route j nj jt (inlet W)) jt V) ∧
      Integrable (fun W=>baseFold o E roster (L n W)) (prior G ((C).side n per)) ∧
      (∀W,(baseFold o E roster (real W)).part (roster).quiet=(baseFold o E roster (L n W)).part (roster).quiet) ∧
      (∀i W,(baseFold o E roster (real W)).part ((roster).fire i)=(baseFold o E roster (L n W)).part ((roster).fire i)) ∧
      ∀u,(C).ref 0 ≤ u → ∀age:u ≤ b,
        let F:=fun i:Fin 3=>Records.clinic C per topN (s i) (Many.point (S i) (x i) m topN) n (o i) (1,false) (f i)
        let hi:=(age.trans b.le_succ).trans (nt.le.trans t.le_succ)
        let v:=fun i:Fin 3=>-actualTransport C (N:=topN) (F i) hi 1
        ‖actualTransport C (N:=topN) (fun U=>∏i:Fin 3,(F i U-actualTransport C (N:=topN) (F i) hi 1)) hi 1-
          pushTo (C).path topN per (age.trans b.le_succ) (fun W=>score v (baseFold o E roster (L n W))) 1/
            liftVac (C).path topN per u 1‖ ≤ target

theorem original {target:ℝ}(bought:WilsonReportHarvestSlabCenteredSale.Closed R nm mt nt s S P x o f target):
    Measured R nm mt nt s S P x o f target:=by
  obtain ⟨L,route,initial,travel,live,zero,single,price⟩:=bought
  refine ⟨L,route,initial,travel,live,zero,single,?_⟩
  intro u base age field hi v
  have earned:=price u base age
  let lower:=fun W=>baseFold o E roster (L n W)
  have exactSample:=WilsonReportHarvestSlabCenteredPhysical.original (m:=m) C o E s q S x R.makes
    (nt.le.trans t.le_succ) (age.trans b.le_succ) lower live v (1:Config G ((C).side u per))
  have read:WilsonSeparatedOriginalCaptureAtOrigin.clinics o E s q S x m topN=field:=by rfl
  have product:(fun U=>∏i:Fin 3,(v i+WilsonSeparatedOriginalCaptureAtOrigin.clinics o E s q S x m topN i U))=
      fun U=>∏i:Fin 3,(field i U-actualTransport C (N:=topN) (field i) hi 1):=by
    rw [read]
    funext U
    refine Finset.prod_congr rfl (fun i _=>?_ )
    exact (add_comm _ _).trans (sub_eq_add_neg _ _).symm
  rw [product] at exactSample
  exact (congrArg norm exactSample).symm.le.trans earned

end YM.Integration.WilsonReportHarvestSlabCenteredSample
