import YM.Integration.WilsonReportHarvestSlabCenteredPush
import YM.Integration.WilsonReportHarvestSlabShiftReceipt

/-! Charge all centered components on the same original held history.
The four grade-zero filed measurements use one retained Wilson action. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabCenteredHeld
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open WilsonReportHarvestSlabLabels WilsonAllDateHarvestPropagation WilsonReportHarvestSlabCenteredPush
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "stock" => Stock.census (Fin 3)

def Balance {b N per:ℕ}(F L:Config G ((C).side (b+1) per)→Poly stock)(goal:ℝ):Prop:=
  ∀v:Fin 3→ℂ,(∀i,‖v i‖≤1) → ∃cost:ℝ,∃X:Coefficient ((C).labels.level 0) ((C).side b per),
    X.Format 0 (C).params ((C).path.rep N per b) ∧
    X.remBound 0 ((C).path.rep N per b) (kappa (C).path b) cost ∧
    ((C).labels.level 0).coeffSize X.x ≤ cost ∧ cost ≤ goal ∧
    ∀u (age:u≤b),WilsonPositionSeparatedProfileStableReturn.read (N:=N) R age X=
      value (C).path N per (age.trans b.le_succ) F L v 1

theorem charged (book:OPE.Package C R.w (mutt (C).path.levels R.Q) R.doors)
    {b N per:ℕ}(top:b≤N)(F L:Config G ((C).side (b+1) per)→Poly stock)
    (full:Integrable F (prior G _))(keep:Integrable L (prior G _))
    (zero:∀W,(F W).part (stock).quiet=(L W).part (stock).quiet)
    (single:∀i W,(F W).part ((stock).fire i)=(L W).part ((stock).fire i))
    {wallet:ℝ}(cash:Balance (N:=N) R F L wallet):
    ∀u,(C).ref 0≤u → ∀age:u≤b,∀c:Fin 3→ℂ,
      ‖value (C).path N per (age.trans b.le_succ) F L c 1‖≤
        (1+2*∑i,‖c i‖)*(1+WilsonPositionSeparatedProfileStableReturn.price)*wallet:=by
  intro u grade age c
  let Q:=fun v:Fin 3→ℂ=>value (C).path N per (age.trans b.le_succ) F L v 1
  let B:=(1+WilsonPositionSeparatedProfileStableReturn.price)*wallet
  have positive:0≤WilsonPositionSeparatedProfileStableReturn.price:=
    div_nonneg WilsonPositionSeparatedProfileStableStep.shrink_pos.le (sub_pos.mpr WilsonPositionSeparatedProfileStableStep.shrink_lt).le
  have one (v:Fin 3→ℂ)(bound:∀i,‖v i‖≤1):‖Q v‖≤B:=by
    obtain ⟨cost,X,form,rem,small,budget,read⟩:=cash v bound
    change ‖value (C).path N per (age.trans b.le_succ) F L v 1‖≤_
    rw [←read u age]
    have forecast:=WilsonPositionSeparatedProfileStableReturn.original R book grade age top X form rem
    have entry:‖X.x 0‖≤((C).labels.level 0).coeffSize X.x:=Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ _)
    calc
      _ ≤ ‖WilsonPositionSeparatedProfileStableReturn.read (N:=N) R age X-X.x 0‖+‖X.x 0‖ := norm_le_norm_sub_add _ _
      _ ≤ WilsonPositionSeparatedProfileStableReturn.price*cost+cost:=add_le_add forecast (entry.trans small)
      _ = (1+WilsonPositionSeparatedProfileStableReturn.price)*cost:=by ring
      _ ≤ B:=mul_le_mul_of_nonneg_left budget (by linarith)
  have paid:=WilsonReportHarvestSlabCenteredPush.charged Q c
    (WilsonReportHarvestSlabCenteredPush.held (C).path N per (age.trans b.le_succ) F L full keep zero single c 1)
    (one 0 (by simp)) (fun i=>one (Pi.single i 1) (fun j=>by by_cases h:j=i <;> simp [h]))
  exact paid.trans_eq (mul_assoc _ _ _).symm

variable {b a t N per:ℕ} (na:b+1≤a)(aturn:a≤t)(nt:b+1<t)(top:t≤N)
    (s:Fin 3→ℕ)(S:(i:Fin 3)→Emblems R.family (s i))(P:(i:Fin 3)→Sight R.family (s i) per)
    (x:(i:Fin 3)→Palette R.family (s i))(o:Fin 3→Site (R.family.side (b+1) per))(E:Fin 3→Motion)
    (q:ManyStem R.family o (b+1)→Body)
local notation "n"=>b+1
local notation "A"=>Mine.tree o E
local notation "J"=>Mine.ward o E stock
local notation "Y"=>R.family.path.rep N per
local notation "color"=>WilsonAllDateHarvestPhysical.columns o E s q S x a N n

def Paid (goal:ℝ):Prop:=
  let rows:=imprint R.makes A (headings o E q) (plants (m:=a) s P S x) t top
  let real:=gust (C).path N per N (birth (J n) (Y N) color) n (nt.le.trans top)
  let gate:=WilsonAllDateHarvestEndpointOpening.opening (WilsonMixedTaggedSeparatedBoard.admitted o E stock na aturn)
    (shadow A s (headings o E q) t)
  let inlet:=fun W=>gate (density (Y t) rows (fun _ _=>0) (fun _ _=>0) W)
  ∃L:∀j,Config G ((C).side j per)→Poly (J j),∃route:Replay A s (le_refl n) t L N,
    L t=inlet ∧
      (∀j (nj:n≤j) (jt:j≤t) V, ((Y j).eval V)⁻¹ • L j V=actualTransport C (N:=N) (fun W=>
        ((Y t).eval W)⁻¹ • WilsonReportHarvestEarlierSlab.route route j nj jt (inlet W)) jt V) ∧
      Integrable (fun W=>baseFold o E stock (L n W)) (prior G ((C).side n per)) ∧
      (∀W,(baseFold o E stock (real W)).part (stock).quiet=(baseFold o E stock (L n W)).part (stock).quiet) ∧
      (∀i W,(baseFold o E stock (real W)).part ((stock).fire i)=(baseFold o E stock (L n W)).part ((stock).fire i)) ∧
      ∀u,(C).ref 0≤u → ∀age:u≤b,∀c:Fin 3→ℂ,
        ‖value (C).path N per (age.trans b.le_succ) (fun W=>baseFold o E stock (real W))
          (fun W=>baseFold o E stock (L n W)) c 1‖≤
            (1+2*∑i,‖c i‖)*(1+WilsonPositionSeparatedProfileStableReturn.price)*goal

theorem original (book:OPE.Package C R.w (mutt (C).path.levels R.Q) R.doors){goal:ℝ}
    (purchased:WilsonReportHarvestSlabShiftReceipt.Captured R na aturn nt top s S P x o E q goal):
    Paid R na aturn nt top s S P x o E q goal:=by
  obtain ⟨L,route,issued,transported,live,zero,single,cash⟩:=purchased
  let F:=fun W=>baseFold o E stock (gust (C).path N per N (birth (J n) (Y N) color) n (nt.le.trans top) W)
  have start:Integrable (birth (J n) (Y N) color) (prior G ((C).side N per)):=
    (hatCont C N per color (fun _=>Records.clinic_cut ..) (show Continuous ((Y N).eval) by
      have eqn : (Y N).eval=_ := (R.makes.wilson.starts N per).2
      rw [eqn];exact bare_cont _) (J n)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have full:Integrable F (prior G ((C).side n per)):=
    feed_live (chamber stock ((A).labelY n)) (fun _=>1) (gust_live (C).path N per _ _ start (nt.le.trans top))
  exact ⟨L,route,issued,transported,live,zero,single,
    charged R book (b.le_succ.trans (nt.le.trans top)) F _ full live zero single cash⟩

end YM.Integration.WilsonReportHarvestSlabCenteredHeld
