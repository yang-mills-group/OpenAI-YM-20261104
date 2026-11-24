import YM.Integration.WilsonOriginalNullReleasedMaximalCost

noncomputable section
namespace YM.Integration.WilsonOriginalNullReleasedMaximalLimit
open Function Filter Finset RG Lattice Wilson Source Labels Next.Rank Next.Rank.Price Next.Rank.Atlas
open Next.Rank.Station Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open Spec OPE OPE.Orbits RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize WilsonPositionCapTransport
open WilsonMaxwellThermometerMaximalHead WilsonMaxwellThermometerStationHeads
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph ConnectedActivityE6
open WilsonPositionThermometerGradedReading WilsonMaxwellThermometerNominatedOrientation
open WilsonOriginalThermometerPalette WilsonOriginalThermometerMicroscopic WilsonOriginalNullReleasedMaximalCost
open scoped Classical BigOperators Topology
abbrev Faces:=Finset (Fin 3)
variable {G:Gauge}(R:Run G)
local notation "C₀"=>R.family
local notation "road"=>R.family.path.levels

/-- The actual solved row displacement on the same original physical stage. -/
def Solved (A:Group C₀ 6)(q N p:ℕ)(S:Faces)(i:Fin 3)(c:(C₀).label (levels i)):Prop:=
  let d:=levels i
  let k:=A.station.k
  let F:=(C₀).labels.level d
  let raw:=((C₀).factory d N p).terminal.symm (A.station.wheel.atCut (N,p) (index A (grade i)) (vector A S i))
  ∃live:k ≤ N,∃home:Opened C₀ d k p,∃W:Rep G ((C₀).side k p),
    W.p=(road).budget k ∧ W.beta=((C₀).path.rep N p k).beta ∧
    let M:=fitting (C:=C₀) d N p k R.makes home live
    let y:=F.scaled (Coat.gStep W.beta/W.p.threshold) (M raw)
    F.coeffSize (c-y) ≤ matrix R d q*Coat.gStep W.beta^(q+1)*F.coeffSize y

def slots:ℕ:=∑i:Fin 3,Fintype.card ((C₀).labels.level (levels i)).Index

/-- The entire genuinely occupied maximal coefficient table on a fixed proper or full face. -/
def sumError (A:Group C₀ 6)(r:ℝ)(S:Faces)(c:(i:Fin 3)→(C₀).label (levels i)):ℝ:=
  ∑i∈S,error ((C₀).labels.level (levels i)) ((r^(levels i))⁻¹) (c i)
    (ladder C₀ (index A (grade i)) (source C₀ S i))

theorem counted {A:Group C₀ 6}{S:Faces}{r e:ℝ}(ep:0 ≤ e)(c:(i:Fin 3)→(C₀).label (levels i))
    (bought:∀i∈S,∀j:((C₀).labels.level (levels i)).Index,
      ((C₀).labels.level (levels i)).grades j=(levels i,levels i/2)→
      ‖(((r^(levels i))⁻¹:ℝ):ℂ)*c i j-(ladder C₀ (index A (grade i)) (source C₀ S i)) j‖ ≤ e):
    sumError R A r S c ≤ (slots R:ℝ)*e:=by
  calc
    _ ≤ ∑i∈S,(Fintype.card ((C₀).labels.level (levels i)).Index:ℝ)*e :=by
      apply Finset.sum_le_sum
      intro i hi
      unfold error
      calc
        _ ≤ ∑_:((C₀).labels.level (levels i)).Index,e:=Finset.sum_le_sum fun j _=>by
          split
          next h=>exact bought i hi j h
          next _=>exact ep
        _ = _:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ ≤ ∑i:Fin 3,(Fintype.card ((C₀).labels.level (levels i)).Index:ℝ)*e:=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>mul_nonneg (Nat.cast_nonneg _) ep)
    _ = _:=by simp only [slots,Nat.cast_sum,Finset.sum_mul]

variable {f:Extraction.Order} {Y:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy} {T:Table R.family.book}

/-- The three maximal blocks converge in total signed coefficient mass after the physical regulators.
The conclusion is uniform over all original solved columns and every deletion of the three fields. -/
theorem original (simple:G.Simple)(shop:WilsonReportingAbsoluteInletSimultaneous.StationInvoice R)
    (F:Final C₀ f T)(J:ℝ→tower T)(V:Store G)(A:ℝ→Group C₀ 6)
    (book:Book (f:=f) (l:=Y) (H:=H) A J)(lead:Leading F J)(q:ℕ){η:ℝ}(pos:0<η):
    ∀ᶠ r in trail,∀ᶠ z:ℕ×ℕ in f.fuse,
      let Z:=WilsonPositionCorrectedCap.adjusted F J V A r
      ∀S:Faces,∀c:(i:Fin 3)→(C₀).label (levels i),(∀i∈S,Solved R Z q z.1 z.2 S i (c i))→sumError R Z r S c<η:=by
  let Z:=WilsonPositionCorrectedCap.adjusted F J V A
  let fee:=η/(3*((slots R:ℝ)+1))
  have ep:0<fee:=by dsimp [fee];positivity
  have native:=WilsonOriginalNullReleasedMaximalCost.original R (f:=f) (H:=H) simple shop q
  have mixed m:=WilsonPositionCorrectedCap.mixed F J V A book lead
    (fun z:Faces×Fin 3=>grade z.2) (fun z=>source C₀ z.1 z.2) m
  have dates:Tendsto (fun r=>(Z r).station.k) trail atTop:=
    tendsto_atTop.mpr fun m=>(mixed m).mono fun _ h=>h.1
  have late (i:Fin 3):∀ᶠ r in trail,WilsonOriginalNullReleasedMaximalCost.graph R (levels i) q (Z r).station.k<fee:=by
    have down: Tendsto (fun r=>((road).clock.hatBeta (Z r).station.k)^(-(1/4):ℝ)) trail (𝓝 0):=
      ((tendsto_rpow_neg_atTop (by norm_num:(0:ℝ)<1/4)).comp (Station.hat_rate (road) simple)).comp dates
    have ready:Tendsto (fun r=>WilsonOriginalNullReleasedMaximalCost.graph R (levels i) q (Z r).station.k) trail (𝓝 0):=by
      simpa only [WilsonOriginalNullReleasedMaximalCost.graph,mul_zero] using down.const_mul
        ((2:ℝ)^(WilsonOriginalAdjacentMicroscopicPrice.height R (levels i)+1)*matrix R (levels i) q*2*mass R)
    exact ready.eventually_lt_const ep
  filter_upwards [mixed 0,dates.eventually native,eventually_all.mpr late,
    WilsonMaxwellThermometerNominatedOrientation.original R simple F J V A book lead ep] with r filed bought head aim
  let k:=(Z r).station.k
  have checked:=WilsonOriginalThermometerMicroscopic.projected R (f:=f) (H:=H) filed
  have radial:Station.gap (road) (Z r).station.b k=r:=filed.2.2.1
  have rp:0<r:=radial ▸ mul_pos ((C₀).S.a_pos k) (Station.mag_pos (road) (Z r).station.b k)
  have wrap (i:Fin 3):∀ᶠ z:ℕ×ℕ in f.fuse,torus R (levels i) k z.2<fee:=
    (WilsonOriginalNullReleasedPeriod.original R (levels i) k f
      ((2:ℝ)^WilsonOriginalAdjacentMicroscopicPrice.height R (levels i)*((road).clock.hatBeta k)^(1/4:ℝ)*mass R)).eventually_lt_const ep
  have top:∀ᶠ z:ℕ×ℕ in f.fuse,k<z.1:=by
    change f.late (fun N _=>k<N)
    exact Eventually.of_forall fun _=>(f.mesh.cofinal.eventually_gt_atTop k)
  filter_upwards [top,eventually_all.mpr wrap] with z live funds
  intro _ S c sold
  have bill:sumError R (Z r) r S c ≤ (slots R:ℝ)*(3*fee):=by
    apply counted R (by positivity)
    intro i membership j degree
    obtain ⟨_,home,W,tier,beta,gross⟩:=sold i membership
    have actual:=bought (Z r) rfl checked.1 checked.2 z.1 z.2 live W tier beta S i membership home (c i) gross r rp radial j degree
    exact actual.trans (by linarith only [head i,funds i,aim z.1 z.2 live S i])
  apply bill.trans_lt
  have denom:0<(slots R:ℝ)+1:=by positivity
  have eq:((slots R:ℝ)+1)*(3*fee)=η:=by dsimp only [fee];field_simp
  rw [←eq]
  exact mul_lt_mul_of_pos_right (by linarith) (by positivity)

end YM.Integration.WilsonOriginalNullReleasedMaximalLimit
end
