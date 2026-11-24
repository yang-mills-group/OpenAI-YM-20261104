import YM.Integration.WilsonPhysicalStationThermalFiledPair

/-! Restore the original lower field's curvature currency after its
signed comparison with the physical detector, retaining a null source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationThermalRefund
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open Next.Rank.Ribbon Table Trace.Pilot Trace PhysicalNext.Repeat.Legato
open WilsonPhysicalStationThermalVotes (votes offered)
open WilsonPhysicalStationThermalPair (cell)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)(B:Binding R.family)(O:HaarBudget G)(J:ChartRatio G)
    {f:Extraction.Order}{S:(Bel R.family.book).Hierarchy}{h D u:ℕ}
    (V:Vane R.family h)(d:Fin (h+1))(checked:V.checked f S h)
    {K:Set (Points 2)}{z bound:ℝ}(P:Tapes.Panel D)
local notation "C"=>R.family
local notation "AX"=>R.family.path.levels

theorem price {P incurred A κ:ℝ} (pos:0<P){r Q:ℕ}(gain:r≤Q)
    (paid:P^(((Q-r:ℕ):ℝ)+κ)*incurred≤A):
    incurred*P^Q ≤ A*P^r*P^(-κ):=by
  have refund:P^(((Q-r:ℕ):ℝ)+κ)*(P^r*P^(-κ))=P^Q:=by
    rw [←Real.rpow_natCast P r,←Real.rpow_add pos,←Real.rpow_add pos,Nat.cast_sub gain,
      show ((Q:ℝ)-r+κ)+(r+-κ)=Q by ring,Real.rpow_natCast]
  calc incurred*P^Q = (P^(((Q-r:ℕ):ℝ)+κ)*incurred)*(P^r*P^(-κ)):=by rw [←refund];ring
       _ ≤ A*(P^r*P^(-κ)):=mul_le_mul_of_nonneg_right paid
        (mul_nonneg (pow_nonneg pos.le _) (Real.rpow_pos_of_pos pos _).le)
       _ = _:=by ring

theorem original (x:R.family.label d)(y:(standard R.family).Field d)(q:Fin 2→ℕ)(rise:q 0≤q 1)
    (ink:WilsonMovingForkReporterNamedInk.Filed B R.makes O J P V u z)
    (bought:WilsonReporterWeightedRankEpoch.Result B R.makes O J (u:=u) (K:=K)
        (d:=fun _:Fin 2=>d.val) (votes R d x y) P q V.k bound z):
    ∀ᶠ N:ℕ in atTop,∀ p:ℕ,∀ fine:V.k<N,∀ a:Points 2,
    tested AX V.b V.k a∈K → FitSky AX V.b V.k a →
    let T:=R.family.path.levels.clock.monitor V.k
    ‖cell R V d (p:=p) checked fine V.k (choose AX V.b V.k a) x y -
          (standard R.family).classMoment (standard R.family) (fun _:Fin 2=>d.val)
            (tested AX V.b V.k a) ![(standard R.family).project d x,y]‖*T^(q 1)
        ≤ bound*T^(q 0)*T^(-(1/(16*(u:ℝ)))):=by
  filter_upwards [WilsonPhysicalStationThermalFiledPair.original R B O J V d checked P x y q ink bought] with N cash
  intro p fine a here fit
  exact price (Real.exp_pos _) rise (cash p fine a here fit)

theorem null (x:R.family.label d)(y:(standard R.family).Field d)(zero:(standard R.family).project d x=0)
    (q:Fin 2→ℕ)(rise:q 0≤q 1)
    (ink:WilsonMovingForkReporterNamedInk.Filed B R.makes O J P V u z)
    (bought:WilsonReporterWeightedRankEpoch.Result B R.makes O J (u:=u) (K:=K)
        (d:=fun _:Fin 2=>d.val) (votes R d x y) P q V.k bound z):
    ∀ᶠ N:ℕ in atTop,∀ p:ℕ,∀ fine:V.k<N,∀ a:Points 2,
    tested AX V.b V.k a∈K → FitSky AX V.b V.k a →
    let T:=R.family.path.levels.clock.monitor V.k
    ‖cell R V d (p:=p) checked fine V.k (choose AX V.b V.k a) x y‖*T^(q 1)
        ≤ bound*T^(q 0)*T^(-(1/(16*(u:ℝ)))):=by
  filter_upwards [original R B O J V d checked P x y q rise ink bought] with N cash
  intro p fine a here fit
  have paid:=cash p fine a here fit
  let M:=(standard R.family).classMoment (standard R.family) (fun _:Fin 2=>d.val) (tested AX V.b V.k a)
  have gone:M ![(standard R.family).project d x,y]=0:=M.map_coord_zero (0:Fin 2) zero
  change ‖_ - M _‖* _ ≤ _ at paid
  rw [gone,sub_zero] at paid
  exact paid

end YM.Integration.WilsonPhysicalStationThermalRefund
end
