import YM.Integration.WilsonOriginalTwoFlatPublicPanel
/-! Independent public reporting radii on the same original hierarchy.
Use the finest of their actual public stations once for all placements.
The chamber is sized by the outer radius and the clearance by the inner. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicMixedRadius
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare

open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {z:Trace.Terrace.Arch R.family}{lo wid teach}(L:Package R.family wid lo teach)
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta

include L in
omit [DecidableEq I] in
theorem selected {E:Type}[Fintype E][DecidableEq E][Nonempty E](sel:E→I) (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {J u:ℕ}(stop:Stop C 0 J u)(d:I→ℕ)(D T h q:ℕ)(cap:∀i,d i ≤ D)
    {M η:ℝ}(one:1 ≤ M)(ep:0<η):
    ∀ᶠ t in trail,∀(r:ℝ)(ρ:I→ℝ),0<r → (∀i,r ≤ ρ i ∧ ρ i ≤ t) → (∃i,ρ i=r) →
      ∀{k:I→ℕ}
      {stock:∀i,Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T (ρ i))
        (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T (ρ i))^T)}
      {W:∀i,Vane R.family (k i)}{fits:∀i,D ≤ k i}{V:∀i,Spin.change S (d i)}
      (A:∀i,Pair F (stock i) (cap i) (W i) (fits i) (V i) (ρ i)),
      (∀i,(W i).checked order H (k i)) → (∀i,(W i).wheel.r=ρ i) →
      let m:=univ.sup fun i=>max (stock i).j (W i).k
      let j:=WilsonInvariantActionPosition.berth R 5 m
      t ≤ (β j)^h*r → ∃uj:u ≤ j,∀N p:ℕ,∀hN:j<N,∀o:E → Cover,(∀i,‖(C).S.gridPoint j (o i)‖ ≤ M*t) →
      (Pairwise fun i i'=>η*r ≤ ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
      ∀weak:E→Bool,∀v:∀i,S.Field (d (sel i)),
      let Y:=word R (fun i=>d (sel i)) j N p hN.le o (fun i=>((A (sel i)).arm (weak i) (v i)).source (N,p))
      ‖gap R N p u (uj.trans hN.le) Y‖  ≤  (∏i,charge F (A (sel i)) j (weak i) (v i))*((β j)^q)⁻¹:=by
  obtain ⟨floor,paid⟩:=eventually_atTop.mp (WilsonOriginalTwoFlatGridScaling.original R (fun i=>d (sel i)) L simple slow stop
    ((2*T+11)+h) q)
  have geo:=WilsonOriginalTwoFlatPublicGeometry.original F simple bliss slow T (max u floor) u one ep
  obtain ⟨δ,dp,box⟩:=Metric.mem_nhdsWithin_iff.mp geo
  obtain ⟨first,wide⟩:=eventually_atTop.mp ((WilsonOriginalTwoFlatPublicGeometry.clearance
    (R:=R) simple slow ep).and (WilsonAddressedCollarWindow.original R simple slow 5 (η:=1) zero_lt_one))
  have Mpos:0<8*M:=by linarith
  filter_upwards [(gt_mem_nhds dp).filter_mono nhdsWithin_le_nhds,
    (ge_mem_nhds (R.family.S.a_pos first)).filter_mono nhdsWithin_le_nhds,
    (ge_mem_nhds (div_pos (R.family.S.a_pos (u+3)) Mpos)).filter_mono nhdsWithin_le_nhds] with t tiny fine small
  intro r ρ rp span anchor k stock W fits V A checked active m j window
  obtain ⟨i₀,near⟩:=anchor
  obtain ⟨i₁,_,peak⟩:=Finset.exists_mem_eq_sup univ univ_nonempty (fun i=>max (stock i).j (W i).k)
  change m=max (stock i₁).j (W i₁).k at peak
  have org:=box (show ρ i₁ ∈ Metric.ball (0:ℝ) δ ∩ Set.Ioi 0 from ⟨by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (rp.trans_le (span _).1)]
    exact (span _).2.trans_lt tiny,rp.trans_le (span _).1⟩) (A i₁) (checked i₁) (active i₁)
  change _ ≤ WilsonInvariantActionPosition.berth R 5 (max _ _) ∧ _ at org
  rw [←peak] at org
  obtain ⟨late,_,_,tight,price,_,_⟩:=org
  have stationLt(i:I):max (stock i).j (W i).k  ≤ m:=Finset.le_sup (f:=fun i=>max (stock i).j (W i).k) (mem_univ i)
  have W₀:(a (W i₀).k) ≤ r:=((WilsonReflectedPublicBulbBerth.mesh R (W i₀) (checked i₀)).trans (active i₀).le).trans near.le
  have rSmall:r ≤ a first:=((span i₀).1.trans (span i₀).2).trans fine
  have lower:first ≤ (W i₀).k:=by
    by_contra! before
    exact (not_le_of_gt (R.family.S.strictAnti before)) (W₀.trans rSmall)
  have fromNear:(W i₀).k ≤ m:=(le_max_right ..).trans (stationLt _)
  have clear:=wide m (lower.trans fromNear)
  have inside:a m ≤ r:=(R.family.S.strictAnti.antitone fromNear).trans W₀
  have mj:m ≤ j:=clear.2.1.le
  have atStation(i:I)(b:Bool):station F (A i) b ≤ j:=by
    cases b <;> simp only [WilsonReflectedPublicStationFare.station,Bool.false_eq_true,if_false,if_true]
    · exact (le_max_left ..).trans ((stationLt _).trans mj)
    · exact (le_max_right ..).trans ((stationLt _).trans mj)
  have wage:8*M*t ≤ (β j)^((2*T+11)+h)*a j:=by
    have H:0 ≤ β j:=(zero_le_one.trans ((P).fits.delayed j).le)
    calc
      _  ≤  (β j)^h*(8*M*r):=by simpa only [mul_left_comm,mul_assoc] using mul_le_mul_of_nonneg_left window Mpos.le
      _  ≤  (β j)^h*((β j)^(2*T+11)*a j):=mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_left (span i₁).1 Mpos.le).trans price) (pow_nonneg H _)
      _ = _:=by rw [pow_add];ring
  have uj:u ≤ j:=(le_max_left ..).trans late
  refine ⟨uj,?_⟩
  intro N p hN o placed separated weak v
  have tol(i:E):=WilsonOriginalTwoFlatPublicFare.issued F (A (sel i)) (checked (sel i)) (weak i) (v i) (atStation (sel i) _) (p:=p) hN
  apply paid j ((le_max_right ..).trans late) (mul_pos Mpos (rp.trans_le ((span i₀).1.trans (span i₀).2)))
    (by simpa only [mul_comm] using (le_div_iff₀ Mpos).mp small)
    (tight.trans_le (mul_le_mul_of_nonneg_left (span i₁).2 Mpos.le)) wage N p hN o _ _ _ _
    (fun _=>lt_of_lt_of_le zero_lt_one (le_max_left ..)) tol uj
  · intro i
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (placed i) (by norm_num:0 ≤ (8:ℝ))
  · intro i i' distinct
    exact (clear.1.trans (mul_le_mul_of_nonneg_left inside ep.le)).trans (separated distinct)

include L in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {J u:ℕ}(stop:Stop C 0 J u)(d:I→ℕ)(D T h q:ℕ)(cap:∀i,d i ≤ D)
    {M η:ℝ}(one:1 ≤ M)(ep:0<η):
    ∀ᶠ t in trail,∀(r:ℝ)(ρ:I→ℝ),0<r → (∀i,r ≤ ρ i ∧ ρ i ≤ t) → (∃i,ρ i=r) →
      ∀{k:I→ℕ}
      {stock:∀i,Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T (ρ i))
        (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T (ρ i))^T)}
      {W:∀i,Vane R.family (k i)}{fits:∀i,D ≤ k i}{V:∀i,Spin.change S (d i)}
      (A:∀i,Pair F (stock i) (cap i) (W i) (fits i) (V i) (ρ i)),
      (∀i,(W i).checked order H (k i)) → (∀i,(W i).wheel.r=ρ i) →
      let m:=univ.sup fun i=>max (stock i).j (W i).k
      let j:=WilsonInvariantActionPosition.berth R 5 m
      t ≤ (β j)^h*r → ∃uj:u ≤ j,∀N p:ℕ,∀hN:j<N,∀o:I → Cover,(∀i,‖(C).S.gridPoint j (o i)‖ ≤ M*t) →
      (Pairwise fun i i'=>η*r ≤ ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
      ∀weak:I→Bool,∀v:∀i,S.Field (d i),
      let Y:=word R d j N p hN.le o (fun i=>((A i).arm (weak i) (v i)).source (N,p))
      ‖gap R N p u (uj.trans hN.le) Y‖  ≤  (∏i,charge F (A i) j (weak i) (v i))*((β j)^q)⁻¹:=by
  exact selected F L (id:I→I) simple bliss slow stop d D T h q cap one ep

end YM.Integration.WilsonOriginalTwoFlatPublicMixedRadius
end
