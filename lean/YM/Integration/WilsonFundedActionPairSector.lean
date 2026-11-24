import YM.Integration.WilsonRegisteredSoftCovariance
import YM.Integration.WilsonInvariantActionDoubleAdmission

/-! The signed Maxwell profile and the two charged regular insertions use
the same two physical cutoff labels, on the original reporting layout. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonFundedActionPairSector
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Climb Table Spec PhysMS
open Lattice Wilson RG RG17 Extraction Next.UVStress Next.Rank.Price
open PhysicalNext.Repeat.Legato Pier.Lair SharpGram.Lenses OPE OPE.Orbits
open Trace.Pilot TraceExtension WilsonLimitConstruction Pert.Asymptotics WilsonInvariantActionPairMarginals
open WilsonInvariantActionIntegratedPair WilsonInheritedRegisteredField
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple) {ρ : ℝ} {T : Campaign R}
    {P : Campaign.Pillars R T} (funded : FundedOriginalProperties.{u} simple ρ P)
    {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S) (L : Layout F)
    {U : Filter (ℕ×ℕ)} [U.NeBot] (chosen : U≤L.lens)
    (J : ℝ→tower S) {H : (Bel R.family.book).Hierarchy} (lead : Leading F J)
    (paid : ∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    {u : Filter (ℕ×ℕ)} (B : Mantle F u) (E : Services R.family f S) (pegs : Pegs B L)
    (near : ∀ᶠr in trail,R.family.S.a (L.level r)≤r ∧
      r≤R.family.S.a (L.level r)*R.family.path.levels.clock.hatBeta (L.level r)^2)
local notation "β" => R.family.path.levels.clock.hatBeta

include simple funded lead paid E pegs near chosen in
theorem original :
    ∃ (e:ℕ) (w:ℝ→RG17.Free R.family 4→R.family.label 4),
      (∀ᶠr in trail,∀v,master L 4 r (w r v)=J r 4 v ∧
        ∀N per,L.level r≤N→quota R.family 4 (L.level r) N per (atRef L 4 r (N,per) (w r v))≤
          R.family.S.a (L.level r)^4*(β (L.level r)^e*‖v‖)) ∧
      (∀ᶠr in trail,∀v (φ:Test 2) (cut:(N p:ℕ)→Fin (N+1)),
        let a:=w r (stepField R.family)
        let b:=w r v
        let central:=S.representative 4 (J r 4 (stepField R.family))
        let exterior:=S.representative 4 (J r 4 v)
        Tendsto (fun z:ℕ×ℕ=>profile R cut (atRef L 4 r z a) (atRef L 4 r z b) φ z.1 z.2-
          profile R cut central exterior φ z.1 z.2) U (𝓝 0)) ∧
      ∀ q:ℕ,∀ε>0,∀ᶠr in trail,0<L.level r ∧
        ∀ v j, j+1=L.level r → ∀ N per (hk:j+1≤N) (x y:Site (R.family.side (j+1) per))
          (η χ : ℂ→L[ℝ]ℝ) (V : Config G (R.family.side j per)),
        let k:=j+1
        let b:=WilsonDegreeFourInheritedRange.height R ((q+2*(e+1))+2*e) k
        let a:=atRef L 4 r (N,per) (w r (stepField R.family))
        let z:=atRef L 4 r (N,per) (w r v)
        let first:=fun W=>η (regular R.makes hk a x W)
        let last:=fun W=>χ (MergeProof.alto R.family.path k 4*WilsonDegreeFourInheritedTail.tail R.makes hk z y b W)
        let read:=actualAverage R.family (N:=N) (p:=per) (m:=j) (E:=ℝ)
        |read (fun W=>(first W-read first V)*last W) V| ≤
          ε*regulatorRun R.family N per k^q*(‖η‖*‖χ‖)*(‖stepField R.family‖*‖v‖) := by
  obtain ⟨e,market⟩:=WilsonReportingMeasuredTender.entry B E
    (WilsonReportingMeasuredAdmission.present F J lead paid) pegs near 4
  let issued (r:ℝ) (v:RG17.Free R.family 4) (z:R.family.label 4) :=
    master L 4 r z=J r 4 v ∧ ∀N per,L.level r≤N→quota R.family 4 (L.level r) N per (atRef L 4 r (N,per) z)≤
      R.family.S.a (L.level r)^4*(β (L.level r)^e*‖v‖)
  let w (r:ℝ) (v:RG17.Free R.family 4) := if h:∃z,issued r v z then h.choose else 0
  have stock : ∀ᶠr in trail,∀v,issued r v (w r v) := by
    filter_upwards [market,pegs.level.growing.eventually_ge_atTop (R.family.ref 4)] with r bought live
    intro v
    obtain ⟨z,cost,name⟩:=bought v
    have ex : ∃z,issued r v z := by
      refine ⟨z,name,fun N p hN=>?_⟩
      rw [WilsonMatrixTicketLanesReportedAdmission.quota R F L 4 r z live N p hN]
      exact mul_le_mul_of_nonneg_left cost (pow_nonneg (R.family.S.a_pos _).le _)
    simpa only [w,dif_pos ex] using ex.choose_spec
  refine ⟨e,w,stock,?_,?_⟩
  · filter_upwards [stock,pegs.level.growing.eventually_ge_atTop (R.family.ref 4)] with r acquired live
    intro v φ cut a b central exterior
    have h:=WilsonInvariantActionDoubleAdmission.measured F L chosen live a b φ cut
    dsimp only at h
    simpa only [a,b,(acquired (stepField R.family)).1,(acquired v).1] using h
  intro q ε positive
  obtain ⟨j₀,late⟩:=eventually_atTop.1 (WilsonRegisteredSoftCovariance.purchased R simple funded e e q positive)
  filter_upwards [stock,pegs.level.growing.eventually_ge_atTop (max (R.family.ref 4) (j₀+1))] with r acquired large
  have older:j₀+1≤L.level r := (le_max_right ..).trans large
  have live:R.family.ref 4≤L.level r := (le_max_left ..).trans large
  refine ⟨by omega,?_⟩
  intro v j date N per hk x y η χ V
  have ca:=((acquired (stepField R.family)).2 N per (date ▸ hk))
  have cb:=((acquired v).2 N per (date ▸ hk))
  rw [←date] at ca cb
  exact late j (by omega) N per hk 4 4 (date ▸ live) (date ▸ live) _ _ x y _ _ (norm_nonneg _) (norm_nonneg _) ca cb η χ V

end YM.Integration.WilsonFundedActionPairSector
end
