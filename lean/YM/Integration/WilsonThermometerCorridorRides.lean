import YM.Integration.WilsonCapturedPrimaryWardRetimed
import YM.Integration.WilsonThermometerOwnOffsetNectar
import YM.Integration.WilsonThermometerWeakMixedAlcove

/- Extend the incumbent fine one-color course into the finite interval before
   it. The exact complete Three on and above the fine date includes its hard
   field. All three colors may use these rides in their common occupied board. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCorridorRides
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout
open RG05Readout.Many Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage
open WilsonThermometerOwnOffsetField WilsonThermometerOwnOffsetTale WilsonThermometerOwnOffsetNectar
open WilsonThermometerOffsetTrajectory
open WilsonThermometerOffsetResidue Trace.Physical OPE
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G){d N p b f:ℕ}{D:Rail R.family}{cash:ℕ→ℕ→ℝ}
  {V:Sight R.family d p}{r:Emblems R.family d}{o:Site (R.family.side N p)}
local notation "C" => R.family

theorem original (paid:Enrolled R.makes D cash f N p d (digits R N p o) V r)
    (nf:f≤N)(bf:b≤f)(awake:Awake D cash b d)(y:Palette (C) d):
    let ν:=WilsonCapturedPrimaryWardRetimed.ratio (C) f b d
    ∃(upper:Sight (C) d p)(register:Emblems (C) d)(initial:Palette (C) d),
      Enrolled R.makes D cash b N p d (digits R N p o) upper register ∧
      size initial ≤ stringCost (C) bf *((C).S.a b/(C).S.a f)^d*size y ∧
      (∀j,f≤j → j≤N →
        ν • state (k:=b) R upper register initial o j = state (k:=f) R V r y o j) ∧
      ∀j (start:b≤j) (live:j<N) (u:ℝ),Cap (d+2) (line (primaryLetter d)) u →
        Ride ((C).path.levels.clock.op j p) (location R o (j+1)) (location R o j)
          (D N p j live) 1
          (ν • state (k:=b) R upper register initial o (j+1))
          (ν • state (k:=b) R upper register initial o j)
          (‖ν‖*charge R register initial start u):=by
  intro ν
  obtain ⟨upper,register,earlier,agrees⟩:=WilsonCapturedPrimaryWardRoute.extend paid nf bf awake
  let initial:Palette (C) d:=(finer register bf).symm y
  refine ⟨upper,register,initial,earlier,WilsonCapturedPrimaryWardRetimed.down earlier (le_refl b) bf nf y,?_,?_⟩
  · intro j fj jN
    have bj:=bf.trans fj
    have chain:finer register bj initial=finer r fj y:=by
      rw [Many.sumwalk register bf fj,LinearEquiv.trans_apply]
      unfold initial
      rw [LinearEquiv.apply_symm_apply,WilsonCapturedPrimaryWardRoute.same fj (fun i fi=>(agrees i fi).1)]
      rfl
    have material:moved R upper register bj jN initial o=moved R V r fj jN y o:=by
      dsimp only [moved,strand]
      rw [(agrees j fj).2]
      congr 3
    unfold state
    rw [dif_pos ⟨bj,jN⟩,dif_pos ⟨fj,jN⟩,material,smul_smul]
    congr 1
    unfold WilsonThermometerOwnOffsetNectar.factor
    calc ν*(((C).S.a b:ℂ)^d*alto (C).path j d)=(((C).S.a b:ℂ)^d*ν)*alto (C).path j d:=by ring
      _=_:=by rw [WilsonCapturedPrimaryWardRetimed.cancel]
  · intro j bj jN u test
    have step:=WilsonThermometerOwnOffsetNectar.paid R earlier awake bj jN initial test
    simpa only [max_self,one_mul,mul_one] using step.matchPay ν ν 1 (by ring)
end YM.Integration.WilsonThermometerCorridorRides
end
