import YM.Integration.WilsonThermometerWeakPanelAxes

/-! The finite small-panel inversion acts on the literal displaced Wilson field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPanelBorn
open Function Filter Lattice Wilson Cells Labels RG Source Extraction Extra.Histories
open RG12 RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank Next.Rank.Price
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerSmallPanelRead WilsonThermometerOwnOffsetTale
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {d k N p:ℕ}
local notation "C" => R.family
local notation "F" => R.family.labels.level d

def arm (r:Emblems C d) (hk:k≤N) (z:Site ((C).side N p)) :
    (C).label d→ₗ[ℂ] (Config G ((C).side N p)→ℂ) :=
  ((C).S.a k:ℂ)^d • (((((C).linearO N p d z).mk' (fun t=>(C).O N p t z)).comp
    ((C).factory d N p).terminal.toLinearMap).comp
    (((LinearMap.proj (R:=ℂ) (φ:=fun i:Letter d=>(C).label (kept i)) (primaryLetter d)).comp
      (finer r hk).toLinearMap).comp (LinearMap.single ℂ (fun i:Letter d=>(C).label (kept i)) (primaryLetter d))))

theorem source (r:Emblems C d) (hk:k≤N) (z:Site ((C).side N p)) (u:(C).label d) :
    arm R r hk z u=WilsonThermometerOwnOffsetNectar.birth R
      (((C).factory d N p).terminal (finer r hk (chunk ( «C» := R.family ) (primaryLetter d) u) (primaryLetter d))) k z:=rfl

theorem cylinder (r:Emblems C d) (hk:k≤N) (z:Site ((C).side N p))
    (b:ℝ) (hb:b≠0) (T:(C).label d≃ₗ[ℂ](C).label d) (v:(C).label d):
    arm R r hk z v=∑ i,(column C d k N p b T.toLinearMap v i)•
      arm R r hk z (WilsonThermometerWeakPanelExchange.refine C (shrink C k N p)⁻¹ b T (Size.axis F i)):=by
  have h:=congrArg (arm R r hk z) (WilsonThermometerWeakPanelExchange.exact (p:=p) C R.makes hk b hb T v)
  simpa only [map_sum,map_smul] using h

theorem root (r:Emblems C d) (hk:k≤N) (z:Site ((C).side N p)) (m:ℕ) (hm:m≤N)
    (b:ℝ) (hb:1≤b) (monitor:1≤(C).path.levels.clock.monitor k)
    (T:(C).label d≃ₗ[ℂ](C).label d) (forward:∀u,(F).coeffSize (T u)≤2*(F).coeffSize u)
    (v:(C).label d) (q:ℝ) (hq:0≤q):
    let S:=center (C).S p hm 0
    let X:=fun i=>arm R r hk z (WilsonThermometerWeakPanelExchange.refine C (shrink C k N p)⁻¹ b T (Size.axis F i))
    (∀ i,Interior (S.chamber 0) (X i) ∧ S.rootTest ((C).beta N p) (X i)≤q) →
    Interior (S.chamber 0) (arm R r hk z v) ∧
    S.rootTest ((C).beta N p) (arm R r hk z v)≤q*((2*scaleCost C d)*(F).coeffSize v):=by
  intro S X check
  let c:=column C d k N p b T.toLinearMap v
  obtain ⟨inside,price⟩:=Next.UVStress.root_sum S ((C).beta N p) Finset.univ X c (fun i _=>(check i).1) (seamless R.makes N p)
  rw [cylinder R r hk z b (lt_of_lt_of_le zero_lt_one hb).ne' T v]
  refine ⟨inside,price.trans ?_⟩
  calc (∑ i,‖c i‖*S.rootTest ((C).beta N p) (X i))≤∑ i,‖c i‖*q:=
        Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (check i).2 (norm_nonneg _)
       _=q*(F).coeffSize c:=by rw [←Finset.sum_mul,mul_comm];rfl
       _≤_:=mul_le_mul_of_nonneg_left (WilsonThermometerWeakPanelExchange.priced C R.makes hk monitor b hb T forward v) hq

end YM.Integration.WilsonThermometerWeakPanelBorn
end
