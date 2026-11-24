import YM.Integration.WilsonReflectedPublicDoseField
import YM.Integration.WilsonReflectedPublicCommonDose
import YM.Integration.WilsonReflectedPublicOpticalJoint

/-! The common-dose original public roster, including the exact old joint and all proper faces. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicDoseRoster
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {N p k : ℕ} {I : Type} [Fintype I] [DecidableEq I]
local notation "C₀" => R.family

open WilsonThermometerReflectedTrajectory WilsonReflectedPublicOrientedFaces WilsonReflectedPublicCommonDose

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)(D:ℕ):
    ∃t ≥ D+3,∀ᶠ k:ℕ in atTop,∀p N (hk:k ≤ N)(I:Type)[Fintype I][DecidableEq I]
      (d:I → ℕ)(_ :∀i,d i ≤ D)(x:(i:I) → (C₀).label (d i))
      (V:(i:I) → Sight C₀ (d i) p)(u:(i:I) → Emblems C₀ (d i))(est:∀i,Opened C₀ (d i) k p)
      (_:∀i,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) k N p (d i)
        (digits R N p 0) (V i) (u i)) (_ :∀i e,e ≤ d i → (C₀).ref e ≤ N)
      (turn:I → Motion)(o:I → Site ((C₀).side k p))
      (_ :∀i j:I,i≠j → (R.family.path.levels.budget k).B^2 < separation (o i) (o j))
      (names:Census I)(C fee:I → ℝ),
      let y:=fun i=>offer R (x i) (est i) hk
      let χ:=fun i=>WilsonThermometerMarchSource.charge (y i)
      let c:=fun i=>dose (χ i) (C i) (fee i)
      let θ:=fun i=>c i*χ i
      let data:=fun i=>((θ i:ℝ):ℂ) • reduce (y i)
      WilsonThermometerReflectedRoster.filed R d (fun _=>0) turn o data V u names hk t ∧
      ∀ j (hj:j ≤ N) (s:names.Mode) U,
        (WilsonThermometerReflectedRoster.density R d (fun _=>0) turn o data u names hk hj U).part s =
        ((C₀).path.rep N p j).eval U • actualTransport C₀ (N:=N)
          (fun W=>∏ i∈s.val,(c i:ℂ)*(C₀).O N p (displayed R (d i) (x i) (turn i)) (anchorAt R (o i) N) W) hj U:=by
  obtain ⟨t,deep,posts⟩:=WilsonThermometerReflectedRoster.original R simple shop D
  refine ⟨t,deep,?_⟩
  filter_upwards [posts] with k bought p N hk I fi di d eligible x V u est raw refs turn o sep names C fee y χ c θ data
  have room i j (h:i≠j): (R.family.path.levels.budget k).B^2 <
      separation (point R (N:=N) 0 (turn i) (o i) k) (point R (N:=N) 0 (turn j) (o j) k):=by
    rw [WilsonReflectedPublicOpticalJoint.location R hk,WilsonReflectedPublicOpticalJoint.location R hk]
    exact sep i j h
  have size₁ (i:I):RG05Readout.Address.size (data i) ≤ 1:=by
    have scaled:=smaller (χ i) (C i) (fee i) (le_max_left ..)
    rw [size_smul,Complex.norm_real,Real.norm_of_nonneg scaled.2.1]
    exact (mul_le_of_le_one_right scaled.2.1 (WilsonThermometerMarchSource.small _)).trans scaled.2.2.1
  have filed:=bought p N hk I d eligible (fun _=>0) V u raw turn o room names data size₁
  refine ⟨filed,?_⟩
  intro j hj s U
  let f:=WilsonThermometerReflectedRoster.source R d (fun _=>0) turn o data u hk
  let bank:=(C₀).path.rep N p
  have bill:=(filed N hk le_rfl).1
  simp only [WilsonThermometerReflectedRoster.density,gust_base] at bill
  rw [WilsonThermometerReflectedRoster.density,actualTransport_unnormalize C₀ R.makes (le_refl N)]
  have face:=congr_fun (pushpart hj (Accent.birth names (bank N) f) s bill) U
  rw [face]
  have factor (i:I): f i=(c i:ℂ) • ((C₀).O N p (displayed R (d i) (x i) (turn i)) (anchorAt R (o i) N)):=by
    have h:=WilsonReflectedPublicDoseField.arm R d x turn o est hk V u θ raw refs i
    exact h.trans (congrArg (fun scalar:ℂ=>scalar • _) (composed (χ i) (C i) (fee i) (le_max_left ..)))
  have exactField (W): ((Accent.birth names (bank N) f) W).part s=(bank N).eval W •
      (∏ i∈s.val,(c i:ℂ)*(C₀).O N p (displayed R (d i) (x i) (turn i)) (anchorAt R (o i) N) W):=by
    unfold Accent.birth Accent.Mach
    rw [Poly.part_smul,pass_fire,Complex.real_smul]
    congr 1
    exact prod_congr rfl fun i _=>congrFun (factor i) W
  simp_rw [exactField]
  rfl

end YM.Integration.WilsonReflectedPublicDoseRoster
end
