import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerFrame

/-! The common physical representative has an honest free lower limit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerLimit
open Function Filter Finset Set Lattice Wilson RG Source Cells GapsContact.Seams Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS PhysMS.Frame
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt incidence)
open WilsonPositionProgramPublicWickGram (reading nodes)
open WilsonPhysicalStationGradedLowerPanel (left right frame)
open WilsonMeasuredPublicEntranceNativeLowerMoment (free)
open WilsonMeasuredPublicEntranceNativeLowerLeft (ears coefficients representative)
open WilsonMeasuredPublicEntranceNativeLowerFrame (panel row pivot vote)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (B:Deck G)(e:ℕ)(a:Axis)
local notation "I" => Glyph B e
local notation "D" => Table.Field (Bel R.family.book)

def lower {h:ℕ}(y:Points 2)(v:D h):D e:=
  ∑i:I,(row R B e y v ᵥ* (panel R B e a y)⁻¹) i • pivot R B e a i

theorem original {U J:ℝ→tower S}(lead:Leading F J)(aligned:localCost trail U J){T:Type*}{l:Filter T}
    {r:T→ℝ}(hr:Tendsto r l trail){x:T→Points 2}{y:Points 2}(hx:Tendsto x l (𝓝 y))(hy:y∈conf 2)
    (rank:IsUnit (panel R B e a y).det){h:ℕ}{X:T→S.Field h}{v:D h}
    (hv:Tendsto (fun t=>(J (r t) h).symm (X t)) l (𝓝 v)):
    (∀ᶠ t in l,IsUnit (frame R (U (r t)) B e a (r t • x t)).det) ∧
    Tendsto (fun t=>(J (r t) e).symm (representative R (U (r t)) B e a (r t • x t) (X t))) l
      (𝓝 (lower R B e a y v)):=by
  let M:=panel R B e a y
  let A (t:T):=frame R (U (r t)) B e a (r t • x t)
  obtain ⟨Glim,E⟩:=WilsonMeasuredPublicEntranceNativeLowerFrame.original R F B e a lead aligned hr hx hy hv
  have values:Tendsto (fun t=>(A t).det) l (𝓝 M.det):=continuous_id.matrix_det.continuousAt.tendsto.comp Glim
  have inverse:Tendsto (fun t=>(A t)⁻¹) l (𝓝 M⁻¹):=by
    have atUnit:ContinuousAt Ring.inverse M.det:=by
      simpa only [IsUnit.unit_spec] using NormedRing.inverse_continuousAt rank.unit
    exact (continuousAt_matrix_inv M atUnit).tendsto.comp Glim
  constructor
  · filter_upwards [values.eventually (isOpen_ne.mem_nhds rank.ne_zero)] with t ht
    exact isUnit_iff_ne_zero.mpr ht
  · have cash (i:I):Tendsto (fun t=>coefficients R (U (r t)) B e a (r t • x t) (X t) i) l
        (𝓝 ((row R B e y v ᵥ* M⁻¹) i)):=by
      apply tendsto_finsetSum
      intro j _
      exact (tendsto_pi_nhds.mp E j).mul (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp inverse j) i)
    have arms (i:I):Tendsto (fun t=>(J (r t) e).symm (left R (U (r t)) B e a i)) l (𝓝 (pivot R B e a i)):=
      vote R aligned hr tendsto_const_nhds
    simpa only [WilsonMeasuredPublicEntranceNativeLowerLeft.representative,lower,map_sum,map_smul,M] using
      tendsto_finsetSum Finset.univ (fun i _=>(cash i).smul (arms i))

theorem lifted {U J:ℝ→tower S}(lead:Leading F J)(aligned:localCost trail U J){T:Type*}{l:Filter T}
    {r:T→ℝ}(hr:Tendsto r l trail){x:T→Points 2}{y:Points 2}(hx:Tendsto x l (𝓝 y))(hy:y∈conf 2)
    (rank:IsUnit (panel R B e a y).det){h:ℕ}(le:e≤h){X:T→S.Field h}{v:D h}
    (hv:Tendsto (fun t=>(J (r t) h).symm (X t)) l (𝓝 v)):
    Tendsto (fun t=>(J (r t) h).symm (F.sector.derivatives.rise le
        (representative R (U (r t)) B e a (r t • x t) (X t)))) l
      (𝓝 ((Maxwell.Free.scheme R.family.labels).rise le (lower R B e a y v))) :=by
  let W (t:T):=representative R (U (r t)) B e a (r t • x t) (X t)
  let inc:=(Maxwell.Free.scheme R.family.labels).rise le
  have pay:=((original R F B e a lead aligned hr hx hy rank hv).2)
  have accrued:=inc.continuous_of_finiteDimensional.continuousAt.tendsto.comp pay
  refine accrued.congr' ?_
  filter_upwards [hr.eventually (lead.raised le)] with t ht
  apply (J (r t) h).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (ht ((J (r t) e).symm (W t))).trans (by rw [LinearEquiv.apply_symm_apply])

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerLimit
end
