import YM.Integration.WilsonPositionProgramNominatedPublicScalar
import YM.Integration.WilsonPositionOriginalDiagnosticCorridor
import YM.WilsonCoeffUV.Emit.ProfileCharge

/-! Use the original measured radius and the actual physical profiles in
reporting-mesh coordinates. Their clearance pays the winding gate. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramOriginalStationRadius
open Filter Function Lattice RG Wilson Precision Cells Extraction MergeProof.East
open Next.Foundations PhysicalNext.Repeat.Legato Next.Rank Next.Rank.East
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Cadenza
open PhysicalNext PhysicalNext.Repeat Trace Trace.Pilot Climb Next.Rank.Price
open WilsonPositionThermometerCapStation WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Layout
open scoped Topology Classical
variable {G:Gauge}{a c:ℕ}{Q:Fin (a+1)→SealR G}

def zoomFactor (R:Run G)(A:Group R.family c):ℝ:= A.station.wheel.r/R.family.S.a A.station.k

theorem radius (R:Run G)(A:Group R.family c):
    zoomFactor R A=Next.Rank.Station.mag R.family.path.levels A.station.b A.station.k:=by
  change (R.family.S.a A.station.k * _) / R.family.S.a A.station.k=_
  exact mul_div_cancel_left₀ _ (R.family.S.a_pos _).ne'

theorem covers (R:Run G)(A:Group R.family c){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
    (checked:A.station.checked f H A.horizon):1≤zoomFactor R A:=by
  rw [radius]
  exact Real.one_le_rpow (Real.one_le_exp (sq_nonneg _)) (by linarith [checked.high.1])

theorem original (R:Run G)(simple:G.Simple){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
    (φ:Wilt Q)(disjoint:∀i j,i≠j → Disjoint (tsupport (φ i).ψ.val) (tsupport (φ j).ψ.val))(δ:ℝ):
    let L:=R.family.path.levels
    ∃Z:ℝ,∃B:Fin (a+1)→ℝ,1 ≤ Z ∧ ∀ᶠ m:ℕ in atTop,∀A:Group R.family c,A.station.k=m →
      A.station.checked f H A.horizon → let ρ:=zoomFactor R A
      ∃eligible:1 ≤ ρ,let filed:=sceneGrow eligible φ
      let budget:=max (Compar L.S (zz L) m m) (Z*ρ)
      (∀i x,(filed i).ψ.val (ρ • x)=ρ⁻¹^4*((φ i).ψ.val x)) ∧
      Bough Q filed 1 budget (fun i=>ρ⁻¹^4 * B i) ∧
      (∀i j,i≠j → ClearDay (filed i) (filed j) (δ*longLog L m+14)):=by
  intro L
  obtain ⟨B,available⟩:=adequateZ Q φ disjoint 1
  obtain ⟨Z,base⟩:=available.exists
  have pZ:=zero_lt_one.trans_le base.pos
  let c:=Z⁻¹
  have hc:0<c:=inv_pos.mpr pZ
  refine ⟨Z,B,base.pos,?_⟩
  filter_upwards [WilsonPositionOriginalDiagnosticCorridor.below L simple 2,
      (toward L simple).eventually_ge_atTop ((|δ|+14)/c)] with m fare late
  intro A station checked ρ
  have scale:longLog L m ^ 2 ≤ ρ:=by
    simpa only [ρ,radius,station,L,WilsonMeasuredAdmission.mast,WilsonAdmissionScale.logarithm,longLog] using fare A.station.b checked.high.1
  have hl:1≤longLog L m:=le_trans (by norm_num : (1:ℝ)≤2) (long_pos L m).le
  have full:1≤ρ:=(one_le_pow₀ hl).trans scale
  refine ⟨full,?_⟩
  intro filed budget
  have baseZ:Z≤budget:=(le_mul_of_one_le_right pZ.le full).trans (le_max_right ..)
  have large:1≤budget:=base.pos.trans baseZ
  have coverage(i j)(h:i≠j):ClearDay (filed i) (filed j) (c*ρ):=clearance (base.seats i j h) full
  have paid:δ*longLog L m+14≤c*ρ:= by
    have room:|δ|+14≤longLog L m*c:=(div_le_iff₀ hc).mp late
    calc
      δ*longLog L m+14 ≤ (|δ|+14)*longLog L m:=by
        nlinarith [mul_le_mul_of_nonneg_right (le_abs_self δ) (zero_le_one.trans hl)]
      _ ≤ (longLog L m*c)*longLog L m:=mul_le_mul_of_nonneg_right room (zero_le_one.trans hl)
      _ = c*(longLog L m^2):=by ring
      _ ≤ c*ρ:=mul_le_mul_of_nonneg_left scale hc.le
  refine ⟨fun i x=>?_,⟨large,fun i=>zoom_charge full _ (base.lanes i),fun i=>?_,?_,fun i j h x hx y hy=>?_⟩,
    fun i j h x hx y hy=>paid.trans (coverage i j h x hx y hy)⟩
  · change (zoom (φ i) ρ).val (ρ • x)=_
    rw [zoom_at,smul_smul,inv_mul_cancel₀ (zero_lt_one.trans_le full).ne',one_smul]
  · exact (mul_le_mul_of_nonneg_right (base.rents i) (zero_le_one.trans full)).trans (le_max_right ..)
  · simpa using large
  · exact ((inv_anti₀ pZ baseZ).trans (le_mul_of_one_le_right hc.le full)).trans (coverage i j h x hx y hy)

end YM.Integration.WilsonPositionProgramOriginalStationRadius
end
