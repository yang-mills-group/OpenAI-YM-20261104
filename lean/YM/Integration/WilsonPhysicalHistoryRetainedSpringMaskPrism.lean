import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskSeat

/-! At each individual signed seat the actual entered clover cancels in the
unmasked comparison. Its honest masked value stays in the physical integral. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson MeasureTheory OPE.Therm
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Comparison.Density Comparison.Density.Render AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open IterationFour IterationFour.Vacuum PhysicalNext.Repeat.Legato WilsonVacuumPreResetLiftedPiece
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side}

def unmaskedSeat (a : PrismA G) (v : Seat n) (U : Config G n) : ℝ :=
  factor*∑'i,(a.cells i).unmasked (v.view U) 0

theorem seat_sums (a : PrismA G) {σ C : ℝ} (hs : 0<σ) (positive : 0<a.grade)
    (bill : Commission a.cells σ C a.grade) (v : Seat n) (U : Config G n) :
    ∑'i,(frame n a Frame.full).dataF i (v.view U) = unmaskedSeat a v U := by
  rcases a with ⟨d,r,hd,P⟩
  have weight (i : ℕ) : recipe 1 Frame.full i=factor := by simp [recipe,Frame.full]
  cases r with
  | zero=>
    let W:=v.view U
    have raw:=NativeBoundedAtomSeries.value_summable P (fun _=>(0:Site n)) hs
        (fun _=>le_rfl) bill.toll.2.1 W
    have pollen : HasSum (fun i=>Render.pollen (0:Site n) (P i) W) 0 := by
      simpa only [Render.pollen] using FundedRankTwoPackets.central P (bill.loan positive)
        (AnalyticBridge.VerifiedReset.petals W 0)
    change (∑'i,recipe 1 Frame.full i*((P i).unmasked W 0-Render.pollen 0 (P i) W))=_
    simp_rw [weight]
    rw [tsum_mul_left,(raw.hasSum.sub pollen).tsum_eq,sub_zero]
    rfl
  | succ r=>
    change (∑'i,recipe 1 Frame.full i*(P i).unmasked (v.view U) 0)=_
    simp_rw [weight]
    rw [tsum_mul_left]
    rfl

/-- Genuine all-field thermal mask price at a fixed enrolled earlier seat,
in the original period, including the rose correction at rank two. -/
theorem spring_mask_prism (R : Run G) (simple : G.Simple) (heat : Poetry R.family.path.levels) (q : ℕ) :
    ∀ᶠ j : ℕ in atTop,∀N,j≤N→∀per (a : PrismA G) (σ C : ℝ),0<σ→0<a.grade→
      Commission a.cells σ C a.grade→∀ (B : BudgetPoint) (v : Seat (R.family.side j per)),
      let θ:=(R.family.path.rep N per j).p.threshold
      let Q:=(FundedCorrectedPeriod.piece (R.family.side j per) B σ C a).packet
      let fee:=(625*(Fintype.card PlaqAxes:ℝ))*R.family.path.levels.clock.forcedAllowance j^q
      let f (U : Config G (R.family.side j per)):=maskedSeat Q θ v U-unmaskedSeat a v U
      Measurable f ∧ (∀U,‖f U‖≤C*(2^(a.rise+2)*2)) ∧
      (∫U,‖f U‖ ∂scene R.family.path N per j)≤C*(2^(a.rise+2)*(1+2*(a.rise+2)+625+σ⁻¹)*2*fee) := by
  filter_upwards [spring_mask_series R simple heat q] with j price N live per a σ C hs pos bill B v θ Q fee f
  let n:=R.family.side j per
  let F:=frame n a Frame.full
  obtain ⟨shape,meas,cap⟩:=seated_prism a B σ C bill (n:=n)
  have charged:=price N live per (a.rise+2) a.cells σ C 2 hs (by norm_num) bill.toll
    v.1 v.2 (0:Site n) F.footprint 625 F.dataF shape meas cap
  have same (U) : f U=(∑'i,masked θ (F.footprint i) (F.dataF i) (v.view U))-
      ∑'i,F.dataF i (v.view U) := by
    dsimp only [f,Q]
    rw [seat_inside,seat_sums a hs pos bill v U]
  have eq:=funext same
  rw [eq]
  simpa only [Seat.view,Pi.sub_def,θ,fee,Nat.cast_add,Nat.cast_ofNat] using charged

end YM.Integration.OriginalMarkedRunAction
