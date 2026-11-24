import YM.Integration.WilsonMovingForkStencilProgramme
import YM.Integration.WilsonReceivedChronologicalFixedRoseRange
import YM.Integration.WilsonThermometerUnitFilingRawSum

/-! The same original older-ear fees propagate the complete finite measured portfolio.
All multiplication by measured coordinates takes place outside the normalized Wilson kernel. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkStencilFees
open Function Finset Lattice Wilson RG Trace.Pilot OPE Marker MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open PhysicalNext.Repeat.Legato Pert.Asymptotics WilsonOriginalMixedBlockRows
open WilsonMovingForkStencilProgramme (Programme Basis coefficient piece row)
open WilsonMovingForkPrintedFile (allSlots)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFlatTelescope (numerator feeAt)
open WilsonOriginalJointTrialHearing (fee)
open scoped Classical BigOperators
variable {G:Gauge}{R:Run G}{n N K per:ℕ}{d h:Fin n → ℕ}
  (table:Programme R d K)(κ:(i:Fin n) → Knob (h i))(pt:Fin n → Chamber)
  (w:(i:Fin n) → R.family.label (d i))(ξ:Fin n → Site (R.family.side K per))
  (raw:Basis R d → (i:ℕ) → Config G (R.family.side i per) → Poly (Stock.census (Fin n)))
local notation "α" => coefficient (R:=R) (K:=K) N per w
local notation "M" => row table κ pt N per w ξ
local notation "piece₀" => piece table κ pt N per w ξ
local notation "X" i:max => Config G (R.family.side i per)

def At (i:ℕ):Prop:=∀q:Basis R d,
  numerator R N per i (piece₀ q i)=(fun U=>(raw q i U).part (allSlots n))

theorem registered {i:ℕ}(ik:i < K)
    (group:∀q:Basis R d,∀U,
      let b:=table N per w ξ q i ik
      raw q i U=(((R.family.path.rep N per i).eval U:ℝ):ℂ) •
        WilsonOriginalTwoFlatIRMounted.value b.binder b.load b.copies (regulatorRun R.family N per i) b.wallet U):
    At (N:=N) table κ pt w ξ raw i:=by
  intro q
  funext U
  simp only [numerator,piece,ik,↓reduceDIte,group q U,Poly.part_smul]

theorem deposited {i z:ℕ}(zi:z ≤ i)(held:At (N:=N) table κ pt w ξ raw i)
    (rent:∀q,Integrable (raw q i) (prior G _)):
    Integrable (numerator R N per i (M i)) (prior G _) ∧
      reading R (N:=N) (numerator R N per i (M i)) z zi=
        ∑q:Basis R d,(α q)*reading R (N:=N) (fun U=>(raw q i U).part (allSlots n)) z zi:=by
  have rewrite_row:numerator R N per i (M i)=
      ∑q:Basis R d,α q • (fun U:X i=>(raw q i U).part (allSlots n)):=by
    funext U
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    change ((R.family.path.rep N per i).eval U:ℂ) * (∑q:Basis R d,α q*piece₀ q i U)=_
    rw [mul_sum]
    apply sum_congr rfl
    intro q _
    rw [←congrFun (held q) U]
    unfold numerator
    ring
  rw [rewrite_row]
  exact WilsonThermometerUnitFilingRawSum.family R univ α (fun q U=>(raw q i U).part (allSlots n))
    (fun q=>(Poly.get (allSlots n)).integrable_comp (rent q)) zi

theorem original {i z:ℕ}(zi:z ≤ i)(live:i < N)
    (held:∀j,i ≤ j → j ≤ i+1 → At (N:=N) table κ pt w ξ raw j)
    (rent:∀q j,i ≤ j → j ≤ i+1 → Integrable (raw q j) (prior G _)):
    feeAt R N per z M i=
      ∑q:Basis R d,(α q)*fee R N per (1:X z) (raw q) i (allSlots n):=by
  have lo:=deposited table κ pt w ξ raw zi (held i le_rfl (by omega)) (fun q=>rent q i le_rfl (by omega))
  have hi:=deposited table κ pt w ξ raw (zi.trans (Nat.le_succ i))
    (held (i+1) (by omega) le_rfl) (fun q=>rent q (i+1) (by omega) le_rfl)
  rw [feeAt,dif_pos zi,WilsonThermometerUnitFilingFlatTelescope.edge R N per zi live M lo.1 hi.1,
    hi.2,lo.2,←sum_sub_distrib]
  apply sum_congr rfl
  intro q _
  rw [←mul_sub]
  congr 1
  have diff:=WilsonReceivedChronologicalFixedRoseRange.interval R (raw q) (allSlots n) zi (Nat.le_succ i) live (rent q)
  have single:Ico i (i+1)={i}:=by
    ext j
    simp only [mem_Ico,mem_singleton]
    omega
  simpa only [single,sum_singleton] using diff

end YM.Integration.WilsonMovingForkStencilFees
end
