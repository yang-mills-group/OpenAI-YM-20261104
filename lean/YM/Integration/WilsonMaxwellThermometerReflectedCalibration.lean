import YM.Integration.WilsonMaxwellThermometerReflectedScalar
import YM.Integration.WilsonPositionProgramReflectedRead

/-! Two reflected rows on the actual common independent inversion band. The
finite least-residual coefficient is purchased without an assumption on
the first lower variation. The latter is priced on its own signed remainder. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedCalibration
open Filter Function Finset MeasureTheory Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Maxwell
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open Source Source.Drops Labels XSpace XSpace.Normalize XSpace.Cirrus XSpace.Rose XSpace.Structure1
open XSpace.Photo XSpace.Tornado XSpace.Retirement Table.Pairing
open WilsonMaxwellThermometerLowerPointGram (occupied)
open WilsonMaxwellThermometerLowerGramPrice (Index token reassemble)
open WilsonMaxwellThermometerIndependentReflection (panel)
open WilsonMaxwellThermometerReflectedScalar (connected)
open WilsonMaxwellThermometerReflectedFirstPrice (filed)
open WilsonMaxwellThermometerReflectedIncidence (Gram Pair mass site)
open scoped Classical BigOperators Topology
variable {G:Gauge}(a:Axis)(x:E4)

def detector (q:Index G a x→Bool→ℂ):occupied G a x→ₗ[ℂ](Bool→ℂ) where
  toFun:=reassemble a x q
  map_add' z z':=by
    funext s
    change ∑i,((Module.finBasis ℂ (occupied G a x)).equivFun (z+z')) i*q i s=_
    simp only [map_add,Pi.add_apply,add_mul,Finset.sum_add_distrib];rfl
  map_smul' scale z:=by
    funext s
    change ∑i,((Module.finBasis ℂ (occupied G a x)).equivFun (scale • z)) i*q i s=_
    simp only [map_smul,Pi.smul_apply,smul_eq_mul,mul_assoc,←Finset.mul_sum];rfl

theorem solved (q:Index G a x→Bool→ℂ)(y:Bool→ℂ):
    ∃z:occupied G a x,∀z',‖y-reassemble a x q z‖ ≤ ‖y-reassemble a x q z'‖:=by
  let f:=detector a x q
  obtain ⟨v,⟨z,rfl⟩,paid⟩:=f.range.closed_of_finiteDimensional.exists_infDist_eq_dist
    ⟨0,f.range.zero_mem⟩ y
  refine ⟨z,fun z'=>?_⟩
  change ‖y-f z‖ ≤ ‖y-f z'‖
  rw [←dist_eq_norm,←dist_eq_norm,←paid]
  exact Metric.infDist_le_dist_of_mem (Set.mem_range_self z')

variable (R:Run G){D k u e l d:ℕ}(h4:4<l)(h6:6<d)
theorem original (U:XSpace.Run){stage:ℕ}(B:WilsonPositionProgramReporterBand.Band R U stage)
    (W:Initialize G)(V:Normalize.Store G)(hx:0<x a)(b:Sec G 6)
    (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (big:0<D)(rails:Rails 0 k u e)(he:1 ≤ e)(cap:capP (panel (G:=G) h4 h6) ≤ k):
    let Q:=panel (G:=G) h4 h6
    ∃β:Bulb (site x) a,∃φ:Wilt Q,∃H C E:ℝ,∃p:ℕ,
      WilsonPositionProgramReflectedRead.reading Q a φ=mass a x β ∧
      (∫w:Pair,WilsonPositionProgramReflectedRead.reading Q a φ w)=1 ∧
      0 ≤ H ∧ 0<C ∧ 0 ≤ E ∧
      ∀ᶠ t:ℕ in atTop,let m:=B.reporter+t;let M:=U.step (B.index t)
        let cash:=H*(1+(B.index t:ℝ))^p
        ∀N:ℕ,m ≤ N → ∀c∈M.Box,
        let y:=connected R h4 h6 a b big φ m N k-filed a x W V β b M c
        let F:=reassemble a x (Gram a x W V β M c)
        (∀z:occupied G a x,‖token a x z‖ ≤ C*(cash+E+‖y-F z‖)) ∧
        ∃z:occupied G a x,(∀z',‖y-F z‖ ≤ ‖y-F z'‖) ∧ ‖token a x z‖ ≤ 2*C*(cash+E):=by
  intro Q
  obtain ⟨β,C,D,hC,hD,first⟩:=WilsonMaxwellThermometerReflectedFirstPrice.original a x W V hx b
  obtain ⟨φ,w,shape,read,integral⟩:=WilsonPositionProgramReflectedRead.original Q a x β 1
  obtain ⟨H,hH,p,cash⟩:=WilsonMaxwellThermometerReflectedScalar.original R h4 h6 a b U B simple v funded
    big rails he cap φ w shape
  obtain ⟨E,hE,bounded⟩:=WilsonMaxwellThermometerReflectedFirstPrice.bounded a x W V β b
  let C₀:=max D E
  refine ⟨β,φ,H,C,C₀,p,read,integral,hH,hC,hD.trans (le_max_left ..),?_⟩
  have ft:Tendsto (fun t=>U.step (B.index t)) atTop Front:=
    (goesFront (Expense.Stretched.runs U)).comp B.cofinal
  filter_upwards [cash,ft.eventually first,ft.eventually bounded] with t earned inv pub
  intro m M wage N early c live y F
  have hw:0 ≤ wage:=mul_nonneg hH (pow_nonneg (by positivity) _)
  have priced:‖connected R h4 h6 a b big φ m N k‖ ≤ wage:=
    (pi_norm_le_iff_of_nonneg hw).2 (earned N early)
  have pay (z:occupied G a x):‖token a x z‖ ≤ C*(wage+C₀+‖y-F z‖):=by
    have step:=inv c live z (connected R h4 h6 a b big φ m N k) ‖y-F z‖ le_rfl
    exact step.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add priced (le_max_left ..)) le_rfl) hC.le)
  refine ⟨pay,?_⟩
  obtain ⟨z,hz⟩:=solved a x (Gram a x W V β M c) y
  refine ⟨z,hz,?_⟩
  have δ:‖y-F z‖ ≤ wage+C₀:=by
    have charge:=hz 0
    change ‖y-F z‖ ≤ ‖y-(detector a x (Gram a x W V β M c)) 0‖ at charge
    rw [map_zero,sub_zero] at charge
    exact charge.trans ((norm_sub_le ..).trans (add_le_add priced ((pub c live).trans (le_max_right ..))))
  calc
    _ ≤ C*(wage+C₀+‖y-F z‖):=pay z
    _ ≤ C*(wage+C₀+(wage+C₀)):=mul_le_mul_of_nonneg_left (add_le_add le_rfl δ) hC.le
    _ = _:=by ring
end YM.Integration.WilsonMaxwellThermometerReflectedCalibration
