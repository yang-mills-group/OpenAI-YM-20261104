import YM.Integration.WilsonOlderFreshSoftFigureSize
import YM.Integration.WilsonOlderFreshSoftTrialCut

/-! The complete per-rank zero-moment expenditure at the captured date in measured coupling units. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftTrialSize
open Function Filter Finset Lattice Laurent Bloch Precision Wilson RG Source Labels Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Winding WilsonCoeffUV.Soil WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PertExtension NativeCurvatureTensor
open OriginalMarkedSourceComet WilsonReceivedFixedDigitHistory
open WilsonOlderFreshSoftFigureReading (upper reading)
open WilsonOlderFreshSoftStops (scalarOnly)
open WilsonOlderFreshSoftTrialCharge (power bill wages)
open WilsonOriginalPublicTrialInput (vector)
open scoped Classical BigOperators Topology
variable {G:Gauge}{ι:Type}[Fintype ι][LinearOrder ι](R:Run G)

open WilsonOlderFreshSoftTrialCut (source)
open WilsonOlderFreshSoftFigureSize (gross)
theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (d:Fin 3→ℕ)(child:ι→Fin 3)(D:ι→ℕ)(e:ℕ)(T:Finset ι)(hs:T.Nonempty)
    (A τ:ℝ)(a0:0≤A)(τ0:0<τ):
    ∃start:ℕ,∀(v:ℕ)(j:Fin 3→ℕ),start≤v → (∀a,start≤j a) →
    (∀a,(R.family.path.levels.budget (j a)).supportExponent≤100) →
    ∀(S:Realm G (e+1) Credit.leanC),S.anchor≤v → S.draws=R.family.path.levels →
      S.y=zz R.family.path.levels → Dormitory S (mass (d ∘ child) T) 0 Credit.leanC →
    ∀(N per K c target:ℕ),v≤c → c≤K → K<N → v+1≤K →
    2≤R.family.path.levels.clock.hatBeta K →
    R.family.S.scale K-R.family.S.scale v≤A*(1+Real.log (R.family.path.levels.clock.hatBeta (v+1))) →
    ∀(η:ℝ)(M:Fin 3→ℝ)(Y:∀a:Fin 3,ℕ×ℕ→R.family.label (d a))
      (before:∀a,j a≤K)(reg:WilsonOriginalMicroscopicGuardedPageSchool.Indexed R d j target η M Y),
      0≤η → (∀a,0≤M a) → ∀(paid m C D₁ D₂:Fin 3→ℝ),
    let g:=regulatorRun R.family N per K
    let s:=Real.log g⁻¹
    (∀a,0≤paid a) → (∀a,0≤C a) → (∀a,M a≤C a*Real.exp ((2*m a)*s)) →
    (∀a,Real.log (R.family.S.a K/R.family.S.a (j a))⁻¹≤D₁ a*s) →
    (∀a,paid a≤Real.exp ((d a:ℝ)*D₂ a*s)) →
    ∀(κ:(i:ι)→Knob (D i))(pt:ι→Chamber)(cells:Digits S.draws ι)(y:ι → Cover)(f:Pen D T→L[ℝ] ℝ),‖f‖≤1 →
    let P:=source R D (d ∘ child) N K c S.draws S.paid κ pt cells y T f
    let x:=fun i=>vector R d j K target η M Y before reg N per (child i)
    ∀q≤e,∀r:ℕ,(∀b,Summable (fun z=>‖(P b).2 q r z‖)) ∧
      (∏i,paid (child i))*gross R (d ∘ child) g x P q r≤
        bill R d child C*Real.exp ((power R d child m η D₁ D₂+τ)*s):=by
  obtain ⟨v₀,vc⟩:=eventually_atTop.mp (WilsonOlderFreshSoftFigureSize.original R D (d ∘ child) simple e T hs A τ a0 τ0)
  obtain ⟨s₀,sc⟩:=eventually_atTop.mp (WilsonOlderFreshSoftTrialCharge.original (ι:=ι) R simple shop d)
  refine ⟨max v₀ s₀,?_⟩
  intro v j fromV fromJ support S first draw ys dorm N per K c target vc₀ cK KN vK warm window η M Y before reg η0 M0 paid m C D₁ D₂
  dsimp only
  intro p0 C0 salary stretch doses κ pt cells y f probe q keep r
  let β:=R.family.path.β N per K
  have band:=(R.makes.wilson.represents N per K KN.le).band.1
  change R.family.path.levels.clock.hatBeta K/2≤β at band
  have β1:1≤β:=by linarith only [warm,band]
  have β0:=zero_lt_one.trans_le β1
  have mono:=WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le vK
  have thermal:R.family.path.levels.clock.hatBeta (v+1)/2≤β:=by linarith only [mono,band]
  let g:=regulatorRun R.family N per K
  let s:=Real.log g⁻¹
  let x:=fun i=>vector R d j K target η M Y before reg N per (child i)
  have lower:=vc v ((le_max_left ..).trans fromV) S first draw ys dorm N K c vc₀ cK KN.le β thermal window κ pt cells y f probe q keep r
  have bought:=sc s₀ le_rfl j (fun a=>(le_max_right ..).trans (fromJ a)) support K target η M Y before reg N per KN warm η0 M0 child paid m C D₁ D₂ p0 salary stretch doses
  refine ⟨fun b=>(lower.1 b).2.1,?_⟩
  let weight:=∑b,‖WilsonOriginalPublicTrialFigure.weight R (d ∘ child) g x b‖
  have pos:0≤∏i,paid (child i):=prod_nonneg fun i _=>p0 _
  have non:0≤(Real.sqrt β)^τ:=Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have heat:(Real.sqrt β)^τ=Real.exp (s*τ):=by
    rw [Real.rpow_def_of_pos (Real.sqrt_pos.mpr β0)]
    simp [s,g,regulatorRun,β]
  calc
    _ ≤ (∏i,paid (child i))*(weight*(Real.sqrt β)^τ):=mul_le_mul_of_nonneg_left (lower.2 g x) pos
    _ = ((∏i,paid (child i))*weight)*(Real.sqrt β)^τ:=by ring
    _ ≤ (bill R d child C*Real.exp (power R d child m η D₁ D₂*s))*(Real.sqrt β)^τ:=
      mul_le_mul_of_nonneg_right bought non
    _ = _:=by rw [heat,mul_assoc,←Real.exp_add,add_mul,mul_comm s τ]

end YM.Integration.WilsonOlderFreshSoftTrialSize
end
