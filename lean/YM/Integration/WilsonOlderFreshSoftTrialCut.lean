import YM.Integration.WilsonOlderFreshSoftTrialCharge
import YM.Integration.WilsonOlderFreshSoftFigureOptics
import YM.Integration.WilsonOlderFreshSoftTrialOpening
import YM.Integration.WilsonOlderFreshSoftCoverScalar

/-! The two measured soft hearings of each funded, unsuspended proper trial face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftTrialCut
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

def source (D d:ι→ℕ)(N K c:ℕ)(L:Levels G)(O:ChartRatio G)(κ:(i:ι)→Knob (D i))(pt:ι→Chamber)
    (cells:Digits L ι)(y:ι → Cover)(T:Finset ι)(f:Pen D T→L[ℝ] ℝ):=
  fun b=>upper R D d κ pt b L O N cells c K y T f

def difference (d:ι→ℕ)(N c w v:ℕ)(L:Levels G)(O:ChartRatio G)(T:Finset ι)
    (P:((i:ι)→(R.family.labels.level (d i)).Index)→Era G ℝ)
    (g:ℝ)(x:∀i,(R.family.labels.level (d i)).Coeff)(q:ℕ)(t:ℝ):ℂ:=
  let h:=mass d T
  let H:=fun b=>cruises L O N h c w (P b)
  reading R d g x (fun b=>cruises L O N h c v (P b)) q t-
    reading R d g x (fun b=>cruises L O N h w v (scalarOnly (H b))) q t

theorem absorbed (β s M E τ ρ B charge weights ratio:ℝ)(x:ℂ)
    (β0:0<β)(s0:0 ≤ s)(gauge:Real.log (Real.sqrt β)= s)
    (M0:0≤M)(price:0≤charge)(r0:0≤ratio)
    (balance:charge*weights≤M*Real.exp (E*s))
    (localFee:‖x‖≤weights*((Real.sqrt β)^τ*ratio^((4:ℝ)⁻¹)))
    (clip:ratio≤Real.exp (-B*s))(length:E+τ+ρ≤B/4):
    charge*‖x‖≤M*Real.exp (-ρ*s):=by
  have root0:=Real.sqrt_pos.mpr β0
  have rest:ratio^((4:ℝ)⁻¹)≤Real.exp ((-B*s)*(4:ℝ)⁻¹):=by
    rw [Real.exp_mul];exact Real.rpow_le_rpow r0 clip (by norm_num)
  have heat:(Real.sqrt β)^τ=Real.exp (s*τ):=by rw [Real.rpow_def_of_pos root0,gauge]
  have non:0≤(Real.sqrt β)^τ*ratio^((4:ℝ)⁻¹):=mul_nonneg (Real.rpow_nonneg root0.le _) (Real.rpow_nonneg r0 _)
  calc
    _ ≤ charge*(weights*((Real.sqrt β)^τ*ratio^((4:ℝ)⁻¹))):=mul_le_mul_of_nonneg_left localFee price
    _ ≤ M*Real.exp (E*s)*((Real.sqrt β)^τ*ratio^((4:ℝ)⁻¹)):=by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right balance non
    _ ≤ M*Real.exp (E*s)*(Real.exp (s*τ)*Real.exp ((-B*s)*(4:ℝ)⁻¹)):=by rw [heat];gcongr
    _ ≤ _:=by rw [mul_assoc,←Real.exp_add,←Real.exp_add];apply mul_le_mul_of_nonneg_left _ M0
              apply Real.exp_le_exp.mpr
              nlinarith only [mul_nonneg (sub_nonneg.mpr length) s0]

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (d:Fin 3→ℕ)(child:ι→Fin 3)(D:ι→ℕ)(e:ℕ)(T:Finset ι)(hs:T.Nonempty)
    (A τ:ℝ)(a0:0≤A)(τ0:0<τ):
    ∃start:ℕ,∀(v:ℕ)(j:Fin 3→ℕ),start≤v → (∀a,start≤j a) →
    (∀a,(R.family.path.levels.budget (j a)).supportExponent≤100) →
    ∀(S:Realm G (e+1) Credit.leanC),S.anchor≤v → S.draws=R.family.path.levels →
      S.y=zz R.family.path.levels → Dormitory S (mass (d ∘ child) T) 0 Credit.leanC →
    ∀(N per K c w target:ℕ),v≤w → w≤c → c≤K → K<N → v+1≤K →
    2≤R.family.path.levels.clock.hatBeta K →
    R.family.S.scale K-R.family.S.scale v≤A*(1+Real.log (R.family.path.levels.clock.hatBeta (v+1))) →
    ∀(η:ℝ)(M:Fin 3→ℝ)(Y:∀a:Fin 3,ℕ×ℕ→R.family.label (d a))
      (before:∀a,j a≤K)(reg:WilsonOriginalMicroscopicGuardedPageSchool.Indexed R d j target η M Y),
      0≤η → (∀a,0≤M a) → ∀(paid m C D₁ D₂:Fin 3→ℝ)(B ρ:ℝ),
    let g:=regulatorRun R.family N per K
    let s:=Real.log g⁻¹
    (∀a,0≤paid a) → (∀a,0≤C a) → (∀a,M a≤C a*Real.exp ((2*m a)*s)) →
    (∀a,Real.log (R.family.S.a K/R.family.S.a (j a))⁻¹≤D₁ a*s) →
    (∀a,paid a≤Real.exp ((d a:ℝ)*D₂ a*s)) →
    R.family.S.a c/R.family.S.a w≤Real.exp (-B*s) → power R d child m η D₁ D₂+τ+ρ≤B/4 →
    ∀(κ:(i:ι)→Knob (D i))(pt:ι→Chamber)(cells:Digits S.draws ι)(y:ι → Cover)(f:Pen D T→L[ℝ] ℝ),‖f‖≤1 →
    let P:=source R D (d ∘ child) N K c S.draws S.paid κ pt cells y T f
    let x:=fun i=>vector R d j K target η M Y before reg N per (child i)
    ∀q≤e,∀t:ℝ,|t|≤1 →
      (∏i,paid (child i))*‖difference R (d ∘ child) N c w v S.draws S.paid T P g x q t‖≤
        bill R d child C*Real.exp (-ρ*s):=by
  obtain ⟨v₀,vc⟩:=eventually_atTop.mp (WilsonOlderFreshSoftFigureOptics.original R D (d ∘ child) simple e T hs A τ a0 τ0)
  obtain ⟨s₀,sc⟩:=eventually_atTop.mp (WilsonOlderFreshSoftTrialCharge.original (ι:=ι) R simple shop d)
  refine ⟨max v₀ s₀,?_⟩
  intro v j fromV fromJ support S first draw ys dorm N per K c w target vw wc cK KN vK warm window η M Y before reg η0 M0 paid m C D₁ D₂ B ρ
  dsimp only
  intro p0 C0 salary stretch doses clip length κ pt cells y f probe q keep t t1
  let β:=R.family.path.β N per K
  have band:=(R.makes.wilson.represents N per K KN.le).band.1
  change R.family.path.levels.clock.hatBeta K/2≤β at band
  have β1:1≤β:=by linarith only [warm,band]
  have β0:=zero_lt_one.trans_le β1
  have mono:=WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le vK
  have thermal:R.family.path.levels.clock.hatBeta (v+1)/2≤β:=by linarith only [mono,band]
  have lower:=vc v ((le_max_left ..).trans fromV) S first draw ys dorm N K c w vw wc cK KN.le β thermal window κ pt cells y f probe q keep t (regulatorRun R.family N per K) t1
  have bought:=sc s₀ le_rfl j (fun a=>(le_max_right ..).trans (fromJ a)) support K target η M Y before reg N per KN warm η0 M0 child paid m C D₁ D₂ p0 salary stretch doses
  have gauge:Real.log (Real.sqrt β)=Real.log (regulatorRun R.family N per K)⁻¹:=by simp [regulatorRun,β]
  have bs:0≤Real.log (regulatorRun R.family N per K)⁻¹:=gauge ▸ Real.log_nonneg (Real.one_le_sqrt.mpr β1)
  have price:0≤bill R d child C:=by
    apply prod_nonneg;intro i _;apply mul_nonneg _ (C0 _);unfold WilsonOlderFreshSoftTrialSalary.base WilsonOlderFreshSoftTrialSalary.wrap;positivity
  exact absorbed β _ _ _ τ ρ B _ _ _ _ β0 bs gauge price (prod_nonneg fun i _=>p0 _) (div_pos (R.family.S.a_pos c) (R.family.S.a_pos w)).le bought (lower _) clip length

end YM.Integration.WilsonOlderFreshSoftTrialCut
end
