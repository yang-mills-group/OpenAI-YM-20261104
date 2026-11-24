import YM.Integration.WilsonPositionSeparatedProfileLocalIncome

/-! The complete signed reporting experiment at any prescribed perturbative order.
The degree and reporting date precede the authentic later cutoffs and fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileLocalPurchase
open Function Filter Set Finset MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonIncidentRegisteredMass WilsonReportingPlaquetteWindows WilsonPositionSeparatedProfileLocalWave
open RG05Readout RG05Readout.Pulse
open scoped Classical BigOperators Topology
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] (R:Run G)

private theorem exchange {N k:ℕ} (per:ℕ) (live:k≤N) (q a:ℕ) :
    R.family.path.levels.clock.hatBeta k^a * regulatorRun R.family N per k^(q+2*a) ≤
      2^a*regulatorRun R.family N per k^q := by
  let b:=R.family.path.levels.clock.hatBeta k
  let β:=R.family.path.β N per k
  let g:=regulatorRun R.family N per k
  have band:b/2≤β:=(R.makes.wilson.represents N per k live).band.1
  have bp:0<β:=Overlay.beta_positive R.makes.wilson live
  have gp:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have cash:g^2*β=1:=by
    change (Real.sqrt β)⁻¹^2*β=1
    rw [inv_pow,Real.sq_sqrt bp.le,inv_mul_cancel₀ bp.ne']
  have one:g^2*b≤2:=(mul_le_mul_of_nonneg_left (by linarith only [band]:b≤2*β) (sq_nonneg g)).trans_eq (by linarith only [cash])
  calc
    b^a*g^(q+2*a)=(g^2*b)^a*g^q:=by rw [pow_add,pow_mul,mul_pow];ring
    _ ≤ _:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg (sq_nonneg g)
      (zero_le_one.trans (R.family.path.levels.fits.delayed k).le)) one a) (pow_nonneg gp _)

def Accepted {m N per:ℕ} (live:m+1<N) (P:ChartRatio G) (q grade:ℕ) (ρ:ℝ)
    (d:I→ℕ) (t:ℕ) (y:∀i,R.family.label (d i)) (φ:Wave I) (r:ℝ) (ξ:Cloud I)
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (χ:ℂ→L[ℝ]ℝ)
    (H:Config G (R.family.side (m+1) per)→ℝ) (target:ℝ) : Prop :=
  ∃w:Config G (R.family.side m per)→ℝ,Integrable w (scene R.family.path N per m) ∧
    (∫V,w V ∂scene R.family.path N per m)≤target ∧ ∀V,
      |actualAverage R.family (N:=N) (fun U=>H U*χ (WilsonPositionSeparatedProfileReportingPrimary.read R d (m+1) N per t y φ r ξ U)) V-
        ∑z:placements (V:=I) R.family (m+1) per t,
          retained R live P q grade ρ d y z.val T (ink R φ r ξ z.val) χ H V|≤w V

def depth (d:I→ℕ) (s q:ℕ) : ℕ := q+2*(s*(4*Fintype.card I)+reserve R d)

theorem original (stoves:Poetry R.family.path.levels) (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (s q grade:ℕ)
    (ord:depth R d s q+5≤grade) (φ:Wave I) (compact:HasCompactSupport φ.val)
    {ε ρ:ℝ} (ep:0<ε) (pr:0<ρ) (sr:ρ<Chart.small G P) (rv:ρ≤J.r) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) (per t:ℕ),(t:ℝ)≤R.family.path.levels.clock.hatBeta (m+1)^s→
      ∀(y:∀i,R.family.label (d i)) (r:ℝ) (ξ:Cloud I)
      (T:Forest (R.family.path.levels.clock.op m per).ratio) (χ:ℂ→L[ℝ]ℝ)
      (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→
      Accepted R live P (depth R d s q) grade ρ d t y φ r ξ T χ H
        (ε*regulatorRun R.family N per (m+1)^q*(‖χ‖*originalMass R d y)*Real.sqrt (∫U,‖H U‖^2 ∂scene R.family.path N per (m+1))) := by
  let a:=s*(4*Fintype.card I)+reserve R d
  obtain ⟨K,kp,earn⟩:=WilsonPositionSeparatedProfileLocalIncome.original R d φ compact s
  let δ:=ε/(K*2^a)
  have dp:0<δ:=div_pos ep (mul_pos kp (pow_pos (by norm_num) _))
  have pay:δ*K*2^a=ε:=by rw [mul_assoc];exact div_mul_cancel₀ ε (mul_pos kp (pow_pos (by norm_num) _)).ne'
  filter_upwards [WilsonPositionSeparatedProfileLocalWave.original R stoves simple marks fees slow P hp J clear d (depth R d s q) grade ord dp pr sr rv]
    with m bought N live per t width y r ξ T χ H eh gh
  obtain ⟨wi,wbound,full⟩:=bought N live per t y φ r ξ T χ H eh gh
  refine ⟨_,wi,wbound.trans ?_,full⟩
  let g:=regulatorRun R.family N per (m+1)
  let b:=R.family.path.levels.clock.hatBeta (m+1)
  let M:=‖χ‖*originalMass R d y
  let X:=Real.sqrt (∫U,‖H U‖^2 ∂scene R.family.path N per (m+1))
  have gp:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have mp:0≤M:=mul_nonneg (norm_nonneg _) (prod_nonneg fun _ _=>sum_nonneg (fun _ _=>norm_nonneg _))
  have xp:0≤X:=Real.sqrt_nonneg _
  calc
    _ ≤ δ*g^(q+2*a)*(K*b^a*M*X) := mul_le_mul_of_nonneg_left
      (earn (m+1) N per live.le t width y r ξ χ H eh) (mul_nonneg dp.le (pow_nonneg gp _))
    _ = (δ*K*(b^a*g^(q+2*a)))*M*X := by ring
    _ ≤ (δ*K*(2^a*g^q))*M*X := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (exchange R per live.le q a) (mul_nonneg dp.le kp.le)) mp) xp
    _ = _ := by rw [←mul_assoc (δ*K),pay]

end YM.Integration.WilsonPositionSeparatedProfileLocalPurchase
