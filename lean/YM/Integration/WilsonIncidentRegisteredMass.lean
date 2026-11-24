import YM.Integration.WilsonIncidentChartTaylorRate
import YM.Integration.WilsonCoherentReportingPivot

/-! Spend the true registered threshold weights before applying the Taylor
error on the physical chart. The surviving factor is the original unscaled
coefficient size of the complete signed roster. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIncidentRegisteredMass
open Function Filter Finset Metric Lattice RG Wilson Tree Precision PertExtension MSbar.Heath
open OPE.Therm RG16 PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonReportingForestPivots
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]

def order (d:ℕ) := univ.sup fun a=>(R.family.labels.level d).grades a |>.2
def reserve (d:I→ℕ) := ∑i,order R (d i)
def originalMass (d:I→ℕ) (y:∀i,R.family.label (d i)) : ℝ :=
  ∏i,(R.family.labels.level (d i)).coeffSize (y i)

theorem threshold {N k:ℕ} (per:ℕ) (live:k≤N) :
    (R.family.path.rep N per k).p.threshold⁻¹≤R.family.path.levels.clock.hatBeta k:=by
  let b:=R.family.path.levels.clock.hatBeta k
  have one:1≤b:=(R.family.path.levels.fits.delayed k).le
  have bp:=zero_lt_one.trans_le one
  have same : (R.family.path.rep N per k).p=R.family.path.levels.budget k := (R.makes.wilson.represents N per k live).vac
  rw [same]
  change ((Real.sqrt b)⁻¹*Real.exp ((Real.log (Real.log b))^2))⁻¹≤b
  have lo:1≤Real.exp ((Real.log (Real.log b))^2):=Real.one_le_exp (sq_nonneg _)
  calc _ ≤ ((Real.sqrt b)⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr (Real.sqrt_pos.mpr bp))
                               (le_mul_of_one_le_right (by positivity) lo)
       _ = _ := inv_inv _
       _ ≤ b := (Real.sqrt_le_left bp.le).mpr (by nlinarith only [mul_nonneg bp.le (sub_nonneg.mpr one)])

theorem scaled (d:I→ℕ) (y:∀i,R.family.label (d i)) {N k:ℕ} (per:ℕ) (live:k≤N) :
    let θ:=(R.family.path.rep N per k).p.threshold
    let b:=R.family.path.levels.clock.hatBeta k
    WilsonCoherentReportingPivot.mass R d θ y≤b^(reserve R d)*originalMass R d y := by
  intro θ b
  rw [WilsonCoherentReportingPivot.counted]
  have b1:1≤b:=(R.family.path.levels.fits.delayed k).le
  have θ0:0≤θ⁻¹:=inv_nonneg.mpr (R.family.path.rep N per k).p.threshold_pos.le
  have term (i:I) : (∑a, ‖(R.family.labels.level (d i)).scaled θ⁻¹ (y i) a‖) ≤
      b^(order R (d i))*(R.family.labels.level (d i)).coeffSize (y i) := by
    unfold Labels.Frame.coeffSize;rw [Finset.mul_sum]
    apply Finset.sum_le_sum;intro a ha
    rw [Labels.Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg θ0 _)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (pow_le_pow_left₀ θ0 (threshold R per live) _).trans
      (pow_le_pow_right₀ b1 (Finset.le_sup (f:=fun a=>((R.family.labels.level (d i)).grades a).2) ha))
  calc _ ≤ ∏ i, (b^(order R (d i))*(R.family.labels.level (d i)).coeffSize (y i)) :=
        Finset.prod_le_prod (fun i _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) (fun i _=>term i)
       _ = _ := by unfold reserve originalMass;rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

theorem purchased (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P)
    (d:I→ℕ) (q:ℕ) (C:ℝ) (c0:0≤C) {ε:ℝ} (he:0<ε) :
    ∀ᶠ j:ℕ in atTop,∀N per, j+1≤N → ∀(y:∀i,R.family.label (d i)) (o:I→Site (R.family.side (j+1) per))
    (T:Forest (R.family.path.levels.clock.op j per).ratio),
    let B:=incident R T d o
    let E:=moving T B
    let θ:=(R.family.path.rep N per (j+1)).p.threshold
    ∀(v:({e:T.Free|e∉E}:Set T.Free)→G.El) (x:↥E→G.Color),x∈ball 0 r →
      restored T B v (Chart.expLinks G (↥E) x)∈cold R j per d o →
      ‖x‖<1 ∧ WilsonCoherentReportingPivot.mass R d θ y * (C*‖x‖^(q+2*reserve R d+1)) ≤
        ε*regulatorRun R.family N per (j+1)^q*originalMass R d y := by
  let H:=reserve R d
  have two:0<(2:ℝ)^H:=by positivity
  filter_upwards [WilsonIncidentChartTaylorRate.purchased R simple slow J clear P pr sr d
    (q+2*H) C c0 (div_pos he two)] with j price N per live y o T B E θ v x hx good
  obtain ⟨admitted,paid⟩:=price N per live o T v x hx good
  refine ⟨admitted,?_⟩
  let b:=R.family.path.levels.clock.hatBeta (j+1)
  let g:=regulatorRun R.family N per (j+1)
  let raw:=originalMass R d y
  have raw0:0≤raw:=Finset.prod_nonneg fun i _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
  have b0:0≤b:=zero_le_one.trans (R.family.path.levels.fits.delayed _).le
  have bp:0<R.family.path.β N per (j+1):=Overlay.beta_positive R.makes.wilson live
  have g0:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have band:b≤2*R.family.path.β N per (j+1):=by
    have h:b/2≤R.family.path.β N per (j+1):=(R.makes.wilson.represents N per (j+1) live).band.1
    linarith only [h]
  have one:(R.family.path.β N per (j+1))*g^2=1:=by
    change _*(Real.sqrt (R.family.path.β N per (j+1)))⁻¹^2=1
    rw [inv_pow,Real.sq_sqrt bp.le,mul_inv_cancel₀ bp.ne']
  have unit:b*g^2≤2:=(mul_le_mul_of_nonneg_right band (sq_nonneg g)).trans_eq (by linarith only [one])
  have cash:b^H*g^(q+2*H)≤2^H*g^q:=by
    calc _=(b*g^2)^H*g^q:=by rw [pow_add,pow_mul,mul_pow];ring
         _≤_:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg b0 (sq_nonneg g)) unit H) (pow_nonneg g0 q)
  calc
    _ ≤ (b^H*raw)*((ε/2^H)*g^(q+2*H)) := mul_le_mul (scaled R d y per live) paid
            (mul_nonneg c0 (pow_nonneg (norm_nonneg _) _)) (mul_nonneg (pow_nonneg b0 _) raw0)
    _ = (raw*(ε/2^H))*(b^H*g^(q+2*H)) := by ring
    _ ≤ (raw*(ε/2^H))*(2^H*g^q) := mul_le_mul_of_nonneg_left cash (mul_nonneg raw0 (div_nonneg he.le two.le))
    _ = _ := by change _=ε*g^q*raw;field_simp

end YM.Integration.WilsonIncidentRegisteredMass
