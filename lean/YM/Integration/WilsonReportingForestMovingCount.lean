import YM.Integration.WilsonReportingForestPivots

/-! The number of actual tangent coordinates used by a signed local action.
Count each fine bond by its tail and one of four directions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingForestPivots
open Filter Finset Lattice RG Wilson Tree PhysicalNext.Repeat.Legato RG16
open WilsonReportingRegisteredAction WilsonReportingForestBlocks
open scoped Topology Classical BigOperators
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]

def depthCap (d:I→ℕ) := Finset.univ.sup (fun i=>depth R (d i)+3)

/-- Exact all-date geometric tariff; no assumption on distinct locations. -/
theorem position_count {m per:ℕ} (d:I→ℕ) (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) :
    let L:=(R.family.S.block m).val
    let r:=extent (depthCap R d) L
    (moving T (incident R T d o)).card≤4*Fintype.card I*(r+r+1)^4 := by
  let L:=(R.family.S.block m).val
  let r:=extent (depthCap R d) L
  let P (i:I):Finset (Site (R.family.side (m+1) per)):=(box r).image (fun z=>wrap _ z+o i)
  let Y:=Finset.univ.biUnion P
  let E:=moving T (incident R T d o)
  have present:E.image Subtype.val⊆Y ×ˢ (Finset.univ:Finset Axis):=by
    intro z used
    obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp used
    obtain ⟨i,base⟩:=anchored R T d o e (Finset.mem_filter.mp he).1
    have reach:separation (o i) e.val.1≤r:=by
      have a:=(base e rfl).1
      have b:depth R (d i)+3≤depthCap R d:=Finset.le_sup (f:=fun i=>depth R (d i)+3) (Finset.mem_univ i)
      change separation (o i) e.val.1≤extent (depth R (d i)+3) L at a
      dsimp only [r,extent] at a ⊢
      omega
    refine Finset.mem_product.mpr ⟨Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,?_⟩,Finset.mem_univ _⟩
    exact Finset.mem_image.mpr ⟨_,Work.E08.lift_mem_box reach,by rw [wrap_lift,sub_add_cancel]⟩
  have one_box (i:I):(P i).card≤(r+r+1)^4:=Finset.card_image_le.trans_eq (Corona.box_size r)
  have sites:Y.card≤Fintype.card I*(r+r+1)^4:=calc
    _≤∑i:I,(P i).card:=Finset.card_biUnion_le
    _≤∑_i:I,(r+r+1)^4:=Finset.sum_le_sum (fun i _=>one_box i)
    _=_:=by simp
  have axes:Fintype.card Axis=4:=by decide
  calc
    E.card=(E.image Subtype.val).card:=(Finset.card_image_of_injective _ Subtype.val_injective).symm
    _≤(Y ×ˢ (Finset.univ:Finset Axis)).card:=Finset.card_le_card present
    _=Y.card*4:=by rw [Finset.card_product,Finset.card_univ,axes]
    _≤4*Fintype.card I*(r+r+1)^4:=by nlinarith only [Nat.mul_le_mul_right 4 sites]

def countFee (d:I→ℕ) : ℝ:=4*(Fintype.card I:ℝ)*(2*(depthCap R d:ℝ)+51)^4

/-- The genuine moving coordinate count is polylogarithmic before every
cutoff, period, placement, forest and integration variable. -/
theorem moving_count (simple:G.Simple)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) : ∀ᶠ m:ℕ in atTop,∀per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio),
    ((moving T (incident R T d o)).card:ℝ)≤countFee R d*(Real.log (R.family.path.levels.clock.hatBeta (m+1)))^4 := by
  let A:=R.family.path.levels
  have grows:=(Next.Rank.Station.hat_rate A simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [(Real.tendsto_log_atTop.comp grows).eventually_ge_atTop (1:ℝ)] with m wide per o T
  let L:=(R.family.S.block m).val
  let a:=depthCap R d
  let s:=Real.log (A.clock.hatBeta (m+1))
  change 1 ≤ s at wide
  have lbound:(L:ℝ)≤2+s:=(slow m).trans ((Real.log_le_self (Literal.lambda_pos R.family m).le).trans
    ((Literal.lambda_mono R.family simple).monotone (Nat.le_succ m)))
  have l3:(L:ℝ)≤3*s:=by linarith only [wide,lbound]
  have ascale:(a:ℝ)≤a*s:=by simpa only [mul_one] using mul_le_mul_of_nonneg_left wide (Nat.cast_nonneg a)
  have span:((extent a L+extent a L+1:ℕ):ℝ)≤(2*a+51)*s:=by
    unfold extent
    push_cast
    nlinarith only [l3,ascale,wide]
  let c:ℝ:=4*Fintype.card I
  have non:0≤c:=by dsimp [c];positivity
  have raw:(moving T (incident R T d o)).card≤4*Fintype.card I*(extent a L+extent a L+1)^4:=
    position_count R d o T
  calc
    ((moving T (incident R T d o)).card:ℝ)≤c*((extent a L+extent a L+1:ℕ):ℝ)^4:=by
      dsimp [c]
      exact_mod_cast raw
    _≤c*((2*a+51)*s)^4:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) span 4) non
    _=countFee R d*s^4:=by dsimp [countFee,c,a];ring

/-- Any prescribed fraction of one genuine fine-coupling power pays the
entire changing dimension, uniformly on the original Wilson beta band. -/
theorem moving_slack (simple:G.Simple)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) {δ ε:ℝ} (hd:0<δ) (ep:0<ε) : ∀ᶠ m:ℕ in atTop,∀N,m<N→∀per
    (o:I→Site (R.family.side (m+1) per)) (T:Forest (R.family.path.levels.clock.op m per).ratio),
    ((moving T (incident R T d o)).card:ℝ)*(Pert.Asymptotics.regulatorRun R.family N per (m+1))^δ≤ε := by
  let A:=R.family.path.levels
  let C:=countFee R d
  let h:=δ/2
  let k:ℝ:=2^h
  have cp:0≤C:=by dsimp [C,countFee];positivity
  have hp:0<h:=half_pos hd
  have kp:0<k:=Real.rpow_pos_of_pos two_pos _
  have small:=(isLittleO_log_rpow_rpow_atTop (4:ℝ) hp).def
    (show 0<ε/((C+1)*k) by positivity)
  have grows:=(Next.Rank.Station.hat_rate A simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [moving_count R simple slow d,grows.eventually small] with m count scarce N live per o T
  let b:=A.clock.hatBeta (m+1)
  let β:=R.family.path.β N per (m+1)
  have b1:1<b:=A.fits.delayed _
  have b0:0<b:=zero_lt_one.trans b1
  have band:b/2≤β:=(R.makes.wilson.represents N per (m+1) live).band.1
  have β0:0<β:=by linarith only [b0,band]
  have tiny:(Real.log b)^4≤(ε/((C+1)*k))*b^h:=by
    change ‖(Real.log b)^(4:ℝ)‖≤ε/((C+1)*k)*‖b^h‖ at scarce
    simpa only [Real.rpow_ofNat,Real.norm_of_nonneg (pow_nonneg (Real.log_nonneg b1.le) 4),
      Real.norm_of_nonneg (Real.rpow_nonneg b0.le h)] using scarce
  have converted:b^h≤k*β^h:=by
    rw [show k=(2:ℝ)^h from rfl,←Real.mul_rpow (by norm_num) β0.le]
    exact Real.rpow_le_rpow b0.le (by linarith only [band]) hp.le
  have reset:(Pert.Asymptotics.regulatorRun R.family N per (m+1))^δ=(β^h)⁻¹:=by
    change (Real.sqrt β)⁻¹^δ=(β^h)⁻¹
    rw [Real.inv_rpow (Real.sqrt_nonneg _),Real.sqrt_eq_rpow,←Real.rpow_mul β0.le]
    congr 2
    dsimp [h]
    ring
  have paid:((moving T (incident R T d o)).card:ℝ)≤ε*β^h:=calc
    _≤C*(Real.log b)^4:=count per o T
    _≤(C+1)*(Real.log b)^4:=mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _≤(C+1)*(ε/((C+1)*k)*(k*β^h)):=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact tiny.trans (mul_le_mul_of_nonneg_left converted (by positivity))
    _=ε*β^h:=by field_simp
  rw [reset,←div_eq_mul_inv]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos β0 h)).mpr paid

end YM.Integration.WilsonReportingForestPivots
