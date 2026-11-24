import YM.Integration.FVA1Physical.Wilson.DistributedIdentity

/-! An absolute, support-weighted bound for the normalized coefficient
*before evaluation*. Its rows include every arrangement of the remaining
joint-coordinate derivatives and the entire independent conditional vacuum. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Duel MSbar.Bout MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling
open PhysicalNext.Repeat.Legato Push.Uniform Pressure RGComparison.Core16 Next.SectorChange
open scoped Classical Topology
variable {G:Gauge}

def fullCov (A:Mosaic.Issue G) : Matrix (Joint A.F G) (Joint A.F G) ℝ :=
  let P:=Rolling.straight A.F G
  P * (mold A.pre A.F A.v)⁻¹ * P.transpose

def normalizedRows (A:Mosaic.Issue G) (χ:ChartRatio G) (src:PowerSeries (Pot (Joint A.F G))) (p:ℕ) :=
  growP (barbed A.F A.v χ A.T) src (fullCov A) (p+1)

theorem normalizedRows_read (A:Mosaic.Issue G) (χ:ChartRatio G) (src:PowerSeries (Pot (Joint A.F G)))
    (p i:ℕ) (z:Positions (Primary A.c G)) :
    PowerSeries.coeff i (bulkColumn A χ z src p)=
    MvPolynomial.eval (bulkPoint A z) (PowerSeries.coeff i (normalizedRows A χ src p)) := by
  exact PowerSeries.coeff_map .. 

/-- A local source through order p needs the unmarked action through the
auxiliary tag degree 2p+1. The upper bound is independent of the number of
coordinates. The same denominator is used in every row. -/
theorem normalized_jet {σ:Type} [Fintype σ] [DecidableEq σ] {f:Side} {l:σ→Site f} (b:Site f)
    (p m h s:ℕ) {α C v:ℝ} {K:Matrix σ σ ℝ} (hα:0≤α) (loop:LoopNet l α s K C)
    (Q src:PowerSeries (Pot σ)) (kind:Kind Q)
    (profile:Expanse Q m (p+1+p))
    (act:∀ i ≤ p+1+p, Tokew l α s (h+2*Whisk.ribbon m (p+1+p)) 0 (PowerSeries.coeff i Q) v)
    (input:∀ i ≤ p+1+p, Vault l {b} α s (h+2*Whisk.ribbon m (p+1+p)+1) 0 (PowerSeries.coeff i src) v ∧
      (PowerSeries.coeff i src).totalDegree ≤ m)
    {i:ℕ} (hi:i≤p) :
    Vault l {b} α s h 0 (PowerSeries.coeff i (growP Q src K (p+1)))
      (driver m (p+1+p) h C (v+v)) := by
  have gain : Gain l b α 0 s K K C 0 := by
    refine ⟨hα,le_rfl,le_rfl,?_,?_,?_⟩
    · simpa only [add_zero] using loop
    · simpa only [add_zero] using loop
    · rw [sub_self]; exact ⟨le_rfl,by intro; simp,by intro; simp⟩
  have shifted : Expanse (Q+PowerSeries.X^(p+1)*src) m (p+1+p) := by
    constructor
    intro j hj
    rw [map_add]
    apply (MvPolynomial.totalDegree_add ..).trans (max_le (profile.profile j hj) ?_)
    rw [PowerSeries.coeff_X_pow_mul']
    split
    · expose_names
      have h1:1≤j:=by omega
      exact (input _ ((Nat.sub_le ..).trans hj)).2.trans
        ((le_mul_of_one_le_right (Nat.zero_le m) h1).trans (by omega))
    · rw [MvPolynomial.totalDegree_zero]; omega
  have both:=Bakery.credential kind gain profile (Nat.succ_pos p) shifted
    (fun j hj=>by simpa only [add_zero] using (input j hj).1)
    (fun j hj=>by simpa only [add_zero] using act j hj) (Nat.add_le_add_left hi (p+1))
  simpa only [add_zero] using both.input

/-- Polynomially many products in a fixed joint row turn an arbitrary
subpower input credit into an arbitrary subpower output credit. The coupling
exponent is selected before the covariance and the individual row. -/
theorem row_exponent (m d h:ℕ) {η:ℝ} (hη:0<η) :
    ∃ δ:ℝ, 0<δ ∧ ∀ C:ℝ, ∀ᶠ y:ℝ in atTop, driver m d h C (y^δ+y^δ) ≤ y^η := by
  let t:=Alto.dyadicGrowthDegree (Whisk.ribbon m d) 1
  let δ:=η/(t+1)
  have pos:0<δ:=div_pos hη (by positivity)
  refine ⟨δ,pos,fun C=>?_⟩
  have idprice : Alto.Tuition (fun x:ℝ=>x) 1:=by simpa only [pow_one] using Alto.Tuition.front 1
  have gate:=Alto.Tuition.down (Alto.river m 1 h d C (fun x=>x+x) (Alto.Tuition.same idprice idprice))
      (Nat.lt_succ_self t)
  have rise:=tendsto_rpow_atTop pos
  filter_upwards [rise.eventually (gate.eventually (gt_mem_nhds zero_lt_one)),eventually_gt_atTop (0:ℝ)] with y bill hy
  have H:driver m d h C (y^δ+y^δ) ≤ (y^δ)^(t+1):=
    by simpa only [one_mul] using
         ((div_le_iff₀ (pow_pos (Real.rpow_pos_of_pos hy δ) (t+1))).mp bill.le)
  have rat:δ*(t+1)=η:=by dsimp only [δ]; field_simp
  apply H.trans_eq
  rw [←Real.rpow_natCast,←Real.rpow_mul hy.le,Nat.cast_add,Nat.cast_one,rat]

end YM.Integration.FVA1Physical.Wilson
