import YM.Integration.WilsonTrueProjectedPointStock
import YM.Integration.WilsonTrueProjectedLocatedSeedTail

/-! The actual terminal basis coefficients of the inverted point program
have subcritical growth at every cutoff, uniformly in the physical period. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareStock
open Function Filter Finset Lattice Wilson RG Source Labels Trace.Physical
open FormalBulk08 City Pose PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PowerSeries WilsonTrueProjectedPointInverse WilsonTrueProjectedPointProgram WilsonPinnedWidthTransport
open ConnectedActivityE6
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){d D:ℕ}
local notation "ι" => Letter (R.family.labels.level d)
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "clock" => R.family.path.levels.clock
local notation "s" => R.family.S.scale
variable (wood:Primer.Families R.family)(a:hue G)(depth:d<D)
    (simple:G.Simple)(o:Stationary.Loc G 1){U:ℕ→ℕ}
    (formal:WilsonWindowFormalPurchase.Canonical U R.kit)(point:WilsonNeutralPointForecast.Filed R.kit)
    (weakly:WilsonNeutralPointWeakForecast.Filed R.kit)(q:ℕ)

include simple o formal point weakly in
theorem original {δ:ℝ}(margin:0<δ) :
    ∃ C:ℝ,∃ V:ℕ,0<C ∧ ∀ᶠ b:ℕ in atTop,
    ∀ (_:d ≤ (clock).J (b+1))(digit:∀j,Site (R.family.S.block j))(j per:ℕ), b ≤ j →
    ∀ (report:ι→ℂ)(origin:ℝ),0 ≤ origin → (∀l,‖report l‖ ≤ origin) →
    let g:=fun t=>Coat.gStep ((R.family.path.rep (j+1) per t).beta)
    let top:=take R q (lift R wood a depth digit (j+1) b g (fun l=>PowerSeries.C (report l)) ((j+1)-b))
    let X:=income R wood a depth digit (j+1) (j+1) q g top
    (∑l:ι,‖∑k:Fin (q+1),X (j+1) k l‖) ≤ C*(Λ b)^V*origin*Real.exp (δ*(s (j+1)-s b)) := by
  classical
  obtain ⟨C,V,hC,paid⟩:=WilsonTrueProjectedPointStock.original R wood a depth simple o formal point weakly q margin
  refine ⟨((q+1:ℕ):ℝ)*C*2^q,V,by positivity,?_⟩
  filter_upwards [paid] with b active
  intro front digit j per bj report origin hO bounds
  dsimp only
  let N:=j+1
  let g:=fun t=>Coat.gStep ((R.family.path.rep N per t).beta)
  let top:=take R q (lift R wood a depth digit N b g (fun l=>PowerSeries.C (report l)) (N-b))
  let X:=income R wood a depth digit N N q g top
  let K:=C*(Λ b)^V*origin
  have hK:0 ≤ K:=by
    dsimp only [K];exact mul_nonneg (mul_nonneg hC.le (pow_nonneg ((WilsonTrueProjectedPointClock.log_rise R simple (le_refl b)).1.trans' (by norm_num : (0:ℝ)≤1)) V)) hO
  have temp:(1:ℝ)/2 ≤ (R.family.path.rep N per j).beta:=by
    have hat:1 ≤ (clock).hatBeta j:=(R.family.path.levels.fits.delayed j).le
    have band:(clock).hatBeta j/2 ≤ (R.family.path.rep N per j).beta:=(R.makes.wilson.represents N per j (by dsimp [N];omega)).band.1
    linarith only [hat,band]
  have rt:(1:ℝ)/2 ≤ Real.sqrt (R.family.path.rep N per j).beta:=Real.le_sqrt_of_sq_le (by nlinarith only [temp])
  have g0:0 ≤ g j:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have cap:g j ≤ 2:=by
    change (Real.sqrt (R.family.path.rep N per j).beta)⁻¹ ≤ 2
    rw [←one_div,div_le_iff₀ (by linarith only [rt])]
    linarith only [rt]
  have age:s j ≤ s N:=by
    have z:=WilsonTrueProjectedPointClock.elapsed_nonnegative R (show j ≤ N by dsimp [N];omega)
    exact sub_nonneg.mp z
  have ex:Real.exp (δ*elapsed R.family.S b j) ≤ Real.exp (δ*(s N-s b)):=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right age _) margin.le)
  have fees (k:Fin (q+1)): (∑l:ι,‖X N k l‖) ≤ K*Real.exp (δ*(s N-s b))*2^q:=by
    have row:=active front digit N per N j bj (by dsimp [N];omega) le_rfl report origin hO bounds k
    dsimp only at row
    have power:(g j)^k.val ≤ 2^q:=(pow_le_pow_left₀ g0 cap k.val).trans
      (pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.mp k.isLt))
    exact row.trans (mul_le_mul (mul_le_mul_of_nonneg_left ex hK) power (pow_nonneg g0 _)
      (mul_nonneg hK (Real.exp_pos _).le))
  change (∑l:ι,‖∑k:Fin (q+1),X N k l‖) ≤ _
  calc
    _ ≤ ∑l:ι,∑k:Fin (q+1),‖X N k l‖:=sum_le_sum fun l _=>norm_sum_le _ _
    _ = ∑k:Fin (q+1),∑l:ι,‖X N k l‖:=sum_comm
    _ ≤ ∑_k:Fin (q+1),K*Real.exp (δ*(s N-s b))*2^q:=sum_le_sum fun k _=>fees k
    _ = _:=by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul];dsimp only [K,N];ring

end YM.Integration.WilsonOriginalNullBareStock
