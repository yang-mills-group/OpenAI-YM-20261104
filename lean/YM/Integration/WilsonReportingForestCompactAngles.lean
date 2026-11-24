import YM.Integration.WilsonReportingForestCompactRoom
import YM.Integration.WilsonReportingForestAngles
import YM.Integration.WilsonReportingForestTagResidence

/-! The full registered union on one original forest fibre, including the
actual crossing-parent links multiplied on the right by their saved pivots. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingForestPivots
open Filter Finset Set Lattice Wilson Tree RG RG16 MSbar.Heath Precision PertExtension OPE.Therm
open PhysicalNext.Repeat.Legato WilsonPhysicalRegisteredForestAction WilsonPhysicalRegisteredForestCrossing
open WilsonReportingRegisteredAction WilsonPhysicalLocalPlaquetteForest WilsonReportingForestBlocks
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]
local notation "A"=>R.family.path.levels

/-- The angular-reflection cutoff is smaller than the original thermal
cutoff on this same fine date. -/
theorem smaller (simple:G.Simple) : ∀ᶠ m:ℕ in atTop,
    let s:=Real.log ((A).clock.hatBeta (m+1))
    (A).clock.hatCoupling (m+1)*s*Real.sqrt (Real.sqrt s)≤cool (A) (m+1) := by
  have grow:=Real.tendsto_log_atTop.comp ((Next.Rank.Station.hat_rate (A) simple).comp (tendsto_add_atTop_nat 1))
  filter_upwards [grow.eventually_ge_atTop (1:ℝ)] with m large
  let s:=Real.log ((A).clock.hatBeta (m+1))
  have s1:1≤ s:=large
  have t1:1≤Real.sqrt s:=by simpa using Real.sqrt_le_sqrt s1
  have u1:1≤Real.sqrt (Real.sqrt s):=by simpa using Real.sqrt_le_sqrt t1
  have t0:=Real.sqrt_nonneg s
  have u0:=Real.sqrt_nonneg (Real.sqrt s)
  have us:Real.sqrt (Real.sqrt s)≤ s:=by
    nlinarith only [Real.sq_sqrt (zero_le_one.trans s1), Real.sq_sqrt t0,
      mul_nonneg t0 (sub_nonneg.mpr t1),mul_nonneg u0 (sub_nonneg.mpr u1)]
  have square:s^2≤ s^12:=pow_le_pow_right₀ s1 (by decide)
  have hp:0≤(A).clock.hatCoupling (m+1):=by unfold RG.Calendar.hatCoupling;positivity
  change (A).clock.hatCoupling (m+1)*s*Real.sqrt (Real.sqrt s)≤(A).clock.hatCoupling (m+1)*s^12
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left us (zero_le_one.trans s1)).trans (by simpa [sq] using square)) hp

/-- The admitted relative logarithms in the actual change of variables
lie in the rescaled compact room. This is simultaneous over all occupied
parents; the fixed exterior may take any of its original values. -/
theorem compact_angles (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) (d:I→ℕ) : ∀ᶠ m:ℕ in atTop,∀N,m<N→∀per
    (o:I→Site (R.family.side (m+1) per)) (T:Forest ((A).clock.op m per).ratio),
    let B:=incident R T d o
    let E:=moving T B
    let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
    let s:=Real.log ((A).clock.hatBeta (m+1))
    ∀(τ:ℝ), 0≤τ→τ≤(A).clock.hatCoupling (m+1)*s*Real.sqrt (Real.sqrt s)→
    ∀(v:({i:T.Free|i∉E}:Set T.Free)→G.El) (x:↥E→G.Color), ‖g • x‖≤J.r →
      (∀i,restored T B v (Chart.expLinks G (↥E) (g • x))∈House.chilly (tagCells R m per (o i)) τ)→
      ‖x‖≤ s^2/32 := by
  let D (i:I):=depth R (d i)+3
  have cp:0≤J.C:=zero_le_one.trans clear.cost
  filter_upwards [dates R.family simple slow (Finset.univ.sup D) (half_pos clear.dist),tag_residence R d,
    WilsonReportingForestCompactRoom.original R simple slow (Finset.univ.sup D) (2*J.C) (by positivity),
    smaller R simple] with m shapes cells rent cap N live per o T
  dsimp only
  intro τ tp small v x inside hood
  let B:=incident R T d o
  let E:=moving T B
  let L:=((A).clock.op m per).ratio.count.val
  let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
  let s:=Real.log ((A).clock.hatBeta (m+1))
  let u:=(cut T E).symm (Chart.expLinks G (↥E) (g • x)*background T B v,v)
  have b0:0<(A).clock.hatBeta (m+1):=zero_lt_one.trans ((A).fits.delayed _)
  have band:(A).clock.hatBeta (m+1)/2≤R.family.path.β N per (m+1):=(R.makes.wilson.represents N per (m+1) live).band.1
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (by linarith only [b0,band]))
  apply (pi_norm_le_iff_of_nonneg (show 0 ≤ s^2/32 by positivity)).mpr
  intro e
  obtain ⟨i,near⟩:=anchored R T d o e.val (Finset.mem_filter.mp e.property).1
  have hi:=Finset.le_sup (f:=D) (Finset.mem_univ i)
  obtain ⟨period,fee,_⟩:=shapes per (D i) hi
  have chill:T.drape u∈House.chilly (faces R m per (d i) (o i)) τ:=
    fun f hf=>hood i f ((cells per o).1 i hf)
  have atBond:deviation T u e.val=G.lieExp ((g • x) e):=(decoded T B v (Chart.expLinks G (↥E) (g • x))).1 e
  let a:=area (extent (D i) L) L
  have a0:0≤a:=by dsimp [a];unfold area;positivity
  have bound:G.chord (G.lieExp ((g • x) e))≤2*(a*τ):=by
    rw [←atBond]
    by_cases h:internal T e.val
    · rw [deviation,if_pos h]
      have loc:=near e.val rfl
      have b:G.chord (u e.val)≤a*τ:=free T (o i) _ period u tp chill e.val loc.1 loc.2 h
      linarith only [b,mul_nonneg a0 tp]
    · rw [deviation,if_neg h]
      exact pair T (o i) _ period u tp chill e.val (pivot T e.val)
        (pair_of T e.val).symm (fun f hf=>near f (hf.elim (fun z=>z ▸ rfl) (fun z=>z ▸ pair_of T e.val)))
  have half:a*τ≤J.δ/2:=(mul_le_mul_of_nonneg_left (small.trans cap) a0).trans fee
  have log:=clear.near (G.lieExp ((g • x) e)) (by linarith only [bound,half])
  rw [(clear.small _ ((norm_le_pi_norm (g • x) e).trans inside)).1] at log
  have cost:g*‖x e‖≤(2*J.C)*a*τ:=calc
    _=‖(g • x) e‖:=by simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos gp]
    _≤J.C*G.chord (G.lieExp ((g • x) e)):=log.2.2
    _≤J.C*(2*(a*τ)):=mul_le_mul_of_nonneg_left bound cp
    _=(2*J.C)*a*τ:=by ring
  apply le_of_mul_le_mul_left _ gp
  exact cost.trans ((mul_le_mul_of_nonneg_left small (by positivity)).trans (rent N live per (D i) hi))

end YM.Integration.WilsonReportingForestPivots
