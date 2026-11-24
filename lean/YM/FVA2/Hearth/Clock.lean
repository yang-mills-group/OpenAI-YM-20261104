import YM.FVA2.Hearth.Route
/-!
 # One clock, every order (common top expansion parameter)

 A concrete trajectory in the EXACT conditional hierarchy. The internal coupling
 reset for this prescription can be any in this family. State e.g. ratios
 via `g_top/g_i`; cumulative, not incrementally multiplied during contraction.
 The leading order-1 shift is disallowed, giving a form as in the schematic
 `gᵢ₋₁ = gᵢ (1 + O(gᵢ²))`. No numerical counterterms are required here. Choice of
 these internal coupling ratios **provably has no effect at all** on the final full
 **reclosed** normalized Wilson coefficients at this regulator. But this doesn't mean you may change one
 inside a conditional identity. Use the same Gear at every stamp.
 See `Arrival/Episodes.lean` for the `candle_eq` and `sum_world` proofs, which don't
 require any special choice of Gear. In particular,
 when specializing to choices from a scale planner or estimator from a different theory
 that plan's hypotheses need separate proof. This doesn't construct the critical trajectory
 $g_*=g(g_MS,a)$; it uses top $g_N$ itself before making such conversion. We use that
 conversion in the matching endpoints elsewhere. Nor estimating the distance to any actual
 implementation's reset/readout. No determinant lost by this convention: field coordinate
 change record supplied by lemma `permit_y`; all internal fields and costs in this assembly
 using `log U = g_top * x`, from the very outset, not silently asserting no difference to
 `log U=g_layer * x`; if using another convention, this lemma gives the actual coordinate
 relation to employ (link-exponent expression). See `Hearth/Income.lean` for further
 details of the finite-germ calculation.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade RGComparison.Core16 PowerSeries
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} {c f n:Side} {L:Fabric G n}

 def RootGate {n:Side}(L:Fabric G n) (f:L.Cost→PowerSeries ℝ)(p:PowerSeries ℝ) : Prop:= match L with
 | .endcap _ _=> p=1
 | .layer _ _ _ _ _=> f none=1

structure Gear (L:Fabric G n) where
  speed : L.Cost→PowerSeries ℝ
  terminal : PowerSeries ℝ
  value : ∀ i, constantCoeff (speed i)=1
  tangent : ∀ i, coeff 1 (speed i)=0
  endv : constantCoeff terminal=1
  endt : coeff 1 terminal=0
  focuses : RootGate L speed terminal

-- Provides an actual specialization; point and tuning hypotheses refer instead to the bare fine spacing and are not coded in this example Clock.
 def exampleGear {n:Side}(L:Fabric G n): Gear L:= { speed:=fun _=>1, terminal:=1, value:= fun _=> map_one _, tangent:= fun _=> by simp,
                                                      endv:=map_one _, endt:=by simp,
                                                      focuses:=by cases L<;> rfl }
variable (K:Gear L)
namespace Gear
-- use canonical first-account label names at each height.Option.Clock
 def onAccounts (i:L.Accounts): PowerSeries ℝ:= i.elim 1 K.speed
 def loops (i:L.Accounts): PowerSeries ℝ:= (K.onAccounts i)^2
lemma first : K.loops none=1:= by unfold loops; rw [show onAccounts K none=1 from rfl]; simp
lemma begins (i : L.Accounts): constantCoeff (K.onAccounts i)=1:= i.recOn (map_one _) K.value
lemma pads (i : L.Accounts): coeff 1 (K.onAccounts i)=0:= i.recOn (by rw [show K.onAccounts none=1 from rfl]; simp) K.tangent
lemma priced (i:L.Accounts):0<term (K.loops i) 0:= by unfold term loops; rw [coeff_zero_eq_constantCoeff_apply, map_pow, begins]; positivity
-- The speed of the top layer (if present) is 1.
lemma firstLayer (S:StepData c f) (h:S.patch.Branches S.kernel G) (b:S.Choices) (hf:Even f.val) (L':Fabric G c)(K:Gear (layer S h b hf L')) : K.speed none=1:= K.focuses

 def coupling (i:L.Accounts) := PowerSeries.X * (K.onAccounts i)⁻¹
 def resetFactor (i j:L.Accounts) := K.onAccounts i * (K.onAccounts j)⁻¹
lemma reset (i j:L.Accounts): K.coupling i*K.resetFactor i j=K.coupling j:= by unfold coupling resetFactor; rw [mul_assoc,← mul_assoc ((K.onAccounts i)⁻¹),PowerSeries.inv_mul_cancel _ (fun E=> one_ne_zero ((K.begins i).symm.trans E)),one_mul]

lemma compared_one (i:L.Accounts): Through 1 (K.onAccounts i) 1:= by intro j hj; interval_cases j; exact (coeff_zero_eq_constantCoeff_apply _|>.trans ((K.begins i).trans (by simp))); simp [K.pads]
lemma reset_leading (i j:L.Accounts) : Through 1 (K.resetFactor i j) 1:= by
 unfold resetFactor; nth_rw 1 [← one_mul (1:PowerSeries ℝ)] -- likely rewrites i in compared?
 apply Through.mul (compared_one K i); exact Through.invAlready (compared_one K j) (PowerSeries.mul_inv_cancel _ (fun H=> one_ne_zero ((K.begins j).symm.trans H))) (one_mul _)
lemma boost_out (i:L.Accounts): K.loops i * K.coupling i ^ 2= X^2:= by unfold loops coupling; rw [← mul_pow,mul_left_comm, PowerSeries.mul_inv_cancel _ (fun H=>one_ne_zero ((K.begins i).symm.trans H)),mul_one]

-- real representatives for each request order.N. Keep positivity in germs. Composition for lower-case stencil uses neither scale shift nor additional powers implicitly.
 def setting (i:L.Accounts) (N:ℕ)(t:ℝ) := sheet K.onAccounts N t i
 def sheets (N:ℕ) (i:L.Accounts)(t:ℝ): ℝ := K.setting i N t ^ 2
 def tick (N:ℕ)(t:ℝ)(i:L.Accounts): ℝ:= t/(K.setting i N t)
lemma warm (N:ℕ)(i:L.Accounts) : ContDiffAt ℝ ω (K.sheets N i) 0:= (heated (K.onAccounts) i N).pow 2
lemma borel (N:ℕ)(i:L.Accounts):Measurable (K.sheets N i):= by
 unfold sheets setting sheet peval Zone.eval; exact (Finset.measurable_fun_sum (s:=Finset.range (N+1)) (f:=fun j (t:ℝ)=>t^j * term (K.onAccounts i) j) (fun j _=> (measurable_id.pow_const _).mul_const _)).pow_const 2 -- inspect
lemma charges (N:ℕ)(i:L.Accounts) : Through N (amount (K.sheets N i)) (K.loops i):= by
 let f:= K.setting i N; have hf : ContDiffAt ℝ ∞ f 0:= ((heated K.onAccounts i N).of_le le_top); have he: K.sheets N i=f*f:= funext fun i=> pow_two _
 rw [he,amount,rise_mul hf hf,map_mul]; unfold loops; rw [pow_two]; exact (traced_bare K.onAccounts i N).mul (traced_bare K.onAccounts i N)
lemma onDuty (N:ℕ)(i:L.Accounts): K.setting i N 0=1:= by
 have he:= (traced_bare K.onAccounts i N) 0 (Nat.zero_le _); unfold amount at he; rw [read_rise, jet_zero, coeff_zero_eq_constantCoeff_apply,K.begins i] at he; exact he
lemma near_clock (N:ℕ): ∀ᶠ t:ℝ in 𝓝 0,∀ i:L.Accounts,0<K.setting i N t:= Filter.eventually_all.mpr fun i=> ((heated K.onAccounts i N).continuousAt.eventually (eventually_gt_nhds (show 0<K.setting i N 0 from by rw [onDuty]; exact one_pos)))
lemma zeroSpeed (N:ℕ)(t:ℝ): K.setting none N t=1:= by unfold setting sheet Tested.peval Zone.eval; rw [show K.onAccounts none=1 from rfl]; simp [Tested.term,coeff_one, Finset.sum_ite_eq']
lemma fires (N:ℕ) (t:ℝ): K.tick N t none=t:= by rw [tick,zeroSpeed]; exact div_one _
lemma bill (i:L.Accounts)(N:ℕ)(t:ℝ) : K.sheets N i t / t^2 = ((K.tick N t i)^2)⁻¹ := by
 unfold tick sheets; rw [div_pow]; simp
-- native orbit field rewrite (all Core16 computations use actual link exponent arg). Need reindex y too when comparing theories that exchange coupling mid-step. No asserting their chart formulas unchanged on leaving y fixed if they changed s.
lemma permit_y (i:L.Accounts)(N:ℕ)(t:ℝ)(h:K.setting i N t ≠ 0) {I:Type} (x:I→G.Color) : expLinks G I (t • x)= expLinks G I (K.tick N t i • (K.setting i N t • x)) := by unfold tick; rw [smul_smul,div_mul_cancel₀ _ h]
end Gear
end YM.FVA2.Hearth
