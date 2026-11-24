import YM.Integration.WilsonRegisteredAxialSquare

/-! A correlated complex physical spectator against the complete old
regular short sum with its original physical positive normalizer. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAxialSpectator
open MeasureTheory Filter Lattice RG Wilson OPE.Therm RG16 PhysicalNext.Repeat.Legato MSbar.Heath
open WilsonReportingForestAngularReflection WilsonInheritedRegisteredField WilsonRegisteredFrozenReading
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

theorem tested (simple:G.Simple) (gate:posted R)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) (a:Lattice.Order) (p base t:ℕ) {ε:ℝ} (he:0<ε):
    ∀ᶠ m:ℕ in atTop,∀ N per (live:m+1 ≤ N) d (_ref:R.family.ref d ≤ m+1)
      (v:R.family.label d) (o:Site (R.family.side (m+1) per)) (H:Config G (R.family.side (m+1) per)→ℂ),
      let k:=m+1
      let μ:=scene R.family.path N per k
      let b:=WilsonDegreeFourInheritedRange.height R p k
      let Z:=packet R.makes live v o
      let L:=R.family.labels.level d
      let F:=previous R live v o b
      let s:=(Real.log (β k))^t
      MemLp H 2 μ →
      Integrable (fun U=>H U*F U) μ ∧
      (∫U,‖H U*F U‖ ∂μ)*s ≤ Real.sqrt (∫U,‖H U‖^2 ∂μ)*(ε*L.coeffSize (L.core Z.x)) ∧
      ‖∫U,H U*F U ∂μ‖*s ≤ Real.sqrt (∫U,‖H U‖^2 ∂μ)*(ε*L.coeffSize (L.core Z.x)):=by
  filter_upwards [WilsonRegisteredAxialSquare.physical R simple gate slow J clear a p base t he] with m paid
  intro N per live d ref v o H k μ b Z L F s hH
  let M:=L.coeffSize (L.core Z.x)
  let f U:=‖F U‖*s
  letI:IsProbabilityMeasure (scene R.family.path N per k):=probability R.makes.wilson live
  have M0:0 ≤ M:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have s0:0 ≤ s:=pow_nonneg (Real.log_nonneg ((A).fits.delayed k).le) t
  have f0 (U):0 ≤ f U:=mul_nonneg (norm_nonneg _) s0
  have gross:=WilsonRegisteredAxialMass.gross R live ref v o b
  have hF:MemLp F 2 μ:=MemLp.of_bound gross.1.aestronglyMeasurable (((A).params k).columns*M) (ae_of_all _ gross.2)
  have hf:MemLp f 2 μ:=MemLp.of_bound ((gross.1.norm.mul_const s).aestronglyMeasurable)
    ((((A).params k).columns*M)*s) (ae_of_all _ fun U=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (f0 U)]
      exact mul_le_mul_of_nonneg_right (gross.2 U) s0)
  have pow2:ENNReal.ofReal (2:ℝ)=2:=by norm_num
  have hH':MemLp (fun U=>‖H U‖) (ENNReal.ofReal (2:ℝ)) μ:=pow2.symm ▸ hH.norm
  have hf':MemLp f (ENNReal.ofReal (2:ℝ)) μ:=pow2.symm ▸ hf
  have cs:=integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hH' hf'
  simp only [Real.rpow_two,←Real.sqrt_eq_rpow,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),abs_of_nonneg (f0 _)] at cs
  have bill:Real.sqrt (∫U,(f U)^2 ∂μ) ≤ ε*M:=
    (Real.sqrt_le_sqrt (paid N per live d ref v o)).trans_eq (Real.sqrt_sq (mul_nonneg he.le M0))
  have priced:(∫U,‖H U*F U‖ ∂μ)*s ≤ Real.sqrt (∫U,‖H U‖^2 ∂μ)*(ε*M):=calc
    _ = (∫U,‖H U‖*f U ∂μ):=by
      rw [←integral_mul_const]
      congr 1;funext U;rw [norm_mul];dsimp only [f];ring
    _ ≤ _:=cs.trans (mul_le_mul_of_nonneg_left bill (Real.sqrt_nonneg _))
  exact ⟨hH.integrable_mul hF,priced,(mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) s0).trans priced⟩

end YM.Integration.WilsonRegisteredAxialSpectator
end
