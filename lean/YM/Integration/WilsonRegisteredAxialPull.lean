import YM.Integration.WilsonRegisteredAxialSpectator

/-! A spectator may depend jointly on earlier and later fields while the
old short source reads its own genuine physical marginal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAxialPull
open MeasureTheory Filter Lattice RG Wilson OPE.Therm RG16 PhysicalNext.Repeat.Legato MSbar.Heath
open WilsonReportingForestAngularReflection WilsonInheritedRegisteredField WilsonRegisteredFrozenReading
open scoped Classical Topology
universe z
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

theorem purchased (simple:G.Simple) (gate:posted R)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) (a:Lattice.Order) (p base t:ℕ) {ε:ℝ} (he:0<ε):
    ∀ᶠ m:ℕ in atTop,∀ N per (live:m+1 ≤ N) d (_ref:R.family.ref d ≤ m+1)
      (v:R.family.label d) (o:Site (R.family.side (m+1) per))
      {Ω:Type z} [MeasurableSpace Ω] (ν:Measure Ω) (read:Ω → Config G (R.family.side (m+1) per)),
      let k:=m+1
      let μ:=scene R.family.path N per k
      let Z:=packet R.makes live v o
      let L:=R.family.labels.level d
      let b:=WilsonDegreeFourInheritedRange.height R p k
      let F:=previous R live v o b
      MeasurePreserving read ν μ → ∀H:Ω→ℂ,MemLp H 2 ν →
      Integrable (fun w=>H w*F (read w)) ν ∧
      (∫w,‖H w*F (read w)‖ ∂ν)*(Real.log (β k))^t ≤
        Real.sqrt (∫w,‖H w‖^2 ∂ν)*(ε*L.coeffSize (L.core Z.x)):=by
  filter_upwards [WilsonRegisteredAxialSquare.physical R simple gate slow J clear a p base t he] with m paid
  intro N per live d ref v o Ω space ν read k μ Z L b F law H hH
  let s:=(Real.log (β k))^t
  let M:=L.coeffSize (L.core Z.x)
  let f U:=‖F U‖*s
  letI:IsProbabilityMeasure (scene R.family.path N per k):=probability R.makes.wilson live
  have M0:0 ≤ M:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have s0:0 ≤ s:=pow_nonneg (Real.log_nonneg ((A).fits.delayed k).le) t
  have f0 (U):0 ≤ f U:=mul_nonneg (norm_nonneg _) s0
  have gross:=WilsonRegisteredAxialMass.gross R live ref v o b
  have fm:Measurable f:=gross.1.norm.mul_const s
  have id:(∫w,(f (read w))^2 ∂ν)=∫U,(f U)^2 ∂μ:=by
    rw [←law.map_eq,integral_map law.measurable.aemeasurable (fm.pow_const 2).aestronglyMeasurable]
  have square:Real.sqrt (∫w,(f (read w))^2 ∂ν) ≤ ε*M:=by
    rw [id];exact (Real.sqrt_le_sqrt (paid N per live d ref v o)).trans_eq (Real.sqrt_sq (mul_nonneg he.le M0))
  have f2:MemLp f 2 μ:=MemLp.of_bound fm.aestronglyMeasurable ((((A).params k).columns*M)*s)
    (ae_of_all _ fun U=>by rw [Real.norm_eq_abs,abs_of_nonneg (f0 U)];exact mul_le_mul_of_nonneg_right (gross.2 U) s0)
  have F2:MemLp F 2 μ:=MemLp.of_bound gross.1.aestronglyMeasurable (((A).params k).columns*M) (ae_of_all _ gross.2)
  have pow2:ENNReal.ofReal (2:ℝ)=2:=by norm_num
  have hH':MemLp (fun w=>‖H w‖) (ENNReal.ofReal (2:ℝ)) ν:=pow2.symm ▸ hH.norm
  have hF':MemLp (f ∘ read) (ENNReal.ofReal (2:ℝ)) ν:=pow2.symm ▸ f2.comp_measurePreserving law
  have cs:=integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hH' hF'
  simp only [Function.comp_apply,Real.rpow_two,←Real.sqrt_eq_rpow,Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _),abs_of_nonneg (f0 _)] at cs
  refine ⟨hH.integrable_mul (F2.comp_measurePreserving law),?_⟩
  calc
    _=(∫w,‖H w‖*f (read w) ∂ν):=by
      rw [←integral_mul_const];congr 1;funext w;rw [norm_mul];dsimp only [f];ring
    _ ≤ _:=cs.trans (mul_le_mul_of_nonneg_left square (Real.sqrt_nonneg _))

end YM.Integration.WilsonRegisteredAxialPull
end
