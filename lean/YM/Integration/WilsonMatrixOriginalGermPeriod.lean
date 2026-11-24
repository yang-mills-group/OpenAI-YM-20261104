import YM.Integration.WilsonMatrixOriginalGermColumn
import YM.Integration.WilsonMatrixOriginalIndependentLimit
import YM.Integration.ActualOuterQuarterProfile

noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermPeriod
open Filter Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open Function RG12 RG17 Spec Next.Rank.Price
open PhysicalNext.Repeat.Legato WilsonMatrixTicketLanesNativePrices
open WilsonMatrixOriginalIndependentColumns WilsonMatrixTicketLanesRegulatorColumn
open WilsonMatrixOriginalIndependentForest WilsonMatrixOriginalIndependentLimit
open FVA2 MS.Local.Physical MS.Menus RGComparison.Core16.Astage
open scoped BigOperators Classical Topology
open private side_tendsto from YM.Integration.ActualOuterQuarterProfile

/-- The finite winding invoice vanishes in the original period limit at each fixed date. -/
theorem winds {G:Gauge} (C:Family G) (d m:ℕ) (f:Extraction.Order) :
    Tendsto (fun z:ℕ×ℕ=>invoice (C:=C) d m z.2) f.fuse (𝓝 0) := by
  let B:=plank C m
  have per:Tendsto (Prod.snd:ℕ×ℕ→ℕ) f.fuse atTop := by
    apply tendsto_atTop.mpr;intro n
    change f.late (fun _ p=>n≤p)
    exact (f.per.cofinal.eventually_ge_atTop n).mono fun _ h=>Eventually.of_forall fun _=>h
  have side:Tendsto (fun z:ℕ×ℕ=>((C.side m z.2).val:ℝ)) f.fuse atTop:=(side_tendsto C.S m).comp per
  have den:0<10*(4*(B.B:ℝ)+2):=by positivity
  have gone:=((side.const_mul_atTop B.exponent_pos).atTop_div_const den)
  have back:=tendsto_neg_atTop_atBot.comp gone
  have down:=Filter.tendsto_atBot_add_const_left f.fuse (2*B.supportExponent) back
  have cost:=Real.tendsto_exp_atBot.comp down
  simpa [invoice,cut,Germ.wraps,B,sub_eq_add_neg,Function.comp_def] using
    cost.const_mul (price (C:=C) d)

/-- A uniformly financed full coefficient has the same limiting coordinates as its principal part. -/
theorem projected {G:Gauge} (C:Family G) (h:C.Makes) (d m:ℕ) (f:Extraction.Order)
    {U:Filter (ℕ×ℕ)} (sub:U≤f.fuse) (age : C.ref d ≤ m)
    (q : (z : ℕ × ℕ) → Coefficient (C.labels.level d) (C.side m z.2)) (fee:ℝ)
    (bought:∀ᶠz in U,reads d z.1 z.2 m (q z) fee) :
    Tendsto (fun z=>page d z.2 m (q z)-(q z).x) U (𝓝 0):= by
  apply tendsto_pi_nhds.mpr;intro i
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have cap:=(((winds C d m f).mono_left sub).mul_const fee)
  apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) _ (by simpa using cap)
  filter_upwards [bought,((OPE.Cards.largeMesh f).eventually_ge_atTop m).filter_mono sub] with z hz live
  have cash:=measured_diff (C:=C) d z.1 z.2 m h age live hz
  exact (Finset.single_le_sum (f:=fun i=>‖(page d z.2 m (q z)-(q z).x) i‖)
    (fun _ _=>norm_nonneg _) (Finset.mem_univ i)).trans cash

variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (L:Layout F)

/-- The complete original Wilson coefficient at m, including all its old regular entries. -/
def captured (r:ℝ) (w:R.family.label 4) (z:ℕ×ℕ) :=
  (R.family.factory 4 z.1 z.2).entries (L.level r)
    ((R.family.factory 4 z.1 z.2).terminal.symm (atRef L 4 r z w))

/-- The actual normalized germ of a deposited field converges to exactly its submitted raw input. -/
theorem at_date (U:Ultrafilter (ℕ×ℕ)) (hU:(U:Filter (ℕ×ℕ))≤L.lens)
    (r:ℝ) (w:R.family.label 4) (age:R.family.ref 4≤L.level r):
    Tendsto (fun z:ℕ×ℕ=>(↑(R.family.S.a (L.level r)^4):ℂ)⁻¹ •
      page 4 z.2 (L.level r) (captured R F L r w z)) (U:Filter _) (𝓝 (L.shift 4 r w)):= by
  let m:=L.level r
  let a:ℂ:=↑(R.family.S.a m^4)
  let q:=captured R F L r w
  let x:R.family.label 4:=a • L.shift 4 r w
  let sub:=hU.trans L.certified
  have nz:a≠0:=Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (R.family.S.a_pos _).ne')
  have principal (z:ℕ×ℕ) (live:m≤z.1):(q z).x=x:=by
    have loc:=WilsonMatrixOriginalIndependentLimit.filed R F L r w z.1 z.2 age live
    change a⁻¹ • (q z).x=L.shift 4 r w at loc
    have placed:=congrArg (fun t:R.family.label 4=>a • t) loc
    simpa only [smul_smul,mul_inv_cancel₀ nz,one_smul] using placed
  have late:=((OPE.Cards.largeMesh f).eventually_ge_atTop m).filter_mono sub
  have bounded:∀ᶠ z in (U:Filter _),reads 4 z.1 z.2 m (q z)
      (stock R.family m*(R.family.labels.level 4).coeffSize x):=by
    filter_upwards [late] with z live
    rw [←principal z live]
    exact entryOk 4 z.1 z.2 m R.makes age live _
  have germ:=projected R.family R.makes 4 m f sub age q _ bounded
  have solid:Tendsto (fun z=>(q z).x) (U:Filter (ℕ×ℕ)) (𝓝 x):=
    tendsto_const_nhds.congr' (late.mono fun z h=>(principal z h).symm)
  have total:=germ.add solid
  have ready:Tendsto (fun z=>page 4 z.2 m (q z)) (U:Filter (ℕ×ℕ)) (𝓝 x):=by
    simpa only [sub_add_cancel,zero_add] using total
  simpa only [x,smul_smul,inv_mul_cancel₀ nz,one_smul] using ready.const_smul a⁻¹

end YM.Integration.WilsonMatrixOriginalGermPeriod
