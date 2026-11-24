import YM.Integration.WilsonReportingForestRelative
import YM.Integration.WilsonRegisteredChartTaylorRate

/-! On the actual accepted nonlinear chart the tangent variable itself is
small to the required measured order, including on all crossing links. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIncidentChartTaylorRate
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open MSbar.Heath OPE.Therm RG16 PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonReportingForestPivots WilsonReportingRegisteredAction WilsonReportingForestBlocks
open WilsonPhysicalLocalPlaquetteForest WilsonPhysicalRegisteredForestAction WilsonPhysicalRegisteredForestCrossing
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]

private theorem area_le {D H:ℕ} (h:D≤H) (L:ℕ) : area D L ≤ area H L := by
  have l:lanes D L≤lanes H L:=by unfold lanes;omega
  have r:radius D L≤radius H L:=by unfold radius;omega
  unfold area
  exact mul_le_mul (Nat.cast_le.mpr l) (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr r) (by norm_num : (0:ℝ)≤4)) (Nat.cast_nonneg _))
    (by positivity) (Nat.cast_nonneg _)

def reach (d:I→ℕ) := Finset.univ.sup fun i=>depth R (d i)+3

theorem coordinates (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P) (d:I→ℕ) :
    ∀ᶠ j:ℕ in atTop,∀per (o:I→Site (R.family.side (j+1) per)) (T:Forest (R.family.path.levels.clock.op j per).ratio),
    let B:=incident R T d o
    let E:=moving T B
    let L:=(R.family.path.levels.clock.op j per).ratio.count.val
    ∀(v:({e:T.Free|e∉E}:Set T.Free)→G.El) (x:↥E→G.Color),x∈ball 0 r →
      restored T B v (Chart.expLinks G (↥E) x)∈cold R j per d o →
      ‖x‖≤2*J.C*(area (extent (reach R d) L) L*cool R.family.path.levels (j+1)) := by
  let η:=min J.δ (r/(2*J.C))
  have pc:=zero_lt_one.trans_le clear.cost
  have hp:0<η:=lt_min clear.dist (div_pos pr (by positivity))
  filter_upwards [WilsonReportingForestBlocks.dates R.family simple slow (reach R d) (half_pos hp)] with j prices per o T B E L v x hx good
  let u:=(cut T E).symm (Chart.expLinks G (↥E) x*background T B v,v)
  let τ:=cool R.family.path.levels (j+1)
  have pt:0≤τ:=by dsimp [τ,cool,RG.Calendar.hatCoupling];positivity
  have a0:0≤area (extent (reach R d) L) L:=by unfold area;positivity
  have dom:0≤2*J.C*(area (extent (reach R d) L) L*τ):=by positivity
  apply (pi_norm_le_iff_of_nonneg dom).mpr
  intro e
  obtain ⟨i,near⟩:=anchored R T d o e.val (Finset.mem_filter.mp e.property).1
  let D:=depth R (d i)+3
  have bound:D≤reach R d:=Finset.le_sup (f:=fun i=>depth R (d i)+3) (Finset.mem_univ i)
  obtain ⟨period,buy,_⟩:=prices per D bound
  let b:=area (extent D L) L*τ
  have bpos:0≤b:=by dsimp [b,area];positivity
  have chord:G.chord (deviation T u e.val)≤2*b:=by
    by_cases hi:internal T e.val
    · have l:=near e.val rfl
      have seen:G.chord (u e.val)≤b:=free T (o i) _ period u pt (Set.mem_iInter.mp good i) e.val l.1 l.2 hi
      rw [deviation,if_pos hi];linarith only [seen,bpos]
    · have seen:=pair T (o i) _ period u pt (Set.mem_iInter.mp good i) e.val (pivot T e.val)
          (pair_of T e.val).symm (fun f hf=>near f (hf.elim (fun z=>z ▸ rfl) (fun z=>z ▸ pair_of T e.val)))
      simpa only [deviation,if_neg hi] using seen
  have two:2*b≤η:=by have h:b≤η/2:=buy;linarith only [h]
  let U:=deviation T u e.val
  have dec:=clear.near U (chord.trans (two.trans (min_le_left ..)))
  have cm:J.C*(r/(2*J.C))=r/2:=by field_simp
  have inside:J.decode U∈ball 0 r:=by
    rw [mem_ball_zero_iff]
    exact dec.2.2.trans_lt ((mul_le_mul_of_nonneg_left (chord.trans (two.trans (min_le_right ..))) pc.le).trans_lt
      (cm.trans_lt (half_lt_self pr)))
  have member:x e∈ball 0 r:=mem_ball_zero_iff.mpr ((norm_le_pi_norm x e).trans_lt (mem_ball_zero_iff.mp hx))
  have identify:U=G.lieExp (x e):=(decoded T B v (Chart.expLinks G (↥E) x)).1 e
  have left:=((LocalH.geom_patch G).choose_spec.2 r (sr.le.trans (min_le_right ..))).2.2.1
  have match':x e=J.decode U:=left.injOn member inside (identify.symm.trans dec.2.1.symm)
  have lift:extent D L≤extent (reach R d) L:=by unfold extent;omega
  have large:b≤area (extent (reach R d) L) L*τ:=mul_le_mul_of_nonneg_right (area_le lift L) pt
  rw [match']
  calc _≤J.C*G.chord U:=dec.2.2
       _≤J.C*(2*(area (extent (reach R d) L) L*τ)):=mul_le_mul_of_nonneg_left (chord.trans (mul_le_mul_of_nonneg_left large (by norm_num))) pc.le
       _=_:=by ring

/-- The Taylor inequality on the exact physical support is uniform before
the cutoff and period. Every frozen parent pivot may take its original value. -/
theorem purchased (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P)
    (d:I→ℕ) (q:ℕ) (C:ℝ) (c0:0≤C) {ε:ℝ} (he:0<ε) :
    ∀ᶠ j:ℕ in atTop,∀N per, j+1≤N → ∀ (o:I→Site (R.family.side (j+1) per)) (T:Forest (R.family.path.levels.clock.op j per).ratio),
    let B:=incident R T d o
    let E:=moving T B
    ∀(v:({e:T.Free|e∉E}:Set T.Free)→G.El) (x:↥E→G.Color),x∈ball 0 r →
      restored T B v (Chart.expLinks G (↥E) x)∈cold R j per d o →
      ‖x‖<1 ∧ C*‖x‖^(q+1)≤ε*regulatorRun R.family N per (j+1)^q := by
  have k:0≤2*J.C:=mul_nonneg (by norm_num) (zero_le_one.trans clear.cost)
  filter_upwards [coordinates R simple slow J clear P pr sr d,
    WilsonRegisteredChartTaylorRate.purchased R simple slow (reach R d) 0 1 _ zero_le_one k (ε:=1/2) (by norm_num),
    WilsonRegisteredChartTaylorRate.purchased R simple slow (reach R d) q C _ c0 k he]
    with j size small fee N per live o T B E v x hx cold
  have known:=size per o T v x hx cold
  have half:=small N per live _ ‖x‖ le_rfl (norm_nonneg _) known
  have h:‖x‖≤1/2:=by simpa only [zero_add,pow_one,one_mul,pow_zero,mul_one] using half
  exact ⟨h.trans_lt (by norm_num),fee N per live _ ‖x‖ le_rfl (norm_nonneg _) known⟩

end YM.Integration.WilsonIncidentChartTaylorRate
