import YM.Integration.FVA1Physical.Marked.CurrentRunField
import YM.Integration.FVA1Physical.Marked.QuaySpatialReserve

/-! Rooted spatial derivative sum for the actual current normalized physical
stencil on the same purchased run, in the Wilson column's own location norm. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.Local Push.AbsoluteSums RGComparison.Core16.Spool
open Next.Foundations RGComparison.Core16.Lam RGComparison.Core16.Catkin MSbar.Whisk
open Integration.FVA1Physical.Round2.Curvature
open scoped Classical BigOperators Topology
variable {G:Gauge}
private theorem clear_density_at {n:Side} (o:Site n) (V:Rep G n) (Q:Coefficient ((frames G).level 0) n)
    (Y:Config G n) (good:flags V.p.threshold Y=∅) :
    Q.density o (localSection G 0) V Y=(V.eval Y:ℂ)*Q.exponentialEntry o (localSection G 0) V Y := by
  have kill (a:Finset ℕ) : Q.marked V a Y=0 := by
    unfold Coefficient.marked
    split
    next ha =>
      have empty : a=∅ := by
        by_contra h
        obtain ⟨i,hi⟩:=Finset.nonempty_iff_ne_empty.mpr h
        have inclusion: (V.activities.forced i).inventory ⊆ a.biUnion (fun k=>(V.activities.forced k).inventory) :=
          Finset.subset_biUnion_of_mem (fun k=>(V.activities.forced k).inventory) hi
        rw [ha.2,good] at inclusion
        exact (V.activities.forced i).inventory_ne.ne_empty (Finset.subset_empty.mp inclusion)
      subst a;simp
    next => rfl
  simp only [Coefficient.density,kill,tsum_zero,mul_zero,add_zero]

variable (H:History G) (sel:H.Selected) {N n m:ℕ} (hm:m < N)
local notation "RI" => H.rep N n (m+1)
local notation "RO" => H.rep N n m
local notation "K" => H.levels.clock.op m n
local notation "D0" => localSection G 0
include sel hm
theorem current_germ (o:Site (H.S.side m n)) (f:Config G (H.S.side (m+1) n) → ℝ)
    (Q:Coefficient ((frames G).level 0) (H.S.side m n))
    (exactness:Q.density o D0 RO=(K).push (RI).beta (fun W=>((RI).eval W:ℂ)*(f W:ℂ)))
    {U:Config G (H.S.side m n)} (healthy:U∈Boulevard.sunny (RO).p) :
    (fun V=>(MSbar.Bulk.expect K RI V f:ℂ)) =ᶠ[𝓝 U] Q.exponentialEntry o D0 RO := by
  filter_upwards [(Boulevard.sky (RO).p).mem_nhds healthy] with V hv
  have h:=congrFun exactness V
  rw [clear_density_at o RO Q V (Boulevard.smoky hv)] at h
  have denominator : (RO).eval V=(K).push (RI).beta (RI).eval V:=congrFun (sel.steps N n m hm).1 V
  have cast : (K).push (RI).beta (fun W=>((RI).eval W:ℂ)*(f W:ℂ)) V=(((K).push (RI).beta (f*(RI).eval) V:ℝ):ℂ) := by
    unfold StepData.push
    simp only [Pi.mul_apply,Complex.real_smul,←Complex.ofReal_mul,smul_eq_mul]
    simp_rw [mul_comm ((RI).eval _) (f _)]
    exact integral_complex_ofReal
  rw [cast] at h
  rw [MSbar.Bulk.expect,←denominator,Complex.ofReal_div,←h]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (SectorNext.Vacuum.strictly H sel N n m hm.le V).ne')

omit sel
variable {I:Type} [Fintype I] {d:ℕ} (R:Run G)
theorem current_run_spatial (simple:G.Simple) (start:R.t 0 ≤ m)
    (a:I → CoverLabel G d) (ready:∀ j,R.t (a j).1.val ≤ m+1)
    (y:Site (R.family.side (m+1) n)) (o:I → Site (R.family.side (m+1) n)) (part:Bool)
    (radius:ℕ) (foot:∀ j,separation (o j-y) 0 ≤ radius) (q s:ℕ) (nq:0 < q)
    {α b:ℝ} (pos:0 < α) (b0:0 ≤ b) (V:Config G (R.family.side m n)) :
    let H:=R.family.path
    let B:=(H.rep N n m).p
    let BI:=(H.rep N n (m+1)).p
    let S:=H.levels.clock.op m n
    let v:=fun j=>o j-y
    let z:=S.ratio.parent y
    let φ:=fun U=>look part (tally (freshLamps a) o U)
    let φ₀:=fun U=>look part (tally (freshLamps a) v U)
    let rate:=((s:ℝ)+1)*α+2*b
    let cost:=Doors.rate (H.S.block m)*birthCost BI (lampSupport a v) (H.levels.clock.forcedAllowance (m+1))
      (localFieldTariff BI a (R.alloy.B.a.params (m+1)).columns radius+‖(φ₀ 1:ℂ)‖) (2*stencilBound (freshLamps a))
    q ≤ B.order → rate*q*(6*B.B+2:ℝ) ≤ B.supportExponent → V∈Boulevard.sunny B → 
    Yarn q (fun l=>‖leftDerivs (fun W=>(MSbar.Bulk.expect S (H.rep N n (m+1)) W φ:ℂ))
      (l.map compass) V‖ * spread crest {z} b s l) ≤ 
      (1+2*α⁻¹)^s*(4*Fintype.card G.ColorIndex*Push.Uniform.countCost α)^q*((B.threshold⁻¹)^q*cost) := by
  intro H B BI S v z φ φ₀ rate cost hq room healthy
  obtain ⟨Q,format,dens,budget⟩:=current_run_field R simple hm start a ready y o part radius foot
  have clean:=current_germ H R.makes.wilson hm z φ Q dens healthy
  have c0:0 ≤ cost:=by obtain ⟨a,b,ha,hb,hab,_⟩:=budget;exact (add_nonneg ha hb).trans hab
  apply rooted_spread_price z q s _ (mul_nonneg (pow_nonneg (inv_nonneg.mpr B.threshold_pos.le) _) c0) b0 pos
    (fun _ _=>norm_nonneg _)
  intro l length
  rw [(UVNext.PricedKernels.left_congr clean (l.map compass)).self_of_nhds]
  have h:=rooted_entry D0 format budget l (by intro e;rw [e] at length;simp at length;omega)
    (length.le.trans hq) (show 0 ≤ rate by unfold rate;positivity) (by simpa only [length] using room) healthy
  simpa only [length] using h
end YM.Integration.FVA1Physical.Marked
