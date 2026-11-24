import YM.Integration.WilsonConditionalTaylorKineticIncome
import YM.UVNext.PRICED_KERNELS.Echo

/-! The measured finite kinetic denominator tends to minus two on the
actual sequence of physical tori. Its quantitative wrap fee is uniform
in the horizon at a fixed height. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorKineticWrap

open Filter Lattice RG Wilson Precision Push.Uniform PhysicalNext.Repeat.Legato
open MSbar MSbar.Midpoint MSbar.Heath MSbar.Cacao MSbar.Wave MSbar.Bakery MSbar.Bakery.Portal
open Qlocal.Schedule WilsonConditionalTaylorSceneCalibration WilsonConditionalTaylorKineticIncome
open scoped Classical Topology

def price (H : Stage) (n : ℕ) : ℝ := (Fintype.card PlaqAxes:ℝ)*H.paths*H.paths *
  ((16*(n:ℝ)^10+2)*Real.exp (-(H.width/100)*(n:ℝ))*Real.exp H.width)

theorem decays (H : Stage) : Tendsto (price H) atTop (𝓝 0) := by
  let a:=H.width/100
  have ha:0<a:=div_pos H.width_pos (by norm_num)
  let f(n:ℕ):=Real.exp (-a*(n:ℝ))
  have powers:Tendsto (fun n:ℕ=>(n:ℝ)^10 * f n) atTop (𝓝 0):=by
    have h:=(Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 10).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
    have h':=h.div_const (a^10)
    rw [zero_div] at h'
    refine h'.congr' (Eventually.of_forall fun n=>?_)
    unfold f
    change (a*n)^10*_*_⁻¹=_
    field_simp
  have flat:Tendsto f atTop (𝓝 0):=Real.tendsto_exp_atBot.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_lt_zero.mpr ha))
  have h:=(((powers.const_mul 16).add (flat.const_mul 2)).mul_const (Real.exp H.width)).const_mul
    ((Fintype.card PlaqAxes:ℝ)*H.paths*H.paths)
  simp only [mul_zero,zero_mul,add_zero] at h
  refine h.congr fun n=>?_
  unfold price
  dsimp only [f,a]
  ring

theorem wrapping (H : Stage) (n : Side) :
    (Fintype.card PlaqAxes:ℝ)*(H.paths*H.paths*url n (n.val/100) H.width) ≤ price H n.val := by
  let p:=n.val/100
  have small : (n.val:ℝ)<100*((p:ℝ)+1):=by exact_mod_cast (show n.val<100*(p+1) by dsimp [p];omega)
  have exp : Real.exp (-H.width*(p:ℝ)) ≤ Real.exp (-(H.width/100)*(n.val:ℝ))*Real.exp H.width := by
    rw [←Real.exp_add]
    apply Real.exp_monotone
    nlinarith only [mul_le_mul_of_nonneg_left small.le H.width_pos.le]
  have pre : (Fintype.card PlaqAxes:ℝ)*H.paths*H.paths*(16*(n.val:ℝ)^10+2)≥0 := by
    have hp:=H.paths_pos; positivity
  have fee:=mul_le_mul_of_nonneg_left exp pre
  unfold price url Midpoint.size
  simp only [site_card,Nat.cast_pow]
  dsimp only [p] at fee
  ring_nf at fee ⊢
  exact fee

variable {G : Gauge} (R : Run G) (simple : G.Simple) (u : G.ColorIndex) (V : Voice G)
    (invoice : vacuumInvoice u V R.metals R.rolls R.alloy R.kit)

include invoice simple in
theorem torus (N j n : ℕ) (hi : j≤N) (room : 1000 < (R.family.side j n).val) :
    |denominator (N:=N) (n:=n) R u j+2| ≤ price (R.family.path.levels.params j) (R.family.side j n).val := by
  have growth:Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2; intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with k hk
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 k hk).1)
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  have merit:=townsR R.b R.Q R.T R.t R.stories R.doors ch
  obtain ⟨S,scene⟩:=Alto.chosen R.alloy.B simple (invoice.1 growth).levy merit N u 0 n hi
  let H:=R.family.path.levels.params j
  let P:=R.alloy.B.kin.path N j
  let per:=R.family.side j n
  let K:=RunFormalChain.fromRun R
  have test:=congrArg (stackH per (Lis.sun G u)) (ion P H.clip (scene.budget j hi le_rfl).1.quiet)
  change denominator (N:=N) (n:=n) R u j=_ at test
  rw [test]
  have cut:10*(per.val/100+4)<per.val:=by change 1000<per.val at room;omega
  exact (sampled (Lis.sun G u) P H.clip (K.planned.cap N j hi) (per.val/100) cut (Lis.sunny ..)).trans
    (wrapping H per)

include invoice simple in
theorem limit (N j : ℕ) (hi : j≤N) :
    Tendsto (fun n : ℕ=>denominator (N:=N) (n:=n) R u j) atTop (𝓝 (-2)) := by
  let H:=R.family.path.levels.params j
  have sides:=UVNext.PricedKernels.Echo.schedule_sides R.family.path.levels.S j
  have bound:=(decays H).comp sides
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [sides.eventually (eventually_gt_atTop 1000),bound.eventually (gt_mem_nhds hε)] with n large small
  rw [Real.dist_eq,sub_neg_eq_add]
  exact (torus R simple u V invoice N j n hi large).trans_lt small

end YM.Integration.WilsonConditionalTaylorKineticWrap
end

