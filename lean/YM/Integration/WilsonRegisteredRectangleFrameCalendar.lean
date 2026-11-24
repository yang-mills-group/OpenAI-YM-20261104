import YM.Integration.WilsonRegisteredRectangleFrameWall
import YM.Integration.WilsonRegisteredRectangleFrameHeat

/-! The real measured radii contain the complete Wilson transition stencils. Their separating shell has a before-period physical price. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredRectangleFrameCalendar
open Push.AbsoluteSums Lattice RG Wilson RG16 Finset Filter OPE.Therm PhysicalNext.Repeat.Legato
open WilsonRegisteredRectangleFrameNeighborhood WilsonRegisteredRectangleFrameWall WilsonReportingForestPivots
open WilsonPhysicalLocalPlaquetteReserve
open scoped Classical Topology
variable {G:Gauge}{c f:Side}

theorem size (S:StepData c f)(o:Site f)(r:ℕ):(wall S o r).card ≤ (2*(r+S.patch.L.val)+1)^4:=by
  have inj:Function.Injective S.ratio.embed:=Function.LeftInverse.injective S.ratio.embed_parent
  have sub:(wall S o r).image S.ratio.embed⊆Animals.neighbors (r+S.patch.L.val) o:=by
    intro y hy;obtain ⟨x,h,rfl⟩:=mem_image.mp hy
    exact (Animals.neighbors_mem ..).mpr ((mem_filter.mp h).2.2)
  rw [← Finset.card_image_of_injective _ inj]
  simpa only [Animals.ballCost,two_mul] using (card_le_card sub).trans (Animals.neighbors_card _ _)

variable (R:Run G)
local notation "A" => R.family.path.levels

theorem dates (simple:G.Simple)(slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A) m)):
    ∀ᶠm:ℕ in atTop,∀per,let S:=(A).clock.op m per
      let B:=((A).budget (m+1)).B
      let b:=(A).clock.hatBeta (m+1)
      2≤B ∧ bondRoom S≤B^2 ∧ ∀o:Site (R.family.side (m+1) per),((wall S o (3*B^2)).card:ℝ)≤b^8:=by
  have grows:=(Next.Rank.Station.hat_rate (A) simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [grade_room (A),(Real.tendsto_log_atTop.comp grows).eventually_ge_atTop (600:ℝ),
    grows.eventually_ge_atTop (10:ℝ),grows.eventually (small 4 4 zero_lt_one)] with m grade logs big sm per
  let V:=R.family.path.levels
  let S:=V.clock.op m per
  let B:=(V.budget (m+1)).B
  let b:=V.clock.hatBeta (m+1)
  let t:=Real.log b
  let L:=(V.S.block m).val
  let j:=V.clock.J (m+1)
  change j≤L at grade
  change (600:ℝ) ≤ t at logs
  change (10:ℝ) ≤ b at big
  have bp:0<b:=by linarith only [big]
  have product:4*t^4/Real.sqrt b≤1:=by
    simpa only [div_eq_mul_inv,t,b,V,Function.comp_apply] using sm
  have tiny:4*t^4 ≤ Real.sqrt b:=by simpa only [one_mul] using (div_le_iff₀ (Real.sqrt_pos.2 bp)).mp product
  have floor:t^2 ≤ (B:ℝ):=Nat.le_ceil _
  have top:(B:ℝ) ≤ t^2+1:=(Nat.ceil_lt_add_one (sq_nonneg t)).le
  have t1:1≤t^2:=by nlinarith only [logs,sq_nonneg (t-1)]
  have domain:(B:ℝ)^2≤b:=calc
    _≤(t^2+1)^2:=pow_le_pow_left₀ (Nat.cast_nonneg _) top 2
    _≤4*t^4:=by nlinarith only [sq_nonneg (t^2-1),t1]
    _≤_:=tiny.trans (by nlinarith only [big,Real.sq_sqrt bp.le,sq_nonneg (Real.sqrt b-1)])
  have hL:(L:ℝ) ≤ 3*t:=by
    have hi: (L:ℝ)≤2+t:=(slow m).trans ((Real.log_le_self (Literal.lambda_pos R.family m).le).trans
      ((Literal.lambda_mono R.family simple).monotone (Nat.le_succ m)))
    linarith
  have hj:(j:ℝ)≤3*t:=(Nat.cast_le.mpr grade).trans hL
  have budget:(bondRoom S:ℝ)≤(B:ℝ)^2:=calc
    _ = (L:ℝ)+10*(((j:ℝ)+3)*L+L+1):=by change ((L+10*((j+3)*L+L+1):ℕ):ℝ)=_;push_cast;rfl
    _ ≤ 3*t+10*((3*t+3)*(3*t)+3*t+1):=by gcongr
    _ ≤ 300*t^2:=by nlinarith only [logs,sq_nonneg (t-1)]
    _ ≤ (t^2)^2:=by nlinarith only [mul_nonneg (sq_nonneg t) (show 0≤t^2-300 by nlinarith only [logs,sq_nonneg (t-1)])]
    _ ≤ _:=pow_le_pow_left₀ (sq_nonneg _) floor 2
  have room:bondRoom S≤B^2:=by exact_mod_cast budget
  have wide:2≤B:=by exact_mod_cast (show (2:ℝ)≤B by nlinarith only [floor,logs,sq_nonneg (t-1)])
  refine ⟨wide,room,?_⟩
  intro o
  have block:S.patch.L.val≤B^2:=(Nat.le_add_right S.patch.L.val (WilsonRegisteredRectangleFrameNeighborhood.room S.patch)).trans room
  have measured:((wall S o (3*B^2)).card:ℝ)≤(2*(3*(B:ℝ)^2+(S.patch.L.val:ℝ))+1)^4:=by
    exact_mod_cast size S o (3*B^2)
  have bw:(S.patch.L.val:ℝ)≤(B:ℝ)^2:=by exact_mod_cast block
  have inside:2*(3*(B:ℝ)^2+(S.patch.L.val:ℝ))+1 ≤ b^2:=by
    nlinarith only [bw,domain,big,sq_nonneg (b-9)]
  exact measured.trans ((pow_le_pow_left₀ (by positivity) inside 4).trans_eq (by ring))

end YM.Integration.WilsonRegisteredRectangleFrameCalendar
