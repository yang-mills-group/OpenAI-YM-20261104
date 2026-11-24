import YM.Integration.WilsonRegisteredRectangleFrameWindow
import YM.Integration.WilsonReportingForestTagCalendar
import YM.Integration.WilsonReportingForestCompactAngles

/-! A cropped thermal reporting block forces the actual common Wilson minimizing frame at every sufficiently late date. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredRectangleFrameRoom
open Filter Set Finset Lattice RG Wilson RG16 Pressure OPE.Therm PhysicalNext.Repeat.Legato
open WilsonPhysicalLocalPlaquetteReserve WilsonRegisteredRectangleFrameWindow WilsonReportingForestPivots
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "A" => R.family.path.levels

theorem calendar (simple:G.Simple)(slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda (A) m)):
    ∀ᶠm:ℕ in atTop,∀per,let S:=(A).clock.op m per
      charge S.patch (cool (A) (m+1)) < S.kernel.frame_cut:=by
  let pay:ℝ:=50000*(Fintype.card PlaqAxes:ℝ)
  have grow:=(Next.Rank.Station.hat_rate (A) simple).comp (tendsto_add_atTop_nat 1)
  have hp:0<(A).clock.kernel.frame_cut/2:=half_pos (A).clock.kernel.frame_cut_pos
  filter_upwards [grade_room (A),(Real.tendsto_log_atTop.comp grow).eventually_ge_atTop (1:ℝ),
    grow.eventually (small pay 16 hp)] with m grade logs fee per
  let S:=(A).clock.op m per
  let b:=(A).clock.hatBeta (m+1)
  let s:=Real.log b
  let L:ℕ:=((A).S.block m).val
  let j:ℕ:=(A).clock.J (m+1)
  change j ≤ L at grade
  change 1 ≤ s at logs
  change pay*s^16*(Real.sqrt b)⁻¹ ≤ (A).clock.kernel.frame_cut/2 at fee
  have l0:0<L:=((A).S.block m).property
  have hi:(L:ℝ)≤2+s:=(slow m).trans ((Real.log_le_self (Literal.lambda_pos R.family m).le).trans
    ((Literal.lambda_mono R.family simple).monotone (Nat.le_succ m)))
  have hL:(L:ℝ)≤3*s:=by linarith only [hi,logs]
  have hJ:j+3≤4*L:=by omega
  have hRnat:(j+3)*L≤4*L^2:=calc
    _ ≤ (4*L)*L:=Nat.mul_le_mul_right L hJ
    _ = _:=by ring
  have hr:(S.patch.radius:ℝ)≤4*(L:ℝ)^2:=by
    exact_mod_cast hRnat
  have hs1:1 ≤ s^2:=one_le_pow₀ logs
  have slab:((S.patch.radius:ℝ))≤36*s^2:=by
    nlinarith only [hr,pow_le_pow_left₀ (Nat.cast_nonneg L) hL 2]
  have h₁:(2*(S.patch.radius:ℝ)+1) ≤ 73*s^2:=by linarith only [hs1,slab]
  have h₂:((S.patch.radius+1:ℕ):ℝ) ≤ 37*s^2:=by push_cast;linarith only [hs1,slab]
  let c:ℝ:=Fintype.card PlaqAxes
  let g:ℝ:=(Real.sqrt b)⁻¹
  have g0:0≤g:=by dsimp [g];positivity
  have s0:0 ≤ s:=zero_le_one.trans logs
  have c0:0≤c:=Nat.cast_nonneg _
  have amount:charge S.patch (cool (A) (m+1))≤pay*s^16*g:=calc
    _=4*((2*(S.patch.radius:ℝ)+1)*(4*((S.patch.radius+1:ℕ):ℝ)*(c*(g*s^12)))):=rfl
    _≤4*((73*s^2)*(4*(37*s^2)*(c*(g*s^12)))):=by gcongr
    _=43216*c*s^16*g:=by ring
    _≤pay*s^16*g:=by dsimp only [pay,c];gcongr;norm_num
  exact amount.trans_lt (lt_of_le_of_lt fee (half_lt_self (A).clock.kernel.frame_cut_pos))

theorem original (simple:G.Simple)(slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda (A) m)):
    ∀ᶠm:ℕ in atTop,∀per,let S:=(A).clock.op m per
      ∀(o:Site (R.family.side m per))(U:Config G (R.family.side (m+1) per))(τ:ℝ),
      0≤τ→τ≤cool (A) (m+1)→U∈House.chilly (tagCells R m per (S.ratio.embed o)) τ →
        S.patch.usesMin S.kernel (expandAt (S.ratio.embed o) U):=by
  filter_upwards [calendar R simple slow] with m prices per
  intro S o U τ hp ht hc
  apply placed S o U τ hp
  · rintro ⟨x,a⟩ hx
    rcases mem_image.mp (mem_product.mp hx).1 with ⟨z,hz,rfl⟩
    apply hc (wrap _ z+S.ratio.embed o,a)
    apply WilsonAxialWindow.cell
    apply Planned.PrimaryIntegral295.Racks.within _ hz
    have live:0<S.patch.L.val:=S.patch.L.property
    change S.patch.radius+1 ≤ 4*macroR S.patch
    unfold macroR;omega
  · apply lt_of_le_of_lt _ (prices per)
    unfold charge;gcongr

end YM.Integration.WilsonRegisteredRectangleFrameRoom
