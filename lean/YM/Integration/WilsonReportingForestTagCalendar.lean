import YM.Integration.WilsonReportingForestPivotPrediction

/-! The macro plaquettes used by the original tag at a touched interface fit
one contractible, thermally payable box at each reported location. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingForestPivots
open Lattice RG Wilson Tree OPE OPE.Therm RG16 Bid Pressure Filter PhysicalNext.Repeat.Legato
open WilsonPhysicalLocalPlaquetteReserve
open scoped Topology Classical
variable {G:Gauge}

/-- The submitted patch order fits the actual block on the original clock. -/
theorem grade_room (A:Levels G) : ∀ᶠ m:ℕ in atTop,A.clock.J (m+1)≤(A.S.block m).val := by
  have pos:=Real.log_pos (one_lt_two (α:=ℝ))
  filter_upwards [((tendsto_natCast_atTop_atTop (R:=ℝ)).comp
    (A.fits.deep.comp (tendsto_add_atTop_nat 1))).eventually_ge_atTop (1/Real.log 2)] with m due
  let p:=A.params (m+1)
  let L:ℝ:=(A.S.block m).val
  let j:ℝ:=A.clock.J (m+1)
  have large:1<L:=by
    have l:=A.S.block_large m
    dsimp [L]
    exact_mod_cast (show 1<(A.S.block m).val by omega)
  have j1:1≤j:=by
    have k:=A.clock.adm (m+1)
    dsimp [j]
    exact_mod_cast (show 1≤A.clock.J (m+1) by omega)
  let X:=1+p.paths+p.width⁻¹+p.columns+p.clip.relaxation+p.supportExponent
  have two:2≤X:=by
    dsimp [X]
    linarith only [p.paths_pos,p.columns_ge,p.clip.radius_pos,p.price_pos,inv_pos.mpr p.width_pos]
  have bound:=(div_le_iff₀ (Real.log_pos large)).mp
    (show Real.log X/Real.log L≤(j^2)⁻¹ from A.fits.logCost m)
  rw [inv_mul_eq_div] at bound
  have fit:=(le_div_iff₀ (show 0<j^2 by positivity)).mp ((Real.log_le_log two_pos two).trans bound)
  change 1/Real.log 2≤j at due
  have linear:=mul_le_mul_of_nonneg_right ((div_le_iff₀ pos).mp due) (zero_le_one.trans j1)
  have good:j≤L:=by nlinarith only [linear,fit,Real.log_le_sub_one_of_pos (zero_lt_one.trans large)]
  dsimp [j,L] at good
  exact_mod_cast good

def tagCells (R:Run G) (m per:ℕ) (o:Site (R.family.side (m+1) per)) : Finset (Face (Per (R.family.side (m+1) per))) :=
  WilsonAxialWindow.cells o (4*macroR (R.family.path.levels.clock.op m per).patch)

/-- The whole tagged reporting box has no winding and costs at most one fine
budget, uniformly before any original period or placement. -/
theorem tag_dates (R:Run G) (simple:G.Simple)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m)) :
    ∀ᶠ m:ℕ in atTop,∀per,let A:=R.family.path.levels
    let S:=A.clock.op m per
    2*(4*macroR S.patch)<(R.family.side (m+1) per).val ∧
      ∀o:Site (R.family.side (m+1) per),((tagCells R m per o).card:ℝ)≤A.clock.hatBeta (m+1) := by
  let A:=R.family.path.levels
  let C:ℝ:=577^4*Fintype.card PlaqAxes
  have grows:=(Next.Rank.Station.hat_rate A simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [grade_room A,MatchingR2.Top.step_shape R.family.path,
    (Real.tendsto_log_atTop.comp grows).eventually_ge_atTop (1:ℝ),
    grows.eventually (small C 8 zero_lt_one)] with m grade shape logs fee per
  let S:=A.clock.op m per
  let L:ℕ:=(A.S.block m).val
  let j:ℕ:=A.clock.J (m+1)
  let b:=A.clock.hatBeta (m+1)
  let s:=Real.log b
  change 1 ≤ s at logs
  change C*s^8*(Real.sqrt b)⁻¹≤1 at fee
  have bet:1<b:=A.fits.delayed _
  have sq:=Real.sqrt_pos.mpr (zero_lt_one.trans bet)
  have l0:0<L:=(A.S.block m).property
  have r:macroR S.patch=(j+7)*L:=by
    change (j+3)*L+4*L=(j+7)*L
    ring
  have big:= (shape per).2.1
  change 100*macroR S.patch≤(R.family.side (m+1) per).val at big
  have nonzero:0 < macroR S.patch:=by rw [r];positivity
  have wrap:2*(4*macroR S.patch)<(R.family.side (m+1) per).val:=
    (show 2*(4*macroR S.patch)<100*macroR S.patch by omega).trans_le big
  refine ⟨wrap,?_⟩
  intro o
  have lbound:(L:ℝ)≤2+s:=(slow m).trans ((Real.log_le_self (Literal.lambda_pos R.family m).le).trans
    ((Literal.lambda_mono R.family simple).monotone (Nat.le_succ m)))
  have l3:(L:ℝ)≤3*s:=by linarith only [logs,lbound]
  have bound:j+7≤8*L:=by change j≤L at grade;omega
  have radial:4*macroR S.patch≤32*L^2:=by
    rw [r]
    nlinarith only [Nat.mul_le_mul_right L bound]
  have purchase:(4*(macroR S.patch):ℝ)≤288*s^2:=by
    have h:4*(macroR S.patch:ℝ)≤32*(L:ℝ)^2:=by exact_mod_cast radial
    nlinarith only [h,pow_le_pow_left₀ (Nat.cast_nonneg L) l3 2]
  have span:((4*macroR S.patch:ℕ):ℝ)+(4*macroR S.patch:ℕ)+1≤577*s^2:=by
    push_cast
    linarith only [purchase,one_le_pow₀ logs (n:=2)]
  have cap:=WilsonAxialWindow.count o (4*macroR S.patch)
  have realcap:((tagCells R m per o).card:ℝ)≤
      (((4*macroR S.patch:ℕ):ℝ)+(4*macroR S.patch:ℕ)+1)^4*Fintype.card PlaqAxes:=by exact_mod_cast cap
  have paid:C*s^8≤Real.sqrt b:=(div_le_one₀ sq).mp (by rwa [div_eq_mul_inv])
  calc
    _≤_:=realcap
    _≤(577*s^2)^4*Fintype.card PlaqAxes:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) span 4) (by positivity)
    _=C*s^8:=by dsimp [C];ring
    _≤Real.sqrt b:=paid
    _≤b:=by nlinarith only [Real.sq_sqrt (zero_lt_one.trans bet).le,Real.one_le_sqrt.mpr bet.le]

end YM.Integration.WilsonReportingForestPivots
