import YM.Integration.WilsonPointChildScalarSlot
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildQuoteWidth
open Filter Finset Lattice RG WilsonCoeffUV Laurent FormalBulk08 Borough Primer
open WilsonCoeffUV.Bank
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Topology Classical
variable {G:Gauge}

/-- A before-election lookup, using only the original kernel and block
length on a Gazette gear. -/
def quote (I:Gear G):ℝ:=(Finset.range (I.patch.L.val+1)).inf'
  (⟨0,Finset.mem_range.mpr (Nat.succ_pos _)⟩) (windowBasis G I.kernel).width

theorem positive(I:Gear G):0<quote I:=by
  unfold quote
  apply (Finset.lt_inf'_iff _).2
  intro k _
  exact (windowBasis G I.kernel).pos k

theorem index(A:Levels G):∀ᶠj:ℕ in atTop,A.clock.J (j+1)≤(A.S.block j).val:=by
  have pos:=Real.log_pos (one_lt_two (α:=ℝ))
  filter_upwards [((tendsto_natCast_atTop_atTop (R:=ℝ)).comp
      (A.fits.deep.comp (tendsto_add_atTop_nat 1))).eventually_ge_atTop (1/Real.log 2)] with j due
  let p:=A.params (j+1)
  let L:ℝ:=(A.S.block j).val
  have large:1<L:=by have h:=A.S.block_large j;unfold L;exact_mod_cast (show 1<(A.S.block j).val from by omega)
  let K:=(A.clock.J (j+1):ℝ)
  have nonneg:0≤K:=Nat.cast_nonneg _
  let x:=1+p.paths+p.width⁻¹+p.columns+p.clip.relaxation+p.supportExponent
  have wide:2≤x:=by unfold x;linarith only [p.paths_pos,p.clip.radius_pos,p.columns_ge,p.price_pos,inv_pos.mpr p.width_pos]
  have hlog:Real.log 2≤Real.log x:=Real.log_le_log (by norm_num) wide
  have bound:=(div_le_iff₀ (Real.log_pos large)).mp (show Real.log x/Real.log L≤(K^2)⁻¹ from A.fits.logCost j)
  have kpos:0<K:=by have h:=A.clock.adm (j+1);unfold K;exact_mod_cast (show 0<A.clock.J (j+1) from by omega)
  have total:=mul_le_mul_of_nonneg_right bound (sq_nonneg K)
  have slope:Real.log 2*K^2≤Real.log L:=by
    calc _≤Real.log x*K^2:=mul_le_mul_of_nonneg_right hlog (sq_nonneg K)
      _≤(K^2)⁻¹*Real.log L*K^2:=total
      _ = Real.log L:=by field_simp
  have base:1≤Real.log 2*K:=by
    have one:1≤K*Real.log 2:=(div_le_iff₀ pos).mp due
    linarith
  have paid:K≤L:=calc
    _≤Real.log 2*K^2:=by nlinarith only [mul_le_mul_of_nonneg_right base nonneg]
    _≤Real.log L:=slope
    _≤L:=by linarith only [Real.log_le_sub_one_of_pos (zero_lt_one.trans large)]
  change (A.clock.J (j+1):ℝ)≤((A.S.block j).val:ℝ) at paid
  exact_mod_cast paid

theorem enrolled (R:Run G){e:ℕ}{H:Credit}(Q:Bank.Realm G e H)(same:Q.draws=R.family.path.levels):
    ∀ᶠj:ℕ in atTop,∀h:Q.anchor≤j,quote (Q.mint j h).gear≤WilsonPointChildFiledPress.width R (j+1):=by
  filter_upwards [index R.family.path.levels] with j paying
  intro h
  let I:=(Q.mint j h).gear
  have kernel:I.kernel=R.family.path.levels.clock.kernel:=congrArg (fun A=>Levels.clock A |>.kernel) same
  have L:I.patch.L=R.family.S.block j:=congrArg (fun A=>(loose A j).L) same
  unfold quote
  have use:=Finset.inf'_le ((windowBasis G I.kernel).width)
    (show R.family.path.levels.clock.J (j+1)∈Finset.range (I.patch.L.val+1) from Finset.mem_range.mpr (by rw [L];exact Nat.lt_succ_of_le paying))
  exact use.trans_eq (congrArg (fun K=>(windowBasis G K).width (R.family.path.levels.clock.J (j+1))) kernel)

end YM.Integration.WilsonPointChildQuoteWidth
