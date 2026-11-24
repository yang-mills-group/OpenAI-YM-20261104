import YM.Integration.WilsonMovingForkProbeDates

/-! The position reading sets the actual independent geometry. A wider
window in the Wilson clock houses these same public field occurrences. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkMeasuredWindow
open Function Filter Lattice Wilson Extraction Table Spec Trace.Pilot Climb RG16 RG16.Literal
open PhysicalNext.Repeat.Legato Trace.Terrace PhysMS RG17 GapsContact.Seams GapsContact GapsContact.Ascent
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open scoped Classical Topology
variable {G:Gauge}

theorem room (simple:G.Simple){a b:ℝ→ℝ}(ha:Coupling G a)(hb:Coupling G b):
    ∀ᶠr in trail,(a r)^2≤b r:=by
  have rel:=ha.running.div hb.running (inv_ne_zero (Gauge.slopeConstant_pos simple).ne')
  simp only [div_self (inv_ne_zero (Gauge.slopeConstant_pos simple).ne')] at rel
  have rel':Tendsto (fun r=>(a r/b r)^2) trail (𝓝 1):=by
    apply rel.congr'
    filter_upwards [PhysMS.to_log_zoom.eventually_gt_atTop (0:ℝ),hb.positive] with r lg bp
    change LogV r*a r^2/(LogV r*b r^2)=(a r/b r)^2
    field_simp [lg.ne',bp.ne']
  filter_upwards [ha.positive,hb.positive,(ha.conforms simple).eventually (ge_mem_nhds
    (show (0:ℝ)<1/2 by norm_num)),rel'.eventually (ge_mem_nhds (show (1:ℝ)<4 by norm_num))]
    with r ap bp small amount
  have ratio:a r/b r≤2:=by nlinarith [sq_nonneg (a r/b r-2)]
  have compare: a r≤2*b r:=(div_le_iff₀ bp).mp ratio
  nlinarith only [compare,mul_le_mul_of_nonneg_left small ap.le]

variable {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {l:Ultrafilter (ℕ×ℕ)}{z:Arch R.family}{H:(Bel R.family.book).Hierarchy}

theorem aperture (simple:G.Simple)(bliss:Bliss F l z H){b:ℝ→ℝ}(link:Coupling G b)(A:ℕ){δ:ℝ}(dp:0<δ):
    ∀ᶠr in trail,0<r ∧ let t:=r/((b r)^A)^2
      r≤t ∧ t<δ ∧ t≤outer z (4*A) r:=by
  let law:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have short:∀ᶠr in trail,outer z (4*A) r<δ:=(longer F simple bliss (4*A)).eventually
    ((gt_mem_nhds dp).filter_mono nhdsWithin_le_nhds)
  filter_upwards [short,law.positive,link.positive,(link.conforms simple).eventually
    (ge_mem_nhds zero_lt_one),length_rate.pos,room simple law link] with r fit gp bp one rp compare
  have power:(wilson z r)^(4*A)≤((b r)^A)^2:=calc
    _ = (((wilson z r)^2)^A)^2:=by rw [←pow_mul,←pow_mul,show 4*A=2*(A*2) by omega]
    _ ≤ _:=pow_le_pow_left₀ (pow_nonneg (sq_nonneg _) _) (pow_le_pow_left₀ (sq_nonneg _) compare A) 2
  have lower:r≤r/((b r)^A)^2:=(le_div_iff₀ (sq_pos_of_pos (pow_pos bp _))).mpr
    (by simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ (pow_nonneg bp.le A) (pow_le_one₀ bp.le one) (n:=2)) rp.le)
  have upper:r/((b r)^A)^2≤outer z (4*A) r:=by
    rw [outer,inv_pow,←div_eq_mul_inv]
    exact div_le_div_of_nonneg_left rp.le (pow_pos gp _) power
  exact ⟨rp,lower,upper.trans_lt fit,upper⟩

end YM.Integration.WilsonMovingForkMeasuredWindow
