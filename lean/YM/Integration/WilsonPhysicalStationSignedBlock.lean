import YM.Integration.WilsonPhysicalStationFiledHead
import YM.Trace.Physicalv2.GermPrices

/-! Signed diagonal blocks of the original deposited Vane, with its unscaled unit
and the original period-uniform measured germ expense. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationSignedBlock
open Filter Function RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open YM.MergeProof YM.MergeProof.Ribbons
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph WilsonPhysicalStationFiledHead
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}{D:ℕ}
  (V:Vane R.family D)(j:Fin (D+1))(w:(Bel R.family.book).Field j)

def scale (N p h b:ℕ):ℂ:=
  ((shrink R.family V.k N p)⁻¹:ℝ)^b*((Next.Rank.Station.mag R.family.path.levels V.b V.k:ℝ):ℂ)^h

theorem pure {N p h b:ℕ}(checked:V.checked f H D)(top:V.k<N)
    (mono:∀i,(Further.CorrectedLift.ladder R.family j w) i≠0 → (R.family.labels.level j).grades i=(h,b)):
    (R.family.labels.level j).coeffSize ((scale R V N p h b)⁻¹ • vote R V j w N p-
      Further.CorrectedLift.ladder R.family j w) ≤
      fee R j V.k p*(2*(R.family.labels.level j).coeffSize (Further.CorrectedLift.ladder R.family j w)):=by
  let a:=shrink R.family V.k N p
  let ρ:=Next.Rank.Station.mag R.family.path.levels V.b V.k
  let y:=Further.CorrectedLift.ladder R.family j w
  let ξ:=scale R V N p h b
  have ap:0<a:=shrink_pos R.family R.makes top.le p
  have rp:0<ρ:=Real.rpow_pos_of_pos (Real.exp_pos _) _
  have ξ0:ξ≠0:=by
    change (((a⁻¹:ℝ):ℂ)^b)*(ρ:ℂ)^h≠0
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (inv_ne_zero ap.ne')))
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr rp.ne'))
  have tab:tagged R V j w N p=ξ • y:=by
    funext i
    change Complex.ofReal (a⁻¹ ^ ((R.family.labels.level j).grades i).2)*(((ρ:ℂ)^((R.family.labels.level j).grades i).1)*y i)=ξ*y i
    by_cases live:y i=0
    · simp [live]
    · rw [mono i live]
      change Complex.ofReal (a⁻¹ ^ b)*(((ρ:ℂ)^h)*y i)=((((a⁻¹:ℝ):ℂ)^b)*((ρ:ℂ)^h))*y i
      push_cast
      ring
  have debt:=WilsonPhysicalStationFiledHead.original R V j w (p:=p) checked top
  rw [tab] at debt
  let F:=R.family.labels.level j
  have abs (z:ℂ)(v:R.family.label j):F.coeffSize (z • v)=‖z‖*F.coeffSize v:=by
    simp [Frame.coeffSize,Finset.mul_sum,Pi.smul_apply]
  have rearr:ξ⁻¹ • vote R V j w N p-y=ξ⁻¹ • (vote R V j w N p-ξ • y):=by
    rw [smul_sub,smul_smul,inv_mul_cancel₀ ξ0,one_smul]
  change F.coeffSize (ξ⁻¹ • vote R V j w N p-y)≤_
  rw [rearr,abs]
  rw [abs] at debt
  calc
    _ ≤ ‖ξ⁻¹‖*(fee R j V.k p*(2*(‖ξ‖*F.coeffSize y))):=mul_le_mul_of_nonneg_left debt (norm_nonneg _)
    _ = _:=by rw [norm_inv];field_simp [norm_ne_zero_iff.mpr ξ0];rfl

theorem uniform (simple:G.Simple)(ε:ℝ)(ep:0<ε):
    ∀ᶠk:ℕ in atTop,∀p,fee R j k p≤ε:=by
  let w:=price (C:=R.family) j
  have wp:0<w:=mul_pos (by exact_mod_cast (Nat.zero_lt_succ _)) (Trace.Physical.Germ.germ_close _ _).choose_spec.1
  have half:0<ε/2:=half_pos ep
  have letter:=((Note.notes R.family.S w wp).mills (Ribbons.fuNote R.family)).mills (Note.bell_exp R.family.S (-1))
  have small:Tendsto (fun k=>Perch.bill (-1/2) (R.family.path.levels.clock.hatBeta k)) atTop (𝓝 0):=
    (Perch.bill_hi (by norm_num)).comp (Next.Rank.Station.hat_rate R.family.path.levels simple)
  filter_upwards [letter.outweigh (Note.notes R.family.S (ε/2) half) (by norm_num),
    cut_flat R.family simple (-1),(tendsto_order.mp small).2 _ half] with k cols cut bill p
  change w*stock R.family k*Real.exp (-1*R.family.S.scale k)≤ε/2 at cols
  have rent:invoice (C:=R.family) j k p*stock R.family k≤ε/2:=by
    calc
      _ ≤ w*Real.exp (-1*R.family.S.scale k)*stock R.family k:=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (cut p) wp.le) (zero_le_one.trans (stage R.family k).columns_ge)
      _ = _:=by ring
      _ ≤ _:=cols
  exact (add_le_add rent bill.le).trans_eq (by ring)

end YM.Integration.WilsonPhysicalStationSignedBlock
