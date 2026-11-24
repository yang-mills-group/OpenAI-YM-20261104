import YM.Integration.WilsonOriginalDecoderHaloRate
import YM.Integration.WilsonWeakBinaryClockField
import YM.Integration.WilsonPhysicalMarkedDefectPlaquetteChart
import YM.RG01.Vacuum.Flat

/-! Each actual ClockFace tile perturbs only the purchased room. The original
normalized positive posterior there costs at most twice its flat event price,
uniformly in both finite regulators and in the selected tile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalClockFacePosterior
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Next.Rank.Spindle Next.Rank.Perch
open PhysicalNext PhysicalNext.Repeat.Legato Stationary Exterior RG17
open Pressure
open scoped BigOperators Classical Matrix.Norms.Frobenius Topology
variable {G:Gauge}(R:Run G)
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "spring" => R.family.path.levels.clock.kernel.penalty

private theorem rooms (simple:G.Simple):∀ᶠ i in atTop,∀p:ℕ,
    ((Room (0:Site (R.family.side i p)) (sizeQ R.family i)).card:ℝ)≤(4*65^4)*(H i):=by
  have grow:=Next.Rank.Station.hat_rate R.family.path.levels simple
  filter_upwards [grow.eventually_ge_atTop (Real.exp 1),
    grow.eventually ((Real.isLittleO_pow_log_id_atTop (n:=16)).bound (by norm_num:0<(1:ℝ)))] with i big logPow
  intro p
  let x:=Real.log (H i)
  have hp:0<H i:=zero_lt_one.trans (R.family.path.levels.fits.delayed i)
  have hx:1≤x:=(Real.le_log_iff_exp_le hp).mpr big
  have h₂:=one_le_pow₀ hx (n:=2)
  have h₄:=one_le_pow₀ hx (n:=4)
  have small:x^16≤H i:=by simpa [x,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (zero_le_one.trans hx) 16),abs_of_pos hp,abs_of_nonneg (show 0≤Real.log (H i) from zero_le_one.trans hx)] using logPow
  have ceil:((M (H i)):ℝ)≤2*x^2:=(Nat.ceil_lt_add_one (sq_nonneg x)).le.trans (by linarith only [h₂])
  have radius:((sizeQ R.family i):ℝ)≤32*x^4:=by
    change ((8*(M (H i))^2:ℕ):ℝ)≤_
    push_cast
    calc _≤8*(2*x^2)^2:=by gcongr
         _=_:=by ring
  have card:=broad (0:Site (R.family.side i p)) (sizeQ R.family i)
  calc _ ≤ (((sizeQ R.family i:ℝ)+(sizeQ R.family i:ℝ)+1)^4*4):=by exact_mod_cast card
       _ ≤ (65*x^4)^4*4:=by gcongr;linarith only [radius,h₄]
       _ = (4*65^4)*(x^16):=by ring
       _ ≤ _:=mul_le_mul_of_nonneg_left small (by norm_num)

theorem original (simple:G.Simple):∀ᶠ i in atTop,∀{N per d:ℕ}(_live:i<N)
    (face:ClockFace R d i N per)(a:(R.family.labels.level d).Index),
    let W:=net (R.family.path.rep N per i).p 0 (sizeQ R.family i) (face.tiles a).val
    (Real.exp (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op i per)
      (R.family.path.β N per (i+1)) W))^2≤2:=by
  obtain ⟨C,δ,cp,dp,lip⟩:=WilsonPhysicalMarkedDefect.PlaquetteChart.slope G
  have grow:=Next.Rank.Station.hat_rate R.family.path.levels simple
  have logtwo:0<Real.log 2:=Real.log_pos (by norm_num)
  let M₀:ℝ:=16*spring*C*(4*65^4)
  filter_upwards [rooms R simple,RG01.Vacuum.Flat.nextComparable R.family.path.levels simple,
    grow.eventually_ge_atTop δ⁻¹,grow.eventually_ge_atTop (M₀/Real.log 2)] with i cap adjacent onset room
  intro N per d live face a W
  let β:=R.family.path.β N per (i+1)
  let point:=(R.family.path.rep N per i).p
  let x:=(face.tiles a).val
  let Z:=Room (0:Site (R.family.side i per)) (sizeQ R.family i)
  have hp:1≤H i:=(R.family.path.levels.fits.delayed i).le
  have pos:0<H i:=zero_lt_one.trans_le hp
  have fee:(H i^6)⁻¹≤(H i)⁻¹:=inv_anti₀ pos (le_self_pow₀ hp (by norm_num))
  have hd:(H i^6)⁻¹≤δ:=fee.trans ((inv_le_comm₀ pos dp).mpr onset)
  have cost:∀e∈Z,G.chord (W e)≤C*(H i^6)⁻¹:=by
    intro e he
    have ht:‖point.threshold • x ⟨e,he⟩‖≤(H i^6)⁻¹:=by
      rw [norm_smul,Real.norm_of_nonneg point.threshold_pos.le]
      exact (mul_le_of_le_one_left (norm_nonneg _) point.threshold_le).trans
        ((norm_le_pi_norm x _).trans (face.tiles a).property)
    change G.chord (net point 0 (sizeQ R.family i) x e) ≤ _
    rw [show net point 0 (sizeQ R.family i) x e=G.lieExp (point.threshold • x ⟨e,he⟩) from net_in point x ⟨e,he⟩]
    exact (lip _ (ht.trans hd)).trans (mul_le_mul_of_nonneg_left ht cp.le)
  have sum:∑e:Bond (R.family.side i per),G.chord (W e)≤(4*65^4)*(H i)*(C*(H i^6)⁻¹):=by
    calc _=∑e∈Z,G.chord (W e):=by
             symm
             apply Finset.sum_subset (Finset.subset_univ _)
             intro e _ miss
             change G.chord (net point 0 (sizeQ R.family i) x e)=0
             rw [net_out point x e miss,G.chord_one]
         _≤∑_∈Z,C*(H i^6)⁻¹:=Finset.sum_le_sum cost
         _≤_:=by rw [Finset.sum_const,nsmul_eq_mul];gcongr;exact cap per
  have bp:0<β:=Overlay.beta_positive R.makes.wilson live
  have bband:β≤2*H (i+1):=(R.makes.wilson.represents N per (i+1) live).band.2
  have cash:|β|≤4*H i:=by rw [abs_of_pos bp];linarith only [bband,adjacent]
  let bill:=WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op i per) β W
  have pen:=R.family.path.levels.clock.kernel.penalty_pos
  have nonnegative:0≤∑e:Bond (R.family.side i per),G.chord (W e):=Finset.sum_nonneg (fun e _=>G.chord_nonneg (W e))
  have reduced:2*bill≤M₀/(H i)^4:=by
    change 2*(|β| *(2*spring*∑e:Bond (R.family.side i per),G.chord (W e)))≤_
    calc _≤2*((4*H i)*(2*spring*((4*65^4)*(H i)*(C*(H i^6)⁻¹)))):=by
              gcongr
         _=_:=by dsimp only [M₀];field_simp [pos.ne'];ring
  have decay:M₀/(H i)^4≤Real.log 2:=by
    apply (div_le_iff₀ (pow_pos pos 4)).mpr
    exact ((div_le_iff₀ logtwo).mp room).trans
      (by rw [mul_comm];exact mul_le_mul_of_nonneg_left (le_self_pow₀ hp (by norm_num)) logtwo.le)
  change (Real.exp bill)^2≤2
  rw [←Real.exp_nat_mul,←Real.exp_log (by norm_num:0<(2:ℝ))]
  apply Real.exp_le_exp.mpr
  exact reduced.trans decay

end YM.Integration.WilsonOriginalClockFacePosterior
end
