import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Inclusions
import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Scale
/-! # Bounded-horizon fixed physical fields vs incoming H reading (G.6)

Basis for payments only. Weight pricing: expansion uses own grade of
individual terms (G.2 polynomial charge per entry). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Climb Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS
open FVA2.Scale Comparing O.Score O.Enh Dframe ScaleCost
open Matrix Flash259HorizonFork
open scoped Topology BigOperators Classical Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S)
    {N : WilsonPrescription G} {ν : ℝ}
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {sim : G.Simple}
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
    {t : ℝ→ℝ} (hZ : Leading F Z) (hq : ∀ d, FieldQuote G (GroupS.gaugeN N.scheme N.criterion M ν) t (via Z) d 1)
    {d : ℕ}
local notation "A" => ScaleCost.value (via Z)
local notation "L" => F.sector.derivatives
variable {I J : Type} {l : Filter J} {s r : J→ℝ}
    (hr:Tendsto r l late) (hs : Tendsto s l late) (he:∀ᶠ i in l,r i ≤ s i)

-- Buy log prices with the same orientation as ScaleCost.
include hr hs he in
lemma piggy {g:ℝ→ℝ} (e:Income g) : Allowance l r (fun _=>1) (g ∘ s) := by
  obtain ⟨k,u⟩:=e
  refine ⟨k,(u.comp_tendsto hs).trans (IsBigO.of_bound' ?_)⟩
  filter_upwards [he,log_pays hr, hs.eventually (holds_cash.eventually_gt_atTop 0),hr.eventually self_mem_nhdsWithin] with i hi hl hs hr
  change ‖cash (s i)^k‖ ≤ ‖1*OPE.Log.badge (r i)^k‖; rw [one_mul,norm_pow,norm_pow,Real.norm_of_nonneg hs.le,Real.norm_of_nonneg (zero_le_one.trans hl)]; apply pow_le_pow_left₀ hs.le _ _
  rw [ScaleCost.cash,Real.log_inv,OPE.Log.badge,OPE.run]; linarith only [Real.log_le_log hr hi]
lemma stamp (r t:ℝ) : IsUnit (Matrix.det (ScaleCost.value (via Z) d t r)) := by
  let U := columns (via Z t r d)
  have h : ScaleCost.value (via Z) d t r * (engine G d (Real.log r)*U)=1:= by
    unfold ScaleCost.value; rw [mul_assoc, ← mul_assoc _ _ U,ScaleCost.forward, neg_add_cancel,origin,one_mul]
    unfold U; rw [composition', ← show via Z r r d= via Z r t d ∘ₗ via Z t r d from checks Z r t r d, reflexive Z, one_matrix]
  apply isUnit_iff_ne_zero.mpr
  intro hz; replace h:= congr_arg Matrix.det h; rw [ Matrix.det_mul,hz,zero_mul,Matrix.det_one] at h; exact zero_ne_one h

-- Column conversion from any fixed basis of a late enough fixed home.
lemma cash_word (u : Sec G d) (r s:ℝ) (h:0< r) (b:Toon G d) :
    coord b (via Z s r d u)= (r:ℂ)^b.size*((ScaleCost.value (via Z) d s r)⁻¹ *ᵥ numbers u) b := by
  -- prove `A_d(r) diag_r = V(r)` and so r^{-w} x = V^-1 u
  let y:= via Z s r d u; let T:= engine G d (-Real.log r); let V:=ScaleCost.value (via Z) d s r
  let q:=engine G d (Real.log r) *ᵥ numbers y
  have he: T*ᵥ q=numbers y := by unfold q T; rw [mulVec_mulVec,ScaleCost.forward, neg_add_cancel,origin,one_mulVec]
  have i : V*ᵥ q=numbers u := by
    unfold V ScaleCost.value; rw [←mulVec_mulVec,he, Comparing.issued]
    congr 1; change via Z r s d y=_; unfold y; rw [← Module.End.mul_apply,← checks Z r s r d,reflexive Z]; rfl
  rw [←i,mulVec_mulVec,nonsing_inv_mul V (stamp Z r s),one_mulVec]
  change numbers y b=_; rw [←he]
  change (T *ᵥ q) b=_
  unfold Matrix.mulVec dotProduct T; simp [gear_cost,h,Real.exp_log]

include H hq hZ hr
lemma free_label (z:S.Field d) (b : Toon G d) : Allowance l r (fun i=>(r i)⁻¹^d)
    (fun i=> coord b ((frame Z (r i) d).symm z)) := by
  let y(s:ℝ):= (frame Z s d).symm z; let v(s:ℝ):= numbers (y s)
  have q := ScaleCost.safe sim v ((H.dilation ν).check) t (fun s=> ScaleCost.linear sim N ν M H s) (hq d)
    (Eventually.of_forall fun s T _ _=> Eq.symm ((Comparing.issued (via Z s (s*T) d) (y (s*T))).trans (congr_arg numbers (by rw [shift]; unfold y; rw [LinearEquiv.apply_symm_apply]))))
  obtain ⟨C,hC,k,h⟩:= Allowance.budget hr (piggy (s:=r) hr hr (Eventually.of_forall fun _=>le_rfl) q) (Eventually.of_forall fun _=> zero_le_one)
  refine ⟨k,IsBigO.of_bound C ?_⟩; filter_upwards [h,hr.eventually self_mem_nhdsWithin,log_pays hr] with i hi e l
  have p : 0 < r i := e; have v' : 0 ≤ tallyZ (v (r i)):=Finset.sum_nonneg fun j _=> norm_nonneg _
  rw [Real.norm_of_nonneg (by positivity)]
  refine (Finset.single_le_sum (f:=fun j : Toon G d=> ‖v (r i) j‖) (fun j _=>norm_nonneg _) (Finset.mem_univ b)).trans ?_
  change ‖r i^d * tallyZ (v (r i))‖ ≤ _ at hi; rw [Real.norm_of_nonneg (by positivity), mul_one] at hi
  rw [inv_pow,←div_eq_inv_mul,←mul_div_assoc,le_div_iff₀ (by positivity)]; exact mul_comm .. |>.le.trans hi

end YM.FVA2.GradedFar259.Original
