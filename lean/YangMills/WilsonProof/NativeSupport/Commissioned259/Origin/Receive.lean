import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Legacy
/-! # A field-horizon-robust booking argument inside Flash259HorizonFork

Transfer genuine H fields to fixed physical using polylog costs G.2, at their own weight caps
anchored at any used late anchor. Uses exact eventual cap inclusion of physical H, &
fixed cap pricing arguments (`estuary` purchases here, as exercised on Flash259HorizonFork).
No changing Far arms after expanding in Q's actual prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Climb Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS
open FVA2.Scale Comparing O.Score O.Enh Dframe ScaleCost Matrix Flash259HorizonFork
open scoped Topology BigOperators Classical Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S)
    {N : WilsonPrescription G} {ν : ℝ}
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {sim : G.Simple}
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
    {t : ℝ→ℝ} (hZ : Leading F Z) (hq : ∀ d, FieldQuote G (GroupS.gaugeN N.scheme N.criterion M ν) t (via Z) d 1)

variable {I J : Type} {l : Filter J} {s r : J→ℝ} (hr:Tendsto r l late)
    (hs : Tendsto s l late) (he : ∀ᶠ i in l,r i ≤ s i) {d:ℕ}
include hr hs he
lemma column_budget (u:J→ Sec G d)(b: Toon G d)(a:ℝ) (h:Income (fun i=>stiffness (ScaleCost.value (via Z) d a i)⁻¹))
    (hu:∀ i,Allowance l r (fun _=>1) (fun j=>coord i (u j))) :
    Allowance l r (fun i=>s i ^ b.size) (fun i=>coord b (via Z a (s i) d (u i))) := by
  let P (i:J): Operator G d := (ScaleCost.value (via Z) d a (s i))⁻¹
  have i (j:Toon G d) : Allowance l r (fun _=>1) (fun k=> P k b j) := by
    refine (piggy hr hs he h).travels (IsBigO.of_bound' (Eventually.of_forall fun i=> ?_))
    exact (leanFee _ _ _).trans_eq (Real.norm_of_nonneg (stiffPos _)).symm
  refine (Allowance.mul (Allowance.covers (f:=fun i=> (s i:ℂ)^b.size) (w:=fun i=>s i^b.size) ?_)
      (Allowance.sum (w:=fun _=>1) hr (Finset.univ:Finset (Toon G d)) (fun j i=> P i b j * numbers (u i) j) (fun j _=>?_))).congr ?_ |>.extend ?_
  · exact IsBigO.of_bound' (Eventually.of_forall fun i=>by simp only [norm_pow, Complex.norm_real]; rfl)
  · refine (Allowance.mul (i j) (hu j)).extend ?_; exact Eventually.of_forall fun _=>one_mul _
  · filter_upwards [hs.eventually self_mem_nhdsWithin] with i hi; exact Eq.symm (cash_word Z (u i) _ _ hi b)
  exact Eventually.of_forall fun _=>mul_one _

-- families of measurements
abbrev enter {d:I→ℕ} (r:ℝ)(u:(i:I) → Sec G (d i)) : Orbits.Labels S d := fun i=> frame Z r (d i) (u i)
omit hr hs he in
lemma beacon (v : Sec G d) (a s:ℝ) : frame Z s d v = ∑ b : Toon G d, coord b (via Z a s d v) • frame Z a d (theory b) := by
  simp_rw [← _root_.map_smul,← map_sum]
  rw [show (∑ b:Toon G d, coord b (via Z a s d v) • theory b) = via Z a s d v from all_sig _, shift, LinearEquiv.apply_symm_apply]
include H hZ hq

set_option maxHeartbeats 700000 in
/-- We do expansions for §G in one or *both* sets of arguments, for any family being priced,
allowances on uniform filters on ALL these layouts. Buy asymptotic polynomials independent of the
upper T in `Wage`. Precisely, compiler only needs expenditures already paid on **fixed fields**
(as in earlier physical estimates), with the prescribed caps. Unit inputs in Sec. -/
lemma receiving {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype I]
    (d : I→ℕ) (X:J→ Oper (E:=E) S d) (u:J→(i:I)→Sec G (d i)) {w:J→ℝ}
    (paid:∀ d' : I→ℕ, ∀ h:d' ≤ d, ∀ v:Labels S d', Allowance l r (fun i=> w i/(s i)^(∑ j,d' j))
      (fun i=> X i (promote F h v)))
    (hu:∀ (i:I) (b:Toon G (d i)), Allowance l r (fun _=>1) (fun j=> coord b (u j i))) :
    Allowance l r w (fun i=> X i (enter Z (s i) (u i))) := by
  choose a heights costs using fun i:I=> (((height hZ (d i)).and (before Z H hZ hq (d i))).exists)
  let U (j:J) (i:I) b := coord b (via Z (a i) (s j) (d i) (u j i))
  let Y := (i:I)→ Toon G (d i)
  haveI : Fintype Y := inferInstanceAs (Fintype ((i:I)→ Toon G (d i)))
  let w' (b:Y) (i:I) := (b i).size
  let E0 (b:Y) (i:I) := frame Z (a i) (w' b i) (theory (O.Score.grab (flash (b i))))
  have hV (b:Y) : w' b ≤ d := fun i=> size_le (b i)
  let V (b:Y) := promote F (hV b) (E0 b)
  have hi (b:Y) (i:I) : frame Z (a i) (d i) (theory (b i))=V b i := by
    let e:=heft (flash (b i)); have hc : e ≤ d i:=size_le (b i)
    exact heights i e hc (theory (O.Score.grab (flash (b i))))
  have hv b : Allowance l r w (fun i=> (∏ j, U i j (b j)) • X i (V b)) := by
    refine (Allowance.smul (Allowance.prod _ (fun j (_:j∈(Finset.univ:Finset I)) => column_budget Z hr hs he (fun i=>u i j) (b j) (a j) (costs j).2 (hu j)))
      (paid (w' b) (hV b) (E0 b))).extend ?_
    filter_upwards [hs.eventually self_mem_nhdsWithin] with i h
    rw [Finset.prod_pow_eq_pow_sum]
    exact mul_div_cancel₀ (w i) (show s i ^ (∑ j, w' b j) ≠ 0 from (pow_pos h _).ne')
  refine (Allowance.sum hr Finset.univ _ (fun j _=> hv j)).congr (Eventually.of_forall fun i=>?_); symm
  change X i (enter Z (s i) (u i))=_
  rw [show enter Z (s i) (u i)=(fun k=>∑ b, U i k b • frame Z (a k) (d k) (theory b)) from funext (fun k=>beacon Z _ (a k) _)]
  refine ((X i).map_sum (fun k b=> U i k b • frame Z (a k) (d k) (theory b))).trans (Finset.sum_congr (by ext; simp only [Finset.mem_univ]) (fun j _=>?_))
  rw [MultilinearMap.map_smul_univ,show (fun k=> frame Z (a k) (d k) (theory (j k)))= V j from funext (fun i=> hi j i)]
end YM.FVA2.GradedFar259.Original
