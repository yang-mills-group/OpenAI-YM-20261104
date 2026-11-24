import YM.Integration.WilsonPhysicalHistoryRetainedSpringSite

/-! The full physical quadratic and cubic/quartic angular sources at one actual
site, with the original row budget and every signed orientation. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice Wilson RG Precision MeasureTheory
open scoped Topology BigOperators Classical
variable {G : Gauge} {n : Side} {B : Clip} {K : PathData G} {σ A Λ : ℝ}

def quadraticAt (B : Clip) (K : PathData G) (x : Site n) (U : Config G n) : ℝ :=
  ∑ a : PlaqAxes, (B.direct*G.price (faceValue U (x,a))+‖K.ell U (x,a)‖^2/2)

def secondAt (B : Clip) (K : PathData G) (x : Site n) (U : Config G n) : ℝ :=
  Patch.average fun s : Signed=>quadraticAt B K x (pull s 0 U)

def interactionAt (K : PathData G) (x : Site n) (U : Config G n) : ℝ :=
  sitePacket K.cubic x U+sitePacket K.quartic x U

def quadraticBill (B : Clip) (A : ℝ) : ℝ :=
  Fintype.card PlaqAxes*(|B.direct| *2+(A*2)^2/2)

theorem bare_sites (B : Clip) (K : PathData G) (U : Config G n) :
    secondTerm B K U=∑ x : Site n, secondAt B K x U ∧
    interaction K U=∑ x : Site n,interactionAt K x U ∧
    mainTerm B K U=∑ x : Site n, (secondAt B K x U+interactionAt K x U) := by
  have hs : secondTerm B K U=∑ x : Site n,secondAt B K x U := by
    unfold secondTerm quadratic secondAt quadraticAt Patch.average
    simp only [Fintype.sum_prod_type]
    rw [←Finset.mul_sum,Finset.sum_comm]
  have hi : interaction K U=∑ x : Site n,interactionAt K x U := by
    unfold interaction interactionAt
    rw [show Patch.average (fun h : Signed=>uncut K.cubic (pull h 0 U)+uncut K.quartic (pull h 0 U))=
      Patch.average (fun h : Signed=>uncut K.cubic (pull h 0 U))+
        Patch.average (fun h : Signed=>uncut K.quartic (pull h 0 U)) from by
          simp only [Patch.average,Finset.sum_add_distrib,mul_add]]
    rw [packet_sites K.cubic,packet_sites K.quartic,Finset.sum_add_distrib]
  refine ⟨hs,hi,?_⟩
  rw [Finset.sum_add_distrib,←hs,←hi,←curvature_pair B]
  ring

private theorem row_price (h : K.Bounds B σ A Λ) (p : Face (Per n)) (U : Config G n) :
    ‖K.ell U p‖≤A*2 := by
  let b:=fun i : ℕ=> |(K.row p.2 i).1| *Real.exp (σ*(K.row p.2 i).2.length)
  have hs : Summable (fun i=>b i*2):=(h.rows p.2).2.1.mul_right _
  have bound (i : ℕ) : ‖K.ellTerms p i U‖≤b i*2 := by
    rw [PathData.ellTerms,norm_smul,Real.norm_eq_abs]
    apply mul_le_mul ?_ (Slot.eval_norm ..) (norm_nonneg _) ((h.rows p.2).1 i)
    exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg h.width.le (by positivity)))
  have summ:=Summable.of_nonneg_of_le (fun i=>norm_nonneg _) bound hs
  apply (norm_tsum_le_tsum_norm summ).trans ((summ.tsum_le_tsum bound hs).trans ?_)
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right (h.rows p.2).2.2 (by norm_num)

theorem bare_site_price (h : K.Bounds B σ A Λ) (x : Site n) :
    Measurable (secondAt B K x) ∧ (∀ U, ‖secondAt B K x U‖≤quadraticBill B A) ∧
    Measurable (interactionAt K x) ∧ (∀ U,‖interactionAt K x U‖≤24*A) := by
  have raw : Measurable (quadraticAt B K x) := by
    unfold quadraticAt
    apply Finset.measurable_sum
    intro a _
    have ff : Measurable (fun U : Config G n=>G.price (faceValue U (x,a))) := by unfold faceValue; fun_prop
    exact (measurable_const.mul ff).add (((K.ell_meas (x,a) B σ A Λ h).norm.pow_const 2).div_const 2)
  have hb (U : Config G n) : ‖quadraticAt B K x U‖≤quadraticBill B A := by
    unfold quadraticAt
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ _ : PlaqAxes, (|B.direct| *2+(A*2)^2/2) := by
        apply Finset.sum_le_sum
        intro a _
        apply (norm_add_le ..).trans
        rw [norm_mul,Real.norm_eq_abs B.direct,Real.norm_of_nonneg (G.price_range _).1,
          Real.norm_of_nonneg (by positivity : 0≤‖K.ell U (x,a)‖^2/2)]
        exact add_le_add (mul_le_mul_of_nonneg_left (G.price_range _).2 (abs_nonneg _))
          (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (row_price h (x,a) U) 2) (by norm_num))
      _ = _ := by simp [quadraticBill,mul_add]
  obtain ⟨mc,bc⟩:=site_packet K.cubic h.width h.three x
  obtain ⟨mq,bq⟩:=site_packet K.quartic h.width h.four x
  refine ⟨measurable_const.mul (Finset.measurable_sum _ fun s _=>raw.comp (continuous_pull s 0).measurable),
    fun U=>mean_bound _ _ (fun s=>hb (pull s 0 U)),mc.add mq,?_⟩
  intro U
  exact (norm_add_le ..).trans ((add_le_add (bc U) (bq U)).trans_eq (by ring))

end YM.Integration.OriginalMarkedRunAction
