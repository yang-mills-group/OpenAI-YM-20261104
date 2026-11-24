import YM.QuadraticLocal.Fk.Maps
import YM.QuadraticLocal.Fk.Table

/-! Linearity in each distinct insertion BEFORE changing mesh. Applies
as well if each input letter is the finite sum of its copies at a larger
period. Includes the vacuum normalization. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset.LinearLetters
open Function Filter Finset Lattice RG Precision Tree YM.Wilson
open QuadraticLocal QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V ι : Type} {G : Gauge} {n c f : Side}

variable (F : Finset ι) (P₁ : ℝ → Config G f → ℝ)
    (L : ι → ℝ → Config G f → ℂ)
    [DecidableEq V] (R : Census V)
    (e : ι → Multi.Hot R) (q : ι → ℂ)
    (w : Multi.Hot R → ℕ)

def colors : Colors R G f := {
  vac := P₁, power := w
  mark i := ∑ j ∈ F.filter (fun j=> i.val=(e j).val), q j • L j }

local notation "S₁" => colors F P₁ L R e q w
variable {B : StepData c f} {P : Clip} {T : PathData G} {O : ChartRatio G}
variable (K : Kernel B P T O) (A : Forest B.ratio) (t : B.Choices) (U : Joint (G:=G) B A)
variable (weights : ι → ℕ) (he : ∀ i∈F, w (e i) = weights i)
    (hc : ∀ i∈F, ContDiffAt ℝ ω (Bulk.posed B A (L i)) 0)


set_option quotPrecheck false
include he hc
lemma mark_at (i : Multi.Hot R) (d : ℕ) :
    Assembly.markLetter (S₁).power (Bulk.markFn B A S₁) i U d =
      ∑ j∈F.filter (fun j=> i.val=(e j).val), q j * Assembly.jet
        (Bulk.posed B A (L j)) (weights j + d) U := by
  let H := F.filter (fun j=> i.val = (e j).val)
  let X j := Bulk.posed B A (q j • L j)
  have hX (j) (hj:j∈H) : ContDiffAt ℝ ω (X j) 0 :=
    (ContinuousLinearMap.contDiff (q j • (ContinuousLinearMap.id ℝ ℂ))).contDiffAt.comp
      (f:=Bulk.posed B A (L j)) 0 (hc j (mem_filter.mp hj).1)
  have hg : Bulk.markFn B A S₁ i = ∑ j∈H, X j := by
    funext v
    unfold colors X H Bulk.markFn Bulk.posed
    simp only [Finset.sum_apply]
  unfold Assembly.markLetter
  rw [hg]; nth_rw 1 [Assembly.jet]; rw [iteratedFDeriv_sum_apply
    (fun j hj=> (hX j hj).of_le le_top),_root_.sum_apply,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hy : (S₁).power i = weights j := (congr_arg w
    (show i=e j from Subtype.ext (mem_filter.mp hj).2)).trans (he _ (mem_filter.mp hj).1)
  rw [hy]
  exact (Assembly.jet_apply_left (q j • ContinuousLinearMap.id ℝ ℂ) (Bulk.posed B A (L j)) _
    ((hc j (mem_filter.mp hj).1).of_le le_top) _).symm

theorem wave (i : ℕ) : PowerSeries.coeff i (Assembly.affine (S₁).power
    (Bulk.markFn B A S₁) (Bulk.geometric K A t S₁) U) =
    Poly.bead R (Complex.ofReal (Assembly.vacuumLetter (Bulk.geometric K A t S₁) U i)) +
    ∑ j∈F, Poly.send (e j).val (q j * Assembly.jet (Bulk.posed B A (L j))
      (weights j + i) U) := by
  rw [Assembly.affine,map_add,Assembly.realCoeff,Assembly.curve,PowerSeries.coeff_mk]
  congr 1
  apply Marker.Poly.ext
  intro v
  rw [Poly.part_sum]
  by_cases hv : v=R.quiet
  · subst v
    simp only [part_lit_quiet, part_quiet_hot, Finset.sum_const_zero]
  let y : Multi.Hot R := ⟨v, (Cumulants.hot_iff_ne _).2 hv⟩
  rw [show (lit R (fun x=> Assembly.markLetter _ (Bulk.markFn B A S₁) x U i)).part v = _ from
    part_lit _ y, mark_at F P₁ L R e q w A U weights he hc]
  simp_rw [Finset.sum_filter,Poly.part_send]
  rfl

omit he hc

-- Basis calculation independent of amplitudes. Use W val mapped to weight
-- through stipulated grade at momentum expansion (offset in powers).
variable [DecidableEq ι] [Fintype ι]

abbrev edition (D : ι→ℕ) := colors F P₁ L (Focus.census ι) Focus.detailI 1
  (fun i=> (Launch.index (Focus.census ι) D i.val)+1)
local notation "C" => Focus.census ι
variable [Fintype V]

def gems (i : ι) : Poly R := Poly.send (e i).val (q i)
omit [DecidableEq ι] [Fintype ι] in
lemma zero_gems (i : ι) : gems R e q i * gems R e q i=0 := by rw [← sq,gems,Focus.no_merge]
local notation "Y₁" => TableMap.mapC (gems R e q) (zero_gems R e q)

variable (D : ι → ℕ) (hD : ∀ i∈F, w (e i) = D i + 1)
include hc hD
local notation "X'" => edition F P₁ L D
local notation "wj" => (fun i=> D i + 1)

private theorem affine_eq : PowerSeries.map (Y₁).toRingHom
    (Assembly.affine (X').power (Bulk.markFn B A X') (Bulk.geometric K A t X') U) =
    Assembly.affine (S₁).power (Bulk.markFn B A S₁) (Bulk.geometric K A t S₁) U := by
  ext1 k
  unfold edition
  rw [PowerSeries.coeff_map,wave F P₁ L _ _ _ _ K A t U wj (fun i _=> by rw [Focus.weight]) hc k,
    wave F P₁ L R e q _ K A t U wj hD hc k,_root_.map_add,_root_.map_sum]
  congr 1
  · exact (Y₁).commutes _
  refine Finset.sum_congr rfl fun i _=> ?_
  simp only [Pi.one_apply,one_mul]
  exact (TableMap.primitive (gems R e q) (zero_gems R e q) i _).trans
    ((send_scale _ _ _).symm.trans (congr_arg _ (mul_comm ..)))

theorem finite_mixing (x : Exterior.fieldDir G c 1) (k d : ℕ) :
    Order.observe R k (Order.logMarked (Bulk.Fk K A t S₁ x k)) d =
      TableMap.mapC (gems R e q) (zero_gems R e q) (Order.observe (Focus.census ι) k
        (Order.logMarked (Bulk.Fk K A t X' x k)) d) :=
  Morph.inspection Y₁ (fun x=> TableMap.unmarked _ _ x) K A X' S₁ t x
    (fun u=> affine_eq F P₁ L R e q w K A t u hc D hD) _

end YM.Integration.FVA1Physical.TwoReset.LinearLetters
