import YM.Integration.FVA1Physical.TwoReset.CopyLetters

/-! Clear rows are not removed. In Fk they just amount to a global marked
constant inside the regular log, already with the multiplicity of their copies. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {V ι α : Type} [DecidableEq V] {c f n : Side}
  {J : Passport n V} {R : Census V}
variable (h : n.val ∣ f.val) (M : ι→Row J R G α) (w : V→ℕ) (q : ι→ℂ)
    (L : Layout G) (T : Finset Age)
local notation "F0" => finiteColor h M w q L T
local notation "p" => Pages n f
variable {S : StepData c f} {P : Clip} {Y : PathData G} {O : ChartRatio G}
variable (K : Kernel S P Y O) (A : Forest S.ratio) (t : S.Choices) (x : Exterior.fieldDir G c 1)

include h
private lemma constant_jet (j:ι) (hh:(M j).clear) (k:ℕ) (z:Precision.Key A G→ℝ) :
    Assembly.jet (Bulk.posed S A (copiesLetter h M j)) ((M j).lamp.power+k)
      (Bulk.translated K A x z) = ↑(Pages n f)*Complex.ofReal
        ((M j).markReceipt k (0:Stationary.Link G n)) := by
  let f₁ := fun u:ℝ => Row.bearing (M j) 1 u
  have e : Bulk.posed S A (copiesLetter h M j) =
      (p:ℂ) • (f₁ ∘ Prod.fst) := by
    funext U
    unfold Bulk.posed copiesLetter
    rw [← pages h (M j).center (fun y=> Complex.ofReal (Loan.letter _ _ y _ _))]
    let u := (M j).center
    let V := (Work.F03.live A U.2)
    have hv(i:Fin p) : Complex.ofReal (Loan.letter (M j).lamp (M j).atom (page h u i).val U.1 V)= f₁ U.1 := by
      unfold Loan.letter f₁ Row.bearing
      rw [← Solo.ghost (M j) hh (M j).center (1:Config G n) (page h u i).val V,one_mul]
    change ∑ j':Fin p, Complex.ofReal (Loan.letter (M j).lamp (M j).atom (page h u j').val U.1 V) = _
    simp_rw [hv]
    rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; rfl
  let B : Bulk.Joint (G:=G) S A →L[ℝ] ℝ:= ContinuousLinearMap.fst ℝ ℝ _
  let Z := B
  have hB : ContDiffAt ℝ ω f₁ 0 := Row.breath ..
  let k':= (M j).lamp.power+k
  have he : Assembly.jet (f₁ ∘ Prod.fst : Bulk.Joint (G:=G) S A→ℂ) k' (Bulk.translated K A x z) =
      ↑((M j).markReceipt k (0:Stationary.Link G n)) := by
    have he: B (Bulk.translated K A x z)=1:= congr_arg Prod.fst (footing K A x z)
    change Assembly.jet (f₁∘B) _ _ = _
    rw [Assembly.jet_continuous_right B (hB.of_le le_top),he,show (Assembly.jet f₁ k' 1) = _ from
      Row.interest (M j) 1 _ hh (0:Stationary.Link G n), one_mul]
  rw [e,← he]
  apply (Assembly.jet_apply_left ((p:ℂ) • ContinuousLinearMap.id ℝ ℂ)
    (f₁ ∘ B) _ (_ : ContDiffAt ℝ _ _ _) _).symm
  exact (ContDiffAt.comp (g:=f₁) (f:=B) _ hB (contDiffAt_fst)).of_le le_top

variable [Fintype V]
local notation "weight" => (fun i:Multi.Hot R=> Launch.index R w i.val + 1)
local notation "watch" F:max => ScatterR.opening M F
local notation "clip" F:max => (Finset.filter (fun i:ι=> ¬(M i).clear) (F))
local notation "ℓ" F:max => ((Pages n f : ℕ) • ScatterR.axisTape M F q)
local notation "Kj" F:max => F0 F
local notation "affine" F:max => (Assembly.affine ( F0 F ).power
  (Bulk.markFn S A (F0 F)) (Bulk.geometric K A t (F0 F)))
local notation "wk" => (fun k:ι=> (M k).lamp.power)
local notation "wx" F:max k:max => Order.series R k (ℓ F)

omit [Fintype V] in
lemma copies_affine (F: Finset ι) (he : ∀ j∈F,(M j).lamp.toll=Launch.index R w (M j).mode)
    (z:Precision.Key A G→ℝ) :
    (affine F) (Bulk.translated K A x z) = ℓ F + (affine (clip F)) (Bulk.translated K A x z) := by
  have hV(j) (hj:j∈F) : weight (ScatterR.actor M j) = (M j).lamp.power := congr_arg (·+1) (he j hj).symm
  let Q := Bulk.translated K A x z
  ext1 i
  rw [LinearLetters.wave F (QuadraticLocal.Fk.money L T) (copiesLetter h M) R _ _ _ K A t Q wk hV
    (fun j _=> posed_copies_smooth h M A j) i, _root_.map_add,
    LinearLetters.wave (clip F) (QuadraticLocal.Fk.money L T) (copiesLetter h M) R _ _ _ K A t Q wk
      (fun j hj=> hV j (mem_filter.mp hj).1) (fun j _=> posed_copies_smooth h M A j) i,
    add_left_comm]
  apply congr_arg₂ (·+·) rfl
  let W (j:ι) := Poly.send (M j).mode (q j*Assembly.jet (Bulk.posed S A (copiesLetter h M j))
      ((M j).lamp.power+i) Q)
  change ∑ j∈F,W j= PowerSeries.coeff i (ℓ F)+∑ j∈clip F,W j
  have hg (j:ι) (hj:j∈watch F) : W j= p • ScatterR.drawing M q i j := by
    let x₀ := ScatterR.drawing M q i j
    have he' : p • ScatterR.drawing M q i j=(p:ℂ) • ScatterR.drawing M q i j :=
      (Nat.cast_smul_eq_nsmul ℂ p x₀).symm
    rw [he']
    unfold W ScatterR.drawing
    rw [constant_jet h M K A x j (mem_filter.mp hj).2 i z,← send_scale, mul_left_comm]
  rw [_root_.map_nsmul, ScatterR.axisTape, PowerSeries.coeff_mk,Finset.smul_sum,
    ← Finset.sum_congr (s₁:= watch F) rfl hg]
  exact (Finset.sum_filter_add_sum_filter_not ..).symm

omit h in
private lemma series_blank (F: Finset ι) (k:ℕ) : Order.denominator (wx F k)=0 := by
  rw [_root_.map_nsmul,Order.denominator,_root_.map_nsmul]
  rw [show Order.bottom R k (Order.series R k (ScatterR.axisTape M F q)) = 0 from
    ScatterR.deposits M F q,nsmul_zero]

variable [DecidableEq ι]
local notation "response" => LinearLetters.mixedTerm (QuadraticLocal.Fk.money L T) (copiesLetter h M) M q K A t x

theorem literal_finite_copy (F: Finset ι) (he : ∀ j∈F,(M j).lamp.toll=Launch.index R w (M j).mode)
    (r i : ℕ) (hi : i≤r) : Order.observe R r
      (Order.logMarked (Bulk.Fk K A t (F0 F) x r)) i =
      (∑ j∈watch F,p • ScatterR.drawing M q i j) +
        ∑ j∈ScatterR.lounge M F,(response r i j) := by
  let S' := (F0 (clip F))
  rw [show Order.logMarked (Bulk.Fk K A t (F0 F) x r) = wx F r + Order.logMarked
      (Bulk.Fk K A t S' x r) from
    Morph.regularize K A S' (F0 F) t x _ (series_blank (n:=n) (f:=f) M q F r)
      (fun z=> by rw [copies_affine h M w q L T K A t x F he z,_root_.map_add]),
    Order.observe_add,Order.observation R r (ℓ F) hi,_root_.map_nsmul,ScatterR.axisTape,
    PowerSeries.coeff_mk,Finset.smul_sum]
  let g₁ := LinearLetters.mix_clubs (clip F) (QuadraticLocal.Fk.money L T) (copiesLetter h M) M q w K A t x r i hi
      (fun j hj=> he j (mem_filter.mp hj).1) (fun j hj=> (mem_filter.mp hj).2)
      (fun j _=> posed_copies_smooth h M A j)
  change _ + Order.observe R r (Order.logMarked (Bulk.Fk K A t S' x r)) i = _
  have hF : ScatterR.lounge M F = ScatterR.lounge M (clip F) := (ScatterR.email ..).symm
  rw [hF]
  exact congr_arg (_ + ·) g₁
end YM.Integration.FVA1Physical.TwoReset
