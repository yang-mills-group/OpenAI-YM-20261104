import YM.Integration.WilsonThermometerWeakMixedAlcove
import YM.Integration.WilsonMixedTaggedEntries
import YM.MergeProof.South.Window

/-! Project the amplified physical array only after an arbitrary number of genuine older Wilson integrations. Each surviving term has the same original occupied set. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMixedFaces
open Function MeasureTheory Finset Lattice Wilson RG Marker MergeProof.Accent Push RG05Readout.Many
open WilsonMixedTaggedRoster WilsonMixedTaggedOutput WilsonMixedTaggedPrice WilsonMixedTaggedEntries
open scoped Topology Classical BigOperators

variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] (B:Census V)

theorem row (z:ℂ) (a:Poly (census B)) (s:B.Mode) :
    (specialize B z a).part s = ∑ i:(census B).Mode,
      if s=base i then (∏ v∈i.val,weight Prod.snd z v)*a.part i else 0 := by
  change (∑ i:(census B).Mode, move (census B) B Prod.fst i ((YM.Multi.dilation (census B) (weight Prod.snd z) a).part i)).part s=_
  rw [Poly.part_sum]
  refine Finset.sum_congr rfl fun i _=>?_
  have admitted : Lit B Prod.fst i.val := (Finset.mem_filter.mp i.property).2
  rw [move,dif_pos admitted,Poly.part_send,YM.Multi.dilation_part]
  rfl

theorem bill {z:ℂ} (hz:‖z‖ ≤ 1) (a:Poly (census B)) (s:B.Mode) :
    ‖(specialize B z a).part s-(specialize B 0 a).part s‖ ≤
      ‖z‖*∑ i:(census B).Mode, if s=base i then ‖a.part i‖ else 0 := by
  rw [row,row,← Finset.sum_sub_distrib,Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _=>?_)
  by_cases h:s=base i
  · rw [if_pos h,if_pos h,if_pos h,← sub_mul,norm_mul]
    exact mul_le_mul_of_nonneg_right (product_difference Prod.snd hz i.val) (norm_nonneg _)
  · simp [h]

theorem toll (w:V→ℝ) (i:(census B).Mode) :
    Poly.toll (w ∘ Prod.fst) i = Poly.toll w (base i) := by
  change (∏ v∈i.val,w v.1)=∏ v∈i.val.image Prod.fst,w v
  have admitted : Lit B Prod.fst i.val := (Finset.mem_filter.mp i.property).2
  rw [Finset.prod_image admitted.2]

variable {j N p:ℕ}

theorem transported (F:RG.History G) (z:ℂ) (Z:Config G (F.S.side j p) → Poly (census B))
    (live:Integrable Z (prior G _)) {k:ℕ} (hk:k ≤ j) :
    gust F N p j (fun U=>specialize B z (Z U)) k hk =
      fun W=>specialize B z (gust F N p j Z k hk W) := by
  let A := ((specialize B z).toLinearMap.restrictScalars ℝ).toContinuousLinearMap
  induction hk using Nat.decreasingInduction with
  | self => simp only [gust_base]
  | of_succ m hm IH =>
    rw [gust_step F N p j _ hm]
    simp_rw [IH]
    rw [gust_step F N p j Z hm]
    funext W
    let f:=gust F N p j Z (m+1) hm
    have int:=StepData.push_slice (F.levels.transition_mass m p (F.β N p (m+1))) W f (gust_live _ _ _ _ _ live hm)
    have paid:=A.integral_comp_comm int
    simp_rw [A.map_smul] at paid
    exact paid

theorem earlier (F:RG.History G) {Z:Config G (F.S.side j p) → Poly (census B)}
    {X E:Config G (F.S.side j p) → Poly B} {δ:ℝ} (pos:0 ≤ δ) (small:δ ≤ 1)
    (live:Integrable Z (prior G _)) (fitted:∀U,specialize B (δ:ℂ) (Z U)=X U)
    (erased:∀U,specialize B 0 (Z U)=E U) {k:ℕ} (hk:k ≤ j) (W:Config G (F.S.side k p)) (s:B.Mode) :
    ‖(gust F N p j X k hk W).part s-(gust F N p j E k hk W).part s‖ ≤
      δ*∑ i:(census B).Mode, if s=base i then ‖(gust F N p j Z k hk W).part i‖ else 0 := by
  rw [← funext fitted,← funext erased,transported B F (δ:ℂ) Z live hk,transported B F 0 Z live hk]
  have normδ:‖(δ:ℂ)‖=δ := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg pos]
  simpa only [normδ] using bill B (z:=(δ:ℂ)) (normδ.trans_le small) (gust F N p j Z k hk W) s

end YM.Integration.WilsonThermometerWeakMixedFaces
end
