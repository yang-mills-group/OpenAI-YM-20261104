import YM.Integration.WilsonCenteredCapturePush

/-! The funded native hard array can be summed with its owner still named
and its true field and quiet weights unchanged. This licenses regrouping
the complete original geometric alternatives after filing. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredActualHardSum
open Finset Function Lattice RG Wilson Push.Local Planned.GuardedAtom
open WilsonCenteredCaptureCensus WilsonCenteredCapturePush WilsonCenteredCaptureSlots
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {P : Rep G n}

theorem absolute {f : ℕ → Config G n → ℂ} {a v : ℝ}
    (budget : ForceCost P.p P.activities f a) (hard : P.activities.KBound P.p v) (U : Config G n) :
    Summable (fun t : Push.Local.Pointed => ‖pointValue P.p P.activities f U t‖) := by
  obtain ⟨e,paid,cap⟩ := budget
  obtain ⟨k,summ,kb⟩ := Activities.K_total hard
  let g (i : ℕ) := e i+k i
  have pos (i) : 0 ≤ g i := add_nonneg (cap i).1 (kb i).1
  have sg : Summable g := (sumBudget_uncharge (fun i=>(cap i).1) paid).2.1.add summ
  have many := summable_finsetProd_of_summable_nonneg
    (f:=fun i=>2*g i) (fun i=>mul_nonneg (by norm_num) (pos i)) (sg.mul_left 2)
  have node (F : Finset ℕ) (i : ↥F) :
      ‖pointValue P.p P.activities f U ⟨F,i⟩‖ ≤ ∏ j∈F,g j := by
    unfold pointValue
    split
    · rw [←Finset.mul_prod_erase F g i.property,norm_mul,norm_prod]
      refine mul_le_mul (((cap i).2 U).trans (le_add_of_nonneg_right (kb _).1)) ?_
        (prod_nonneg fun _ _=>norm_nonneg _) (pos i)
      exact prod_le_prod (fun _ _=>norm_nonneg _) fun j _=>
        (Complex.norm_real _).trans_le (((kb j).2 U).trans (le_add_of_nonneg_left (cap j).1))
    exact norm_zero.le.trans (prod_nonneg fun j _=>pos j)
  apply (summable_sigma_of_nonneg (fun k : Push.Local.Pointed => norm_nonneg (pointValue P.p P.activities f U k))).2
  refine ⟨fun _=>Summable.of_finite,Summable.of_nonneg_of_le (fun _=>tsum_nonneg fun _=>norm_nonneg _) (fun F=>?_) many⟩
  rw [tsum_fintype]
  refine (Finset.sum_le_sum (fun i _=>node F i)).trans ?_
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,Finset.prod_mul_distrib,Finset.prod_const]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.lt_two_pow_self (n:=F.card)).le)
    (prod_nonneg fun j _=>pos j)

theorem actual {f : ℕ → Config G n → ℂ} {a v : ℝ}
    (budget : ForceCost P.p P.activities f a) (hard : P.activities.KBound P.p v) (U : Config G n) :
    HasSum (pointValue P.p P.activities f U) (∑' F,gasMark P.p P.activities U F f) := by
  have h := (absolute budget hard U).of_norm
  have eq : (∑' x : Push.Local.Pointed,pointValue P.p P.activities f U x) = ∑' F,gasMark P.p P.activities U F f :=
    h.tsum_sigma.trans (tsum_congr fun F=> by rw [tsum_fintype,←gasMark_point])
  rw [←eq]
  exact h.hasSum

theorem retained {ι : Type} (K : Guard.Keeper P.p P.activities) (T : ι → Support n) (I : ι → Finset ℕ)
    (serial : ι × Finset ℕ ↪ ℕ) (f : ι → Config G n → ℂ)
    {a v : ℝ} (budget : ForceCost P.p P.activities (entered P K T I serial f) a)
    (hard : P.activities.KBound P.p v) (U : Config G n) :
    HasSum (fun z : Born P T I U => f z.1 U * ∏ j ∈ z.2.val \ I z.1,(P.activities.K j U : ℂ))
      (∑' F,gasMark P.p P.activities U F (entered P K T I serial f)) := by
  let e : Born P T I U ≃ Arrived P K T I serial U := Equiv.sigmaCongrRight
    (fun z=>equivalence P K (T z) (I z) U (fun C=>serial (z,C)))
  have source := ((unique P K T I serial U).hasSum_iff (zeroOutside P K T I serial U f)).2 (actual budget hard U)
  apply (e.symm.hasSum_iff).1
  apply source.congr_fun
  intro w
  exact (WilsonCenteredCapturePush.value P K T I serial U f w).symm

end YM.Integration.WilsonCenteredActualHardSum
