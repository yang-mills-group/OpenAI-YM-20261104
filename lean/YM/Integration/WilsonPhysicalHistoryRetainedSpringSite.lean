import YM.Integration.WilsonPhysicalHistoryRetainedSpringPlan

/-! The true site bill of every signed native period packet. Its absolute
size has no factor for the number of sites of the observing torus. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice Wilson RG Precision MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open scoped Topology BigOperators Classical
variable {G : Gauge} {n : Side} {k : ℕ}

def sitePacket (A : ℕ→Atom G k) (x : Site n) (U : Config G n) : ℝ :=
  Patch.average fun s : Signed=>∑' i,(A i).unmasked (pull s 0 U) x

theorem mean_bound (f : Signed→ℝ) (b : ℝ) (h : ∀ s,|f s|≤b) :
    |Patch.average f|≤b := by
  have pos : 0<(Fintype.card Signed:ℝ):=Nat.cast_pos.mpr Fintype.card_pos
  unfold Patch.average
  rw [abs_mul,abs_of_pos (inv_pos.mpr pos)]
  apply (mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs ..).trans
    (Finset.sum_le_sum (g:=fun _=>b) (fun i _=>h i))) (inv_nonneg.mpr pos.le)).trans_eq
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←mul_assoc,inv_mul_cancel₀ pos.ne',one_mul]

theorem site_packet (A : ℕ→Atom G k) {σ b : ℝ} (pos : 0<σ)
    (bill : SumBudget (fun i=>(A i).budget σ) b) (x : Site n) :
    Measurable (sitePacket A x) ∧ ∀ U,‖sitePacket A x U‖≤b*2^k := by
  have obs (s : Signed) (i : ℕ) :
      Measurable (fun U : Config G n=>(A i).unmasked (pull s 0 U) x) :=
    ((A i).unmasked_cont x).measurable.comp (continuous_pull s 0).measurable
  refine ⟨measurable_const.mul (Finset.measurable_sum _ fun s _=>Measurable.tsum (obs s)),?_⟩
  intro U
  exact mean_bound _ _ fun s=>by
    let f:=fun i : ℕ=>(A i).unmasked (pull s 0 U) x
    let B:=fun i : ℕ=>(A i).budget σ*2^k
    have hs : Summable B := bill.2.1.mul_right _
    have hb (i : ℕ) : ‖f i‖≤B i := ((A i).unmasked_bound _ _).trans
      (mul_le_mul_of_nonneg_right ((A i).lower_budget σ pos) (by positivity))
    have hf : Summable (fun i=>‖f i‖) := Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hb hs
    apply (norm_tsum_le_tsum_norm hf).trans ((hf.tsum_le_tsum hb hs).trans ?_)
    change (∑' i,(A i).budget σ*2^k)≤_
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right bill.2.2 (by positivity)

theorem packet_sites (A : ℕ→Atom G k) (U : Config G n) :
    Patch.average (fun s : Signed=>uncut A (pull s 0 U))=∑ x : Site n,sitePacket A x U := by
  unfold uncut sitePacket Patch.average
  rw [←Finset.mul_sum,Finset.sum_comm]

def springPacketsAt (Z : SeriesA G) (c : ℝ) (x : Site n) (U : Config G n) : ℝ :=
  (Z.map fun a=>c^(a.grade-a.rise)*sitePacket a.cells x U).sum

def packetBill (Z : SeriesA G) (c b : ℝ) : ℝ :=
  (Z.map fun a=>|c|^(a.grade-a.rise)*(b*2^(a.rise+2))).sum

theorem period_sites (Z : SeriesA G) (c : ℝ) (U : Config G n) :
    FundedPeriodAction.rendered n Z c U=∑ x : Site n,springPacketsAt Z c x U := by
  induction Z with
  | nil => simp [FundedPeriodAction.rendered,springPacketsAt]
  | cons a z ih =>
    simp only [FundedPeriodAction.rendered,springPacketsAt,List.map_cons,List.sum_cons] at ih ⊢
    rw [Finset.sum_add_distrib,FundedPeriodAction.action,packet_sites,Finset.mul_sum,ih]

theorem period_site_price {σ b : ℝ} (pos : 0<σ) (Z : SeriesA G) (paid : Draw Z σ b)
    (c : ℝ) (x : Site n) :
    Measurable (springPacketsAt Z c x) ∧ ∀ U,‖springPacketsAt Z c x U‖≤packetBill Z c b := by
  induction Z with
  | nil => exact ⟨measurable_const,fun _=>by simp [springPacketsAt,packetBill]⟩
  | cons a z ih =>
    have hz : Draw z σ b:=⟨paid.1,fun b h=>paid.2 b (List.mem_cons_of_mem _ h)⟩
    obtain ⟨hm,hc⟩:=ih hz
    obtain ⟨am,ac⟩:=site_packet a.cells pos (paid.2 a (List.mem_cons_self ..)).toll x
    refine ⟨(measurable_const.mul am).add hm,?_⟩
    intro U
    change ‖c^(a.grade-a.rise)*sitePacket a.cells x U+springPacketsAt z c x U‖≤
      |c|^(a.grade-a.rise)*(b*2^(a.rise+2))+packetBill z c b
    apply (norm_add_le ..).trans
    rw [norm_mul,norm_pow,Real.norm_eq_abs]
    exact add_le_add (mul_le_mul_of_nonneg_left (ac U) (by positivity)) (hc U)

end YM.Integration.OriginalMarkedRunAction
