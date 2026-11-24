import YangMills.WilsonProof.NativeSupport.JointLinearPicture
import YangMills.WilsonProof.NativeSupport.JointStageWord

/-! Recover the product of every genuine spectator from positive physical
generating subsets in the original law. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Dated
open Function Finset Lattice RG Wilson RGComparison.Core16 Marker Push.BetaTransport
open WilsonUniformUnmarkedInletEnergySites WilsonUniformUnmarkedInletBondRemainder
open JointMoments
open scoped Classical BigOperators
variable {I:Type} [Fintype I] [DecidableEq I] {G:Gauge} {n c:Side}

private theorem restrict_micro (F:I → Config G n → ℝ) (E:Finset I) (h:ℝ) (X:Config G n):
    micro F E h X=∏ i∈E,(1+h*F i X) := by
  unfold micro
  rw [←prod_subset (subset_univ E) (f:=fun i=>(1+(if i∈E then 1 else 0)*h*F i X)) (fun i _ hi=>by simp [hi])]
  exact prod_congr rfl fun i hi=>by simp [hi]

private theorem reconstruct (F:I → Config G n → ℝ) (h:ℝ) (X:Config G n):
    ∑ E∈(univ:Finset I).powerset,(-1:ℝ)^(Fintype.card I-E.card)*micro F E h X=h^(Fintype.card I)*(∏ i,F i X) := by
  calc
    _ = ∑ E∈(univ:Finset I).powerset,(∏ i∈E,(1+h*F i X))*(∏ _i∈univ\E,(-1:ℝ)) := by
      apply sum_congr rfl;intro E hE
      rw [prod_const,card_sdiff_of_subset (mem_powerset.mp hE),card_univ,restrict_micro,mul_comm]
    _ = ∏ i,(1+h*F i X+(-1:ℝ)) := (prod_add _ _ _).symm
    _ = ∏ i,(h*F i X) := prod_congr rfl fun i _=>by ring
    _ = _ := by rw [prod_mul_distrib,prod_const,card_univ]

theorem roster_extraction (d:Descent n c) (ok:d.OK G) (β δ:ℕ→ℝ) (r:ℝ) (V:Config G c)
    (F:I → Config G n → ℝ) (ct:∀ i,Continuous (F i)) (sym:∀ i,GaugeInvariant (F i)) {h:ℝ} (hp:0 < h)
    (subsetPrice:∀ E:Finset I,h*(∑ q∈interior d,|picture d β δ V (micro F E h) r q|) ≤ (3/2:ℝ)^E.card):
    (∑ q∈interior d,|picture d β δ V (fun X=>∏ i,F i X) r q|) ≤
      (5/2:ℝ)^(Fintype.card I)/h^(Fintype.card I+1) := by
  let m:=Fintype.card I
  let a (E:Finset I):=(-1:ℝ)^(m-E.card)/h^m
  have cf (E:Finset I):Continuous (micro F E h):=
    continuous_finsetProd _ (fun i _=>continuous_const.add (continuous_const.mul (ct i)))
  have gf (E:Finset I):GaugeInvariant (micro F E h):=by
    intro k X;unfold micro;exact prod_congr rfl fun i _=>by rw [sym i k X]
  have expr:(fun X=>∏ i,F i X)=(fun X=>∑ E∈(univ:Finset I).powerset,a E*micro F E h X):=by
    funext X
    calc
      _=(h^m*(∏ i,F i X))/h^m := by field_simp
      _=(∑ E∈(univ:Finset I).powerset,(-1:ℝ)^(m-E.card)*micro F E h X)/h^m := by rw [reconstruct]
      _=_ := by rw [sum_div];apply sum_congr rfl;intro E _;unfold a;ring
  have coeff (E:Finset I):|a E|=1/h^m:=by
    dsimp only [a]
    rw [abs_div,abs_pow,abs_neg,abs_one,one_pow,abs_of_pos (pow_pos hp _)]
  have fee (E:Finset I):(∑ q∈interior d,|picture d β δ V (micro F E h) r q|) ≤ (3/2:ℝ)^E.card/h:=
    (le_div_iff₀ hp).2 (by simpa only [mul_comm h] using subsetPrice E)
  rw [expr]
  calc
    _ ≤ _ := abs_picture_linear d ok β δ V r (univ:Finset I).powerset a (fun E=>micro F E h) (fun E _=>cf E) (fun E _=>gf E)
    _ ≤ ∑ E∈(univ:Finset I).powerset,(3/2:ℝ)^E.card/h^(m+1) := by
      apply sum_le_sum;intro E _
      rw [coeff]
      calc
        _ ≤ (1/h^m)*((3/2:ℝ)^E.card/h) := mul_le_mul_of_nonneg_left (fee E) (by positivity)
        _ = _ := by rw [pow_succ];ring
    _ = _ := by
      rw [←sum_div]
      have form:=prod_one_add (f:=fun _:I=>(3/2:ℝ)) univ
      have count:(∑ E∈(univ:Finset I).powerset,(3/2:ℝ)^E.card)=(5/2:ℝ)^m:=by
        simpa only [prod_const,card_univ,show (1:ℝ)+3/2=5/2 by norm_num] using form.symm
      rw [count]

end YM.Integration.InletSusceptibility.Dated
