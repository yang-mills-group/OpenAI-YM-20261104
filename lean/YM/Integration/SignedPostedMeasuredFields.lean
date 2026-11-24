import YM.Integration.SignedShiftedMeasuredCurrent
import YM.Integration.FundedMarkedPathSelection
import YM.Integration.OriginalMarkedHeatCovariance

/-! All roots and all actual unmasked Laurent source grades of the preselected original posted field. The independent output is the periodization of the measured cover tensor for its own chosen RG levels and ratio. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedPostedMeasuredFields
open Function Filter Finset Lattice Laurent Wilson RG RG.Supply Precision Exterior Tree Bloch Matrix PowerSeries
open Comparison.RG02 PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio) (M : Matrix (Woods G f) (Woods G c) ℝ) (ρ : fieldDir G c 1→ AxisChart G F)
variable {ι : Type} [DecidableEq ι] {D k : ι→ℕ} {J : Finset ι}

def expense (R : Robes G (Pen D J) (mass k J)) (p : ℕ) (A : Case D) (o:Cover) (b n:ℕ) (L : POL (Active G F⊕Woods G c)→ₗ[ℝ]ℝ) :=
  ∑j∈range p,∑r:Fin (mass k J + j + 1),∑'i, L (coeff (b+n) ((X:Ink (Active G F⊕Woods G c))^(b+j-r.val)*jet (fun z:Sloc S F G=>
    (dip (R j r i) (touch A J)).unmasked (Work.F03.live F (SignedMarkedChartGerm.chart S F ρ z)) (wrap f o))))

omit [DecidableEq ι] in
/-- The physical sum of absolutely convergent, genuinely rooted finite field jets equals the full posted finite branch at every original order and arbitrary real linear polynomial probe. -/
theorem whole (R : Robes G (Pen D J) (mass k J)) {s budget:ℝ} {p:ℕ} (hs:0<s) (bill:Rains R p s budget)
    (hM:M=reveal G S F*((reveal G S F).transpose*M)) (hρ:ContDiffAt ℝ ω ρ 0) (h0:ρ 0=0)
    (A:Case D) (o:Cover) (b n:ℕ) (hb:mass k J ≤ b) (L:POL (Active G F⊕Woods G c)→ₗ[ℝ]ℝ) :
    expense S F ρ R p A o b n L=L (coeff n (SignedMeasuredSourceSeries.probe S F M ρ (readO A (shifted (baton R p) o) f))) := by
  rw [baton,shiftedSum,read_Sum A f (fun j hj=>(starR _ (bill.2 j (mem_range.mp hj)) hs).shifted o)]
  simp only [map_sum,expense]
  apply sum_congr rfl;intro j hj
  rw [linesR,shiftedSum,read_Sum A f (fun r _=>(stars hs ((bill.2 j (mem_range.mp hj)).2 r).2 (Nat.le_of_lt_succ r.isLt) ((bill.2 j (mem_range.mp hj)).2 r).1).shifted o)]
  simp only [map_sum]
  apply sum_congr rfl;intro r _
  have g:=((bill.2 j (mem_range.mp hj)).2 r)
  exact (SignedShiftedMeasuredCurrent.measured S F M ρ (R j r) hs g.2 g.1 j b (b+j-r.val) (Nat.le_of_lt_succ r.isLt) (by have:=r.isLt;omega) hM hρ h0 A o n L).tsum_eq

private theorem prefixRows {U V : Type} [Fintype U] [Fintype V] (z:U→ Ink V) (a b:Ink U) (n:ℕ) (h:∀j ≤ n,coeff j a=coeff j b) :
    coeff n (train z a)=coeff n (train z b) := by
  unfold train;rw [edit_coeff _ _ _ (Nat.lt_succ_self n),edit_coeff _ _ _ (Nat.lt_succ_self n)];apply congrArg (coeff n);apply sum_congr rfl;intro i hi;rw [h i (Nat.le_of_lt_succ (mem_range.mp hi))]

section Actual
variable [Fintype ι] {Z:Finset ι} {e m N:ℕ} {A:ℝ} {Q:Realm G (e+1) Credit.leanC} {hm:Q.anchor ≤ m}
variable (X:FundedMarkedPathSelection.Input Q hm Z k D A) (hj:J⊆Z) (hA:0 ≤ A) (hN:m<N)
    (cl:Cloze D k Q Credit.leanC) (cap H:ℕ) (hc:J.card ≤ cap) (hdeg:mass k J ≤ H) (reserved:Insure cap H Q Credit.leanC) (a:ι) (ha:a∈J) (y : ι → Cover)
local notation "T" => FundedMarkedPathSelection.output X J N y
local notation "R₀" => sphere (T) (mass k J) (e+1) a y
local notation "baseFee" => FundedMarkedPathSelection.price Q k D A J m

include hj hA hN cl hc hdeg reserved ha in
/-- The sum of actual finite Wilson source jets on the posted run equals the independently periodized full canonical coefficient through the chosen horizon. All spatially independent source positions and the chosen root, all original external fields, and all Gaussian polynomial probes remain free. -/
theorem posted (hM:M=reveal G S F*((reveal G S F).transpose*M)) (hρ:ContDiffAt ℝ ω ρ 0) (h0:ρ 0=0)
    (A₀:Case D) (b n:ℕ) (hb:mass k J ≤ b) (hn:n ≤ e) (L:POL (Active G F⊕Woods G c)→ₗ[ℝ]ℝ) :
    expense S F ρ (R₀) (e+1) A₀ (y a) b n L=L (coeff n (SignedMeasuredSourceSeries.probe S F M ρ
      (flash (pPly A₀ J (fun i r=>plume ((T).2 i r) f))))) := by
  obtain ⟨hK,hW⟩:=FundedMarkedPathSelection.ready X hj hA hN cl y
  have hg : 0 ≤ baseFee := mul_nonneg (zero_le_one.trans (Credit.purchase _ (Q.depth m hm))) (pow_nonneg hA _)
  have g:=WilsonCoeffUV.Mer.Rolls.posting (reserved.proof m hm) y (T) ha hdeg hc (baseFee) hg hK hW (le_refl (e+1))
  rw [whole S F M ρ (R₀) (reserved.proof m hm).affordable g.1 hM hρ h0 A₀ (y a) b n hb L]
  apply congrArg L
  rw [SignedMeasuredSourceSeries.genuine]
  apply prefixRows;intro j hje
  have h:=g.2.2 j (by omega)
  apply congrArg totalR;funext r x
  change (touch A₀ J) ((shifted (baton R₀ (e+1)) (y a)).1 f ((Finsupp.single () j) ()) r x)=(touch A₀ J) (Carp.plume (T.2 ((Finsupp.single () j) ()) r) f x)
  rw [Finsupp.single_eq_same]
  exact congrArg (fun b=>(touch A₀ J) (b x)) (h.2.2 f r)
end Actual
end YM.Integration.SignedPostedMeasuredFields
