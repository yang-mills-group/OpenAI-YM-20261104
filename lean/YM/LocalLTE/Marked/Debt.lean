import YM.LocalLTE.Marked.Owners
import YM.MergeProof.Permit
import YM.LocalLTE.Tier.Score
import YM.LocalLTE.Pond.Mint
/-! Reduced-radius cluster invoices. Finite tapes before narrowing, fully priced when #markers bounded (anchors arbitrary). -/
set_option autoImplicit false
noncomputable section
namespace YM.Merge.Palette
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι] {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ:Chi)
local notation "sx"=> radiusB x
open Blaze.March Multiple Ursell Trees Mixed Daisy OmitClusters Gas
variable (rA:ι→ℝ)
local notation "dc"=> ConnectedActivityE6.lengths T R
local notation "kd"=> steamP S (Q.costs L μ R.beta x C)
variable (h:∀ i, 0≤ rA i)
-- as output.Canonical.Us prices ∑ abs all labels AFTER reduction. see Cards.P
local notation "w!"=> (wages M rA)
local notation "D"=> Q.goal L x
local notation "E'"=> ((Q.costs L μ R.beta x C))
set_option quotPrecheck false
include h Y
lemma saltBill (hp: (∑ i,rA i*R.p.mass (M i).crest (M i).weight) ≤ Q.goal L x) : (∑ i,rA i*jewelDebt (M i) Q L x) ≤1:=by
    have he:=arable Y
    apply le_of_mul_le_mul_right _ he; rw [sum_mul]; refine (sum_le_sum ?_).trans (hp.trans (one_mul _).symm.le)
    intro i _; unfold jewelDebt; rw [mul_assoc,div_mul_cancel₀ _ he.ne']; apply mul_le_mul_of_nonneg_left _ (h _)
    exact mul_le_of_le_one_right (mul_nonneg (Real.exp_pos _).le (M i).profit) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Q.usable.le) (Nat.cast_nonneg _)))
variable (hh': (∑ i,rA i* R.p.mass (M i).crest (M i).weight) ≤ Q.goal L x) (hF:foam Q L)(ht:R.p.B≤2*(radiusB x))
include hh' hF ht
open Reserves
lemma fires : Ac.Hit Y.birth (radiusB x) (Reserves.tariff (Tickets.extra (mark M) (wages M rA)) (ConnectedActivityE6.lengths T R) (fun _=>0) Q.ε) Q.relative (Daisy.ribbon Q L x):=by
    let i j:= colly (n:=c) (fun _=>0) (M j) Q L x
    let e j:= rA j*jewelDebt (M j) Q L x; have he j:0 ≤ e j:=mul_nonneg (h _) (dew (M j) Y).2.1
    let γ:= Daisy.ribbon Q L x; have hp:0 ≤ γ:= mul_nonneg (arable Y).le (Real.exp_nonneg _)
    intro u
    let f k := fun j=> if u∈Y.birth j then Reserves.tariff (i k) (ConnectedActivityE6.lengths T R) (fun _=>0) Q.ε j* Real.exp (Q.relative*coverNumber sx (Y.birth j)) else 0
    have ht' k := budget_scale (he k) (Daisy.sustains (M k) Y hF ht u)
    have hf : SumBudget (fun j=>∑ k:ι,e k*f k j) (∑ k,e k*γ):= by
       exact AnalyticBridge.VerifiedReset.Collection.Price.total _ _ _ (fun i _=> ht' i) -- edit
    have hc (j): Tickets.extra (mark M (c:=c)) (wages M rA) j=∑ k,e k*i k j :=by
       apply sum_congr rfl; intro k _; by_cases h :mark (c:=c) M k=j
       · rw [if_pos h, show i k j=jewel (M k) Q L x from (if_pos h.symm)]; unfold wages; rw [(dew (M k) Y).2.2]; ring
       rw [if_neg h,show i k j=0 from (if_neg (Ne.symm h)),mul_zero]
    refine budget_loosen (budget_mono hf (fun j=> ?_) (fun j=> ?_)) ?_
    · split; next ht=>
        apply mul_nonneg _ (Real.exp_nonneg _); apply mul_nonneg _ (Real.exp_nonneg _); exact sum_nonneg (fun k _=> by split <;> first| exact mul_nonneg (h _) (M k).profit | exact le_rfl)
      next=> rfl
    · split
      next hx=>
        unfold f; simp_rw [if_pos hx]; unfold Reserves.tariff; rw [hc, sum_mul,sum_mul]; exact le_of_eq <| sum_congr rfl (fun i _=> by ring)
      next=> exact hf.1 _
    rw [← sum_mul]; exact mul_le_of_le_one_left hp (saltBill M Y rA h hh')
lemma toward {r : ℝ} (V:ConnectedActivityE6.Alphabet c f→ℝ)(X : Pressure.Stores S→ℝ) (hv:Accounts S Q.halo sx (Q.costs L μ R.beta x r) Y.birth V dc X): Accounts S Q.halo sx (swing Q L μ R.beta x r) Y.birth (fun i=> V i+Tickets.extra (mark M) (wages M rA) i) dc X:=by
   refine ⟨hv.packetBound,fun i=>add_nonneg (hv.holds i) (sum_nonneg (fun k _=> ?_)),hv.extra,fun i=>?_⟩
   · split; exact mul_nonneg (h _) (M k).profit; exact le_rfl
   have ht:= budget_plus (hv.pays i) (fires M Y rA h hh' hF ht i); convert! ht using 1; ext j; unfold Reserves.tariff; split_ifs <;> simp only [add_mul,add_zero]; rfl
lemma activeB : Plot M Y rA:= ⟨toward M Y rA h hh' hF ht Y.opt _ Y.armed,h⟩
end YM.Merge.Palette
