import YangMills.WilsonProof.NativeSupport.JointTicket
import YM.MergeProof.Dreams

/-! The positive selector bill is the original campaign's numerical bill even
when each selected ticket carries its actual bounded transition measurements. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointSwitch
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset
open MeasureTheory Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6
open Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Mask Contract Work.F03
open Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse Coat Matter
open ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt
open Merge Merge.Palette Switch Mixed Daisy Blaze.March Multiple Ursell Trees OmitClusters Gas
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {ι : Type} [Fintype ι] {G : Gauge} {c f L : Side} {S : StepData c f}
    {P : Teller G} {T : Tube G S} {F : Forest S.ratio} {R : Rep G f} {W μ x C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}
variable (M : ι→Leaf R) (Y : Cash W x μ L Q o C T R) (χ : Chi) (rA : ι→ℝ)
variable (marks : Tickets (Palette.sign M S)→Finset (Bond c)) (h : Tickets (Palette.sign M S)→Bond c→ℝ→ℝ)
variable (hm : ∀ i,∀ b∈marks i,Measurable (h i b))
variable (unit : ∀ i,∀ b∈marks i,∀ t∈Set.Icc 0 (linkCap S),‖h i b t‖≤1)
abbrev coefficientAt (U : Config G c) (p : Molecule S) (i : Tickets (Palette.sign M S)) : ℝ :=
  JointTicket.act M Y χ U p i (marks i) (h i)
local notation "sx" => radiusB x
local notation "di" => ConnectedActivityE6.lengths T R
local notation "kd" => steamP S (Q.costs L μ R.beta x C)

def vote (p : Molecule S) (U : Config G c) (t : ℝ) (s : Finset ι) : ℝ :=
  ∑ i : Tickets (Palette.sign M S),(∏ j∈i.val,ways rA t s j)*coefficientAt M Y χ marks h U p i

omit [Fintype ι] in
theorem present {p : Molecule S} (U : Config G c) (i : Tickets (Palette.sign M S))
    (nonzero : coefficientAt M Y χ marks h U p i≠0) :
    standsIn (planted (prism T x χ o.K U F) p) R Q.halo p := by
  by_contra absent
  apply nonzero
  unfold coefficientAt JointTicket.act likely
  dsimp only
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro r _
  exact if_neg (show ¬standsIn (prism T x χ o.K U (allot r)) R Q.halo p from absent)

variable (live : ∀ i,0≤rA i)
include hm unit live
theorem payments (p : Molecule S) :
    Paid (vote M Y χ rA marks h p) (∏ i∈p,Palette.toll M Y rA i) := by
  let cost (i : Tickets (Palette.sign M S)) := if i.reach⊆p then
    (∏ j∈i.val,Palette.wages M rA j)*∏ j∈p\i.reach,Y.text j else 0
  have each (i : Tickets (Palette.sign M S)) :
      Paid (fun U t s => (∏ j∈i.val,ways rA t s j)*coefficientAt M Y χ marks h U p i) (cost i) := by
    by_cases here : i.reach⊆p
    · let a := ∏ j∈i.val,rA j
      let base := (∏ j∈i.val,(M j).weight)*∏ j∈p\i.reach,Y.text j
      have ha : 0≤a := prod_nonneg fun j _ => live j
      have hb : 0≤base := mul_nonneg (prod_nonneg fun j _ => (M j).profit)
        (prod_nonneg fun j _ => Y.positive j)
      have bill : cost i=a*base := by
        simp only [cost,if_pos here,Palette.wages,prod_mul_distrib,a,base,mul_assoc]
      rw [bill]
      have clickPaid := paidClick (ι:=ι) i.val (p:=fun U => a*coefficientAt M Y χ marks h U p i)
        (mul_nonneg ha hb) (fun U => by
          rw [norm_mul,Real.norm_of_nonneg ha]
          apply mul_le_mul_of_nonneg_left _ ha
          simpa only [if_pos here] using JointTicket.price M Y χ U p i (marks i) (h i) (hm i) (unit i))
      apply Paid.congr clickPaid
      intro U t _
      ext v
      rw [amplitudes]
      unfold click
      split_ifs <;> ring
    · have vanish (U) : coefficientAt M Y χ marks h U p i=0 := norm_le_zero_iff.mp (by
        simpa only [if_neg here] using JointTicket.price M Y χ U p i (marks i) (h i) (hm i) (unit i))
      rw [show cost i=0 from if_neg here]
      apply Paid.congr paidZero
      intro U t _
      ext v
      rw [vanish,mul_zero]
      rfl
  rw [show (∏ i∈p,Palette.toll M Y rA i)=∑ i:Tickets (Palette.sign M S),cost i from
    Tickets.expanded (sign M S) _ _ p]
  apply Paid.congr (Paid.sum univ _ _ fun i _ => each i)
  intro U t _
  ext v
  simp only [Finset.sum_apply]
  rfl

theorem molecular (p : Molecule S) (n k : ℕ) (hn : n≤Cash.numP p) :
    Paid (vote M Y χ rA marks h p) (Palette.tune M Y rA n k p) := by
  by_cases admitted : Y.ticketsP 0 n 0 p
  · have same (i) : Palette.toll M Y rA i =
        Mixed.costs S Q.halo sx kd (Palette.pitch M Y rA) i := by
      rcases i with i|i
      · unfold Palette.toll Tickets.extra
        rw [sum_eq_zero,add_zero]
        · rfl
        intro j _
        exact if_neg fun e => by
          have bad := (show .inr _=sign M S j from Daisy.sparkPath ..).trans e
          contradiction
      unfold Palette.toll Tickets.extra Cash.text Mixed.costs Palette.pitch Tickets.extra
      dsimp only [Sum.elim]
      simp_rw [← show ∀ j,(.inr (Palette.mark M (c:=c) j) : Head S)=sign M S j from
        fun j => Daisy.sparkPath ..]
      simp only [Sum.inr.injEq]
    have hit := payments M Y χ rA marks h hm unit live p
    apply hit.weaken
    unfold Palette.tune Mixed.selected
    rw [if_pos (show Allowed S Q.halo sx (Daisy.swing Q L μ R.beta x C) Y.birth di 0 n 0 p from admitted)]
    unfold Mixed.Price
    simp_rw [← same]
    exact le_mul_of_one_le_right hit.rocket (one_le_pow₀ (le_add_of_nonneg_right (Y.positive_volume p)))
  · have vanish (i : Tickets (Palette.sign M S)) (U) : coefficientAt M Y χ marks h U p i=0 := by
      letI : Nonempty (Forest S.ratio) := Tree.select S.ratio S.patch.odd_side
      by_contra ne
      have has := present M Y χ marks h (F:=Classical.ofNonempty) U i ne
      exact admitted ⟨has.1,Nat.zero_le _,hn,Y.positive_volume p⟩
    unfold Palette.tune Mixed.selected
    rw [if_neg (show ¬Allowed S Q.halo sx (Daisy.swing Q L μ R.beta x C) Y.birth di 0 n 0 p from admitted)]
    apply Paid.congr paidZero
    intro U t _
    ext v
    unfold vote
    simp_rw [vanish,mul_zero,sum_const_zero]
    rfl

end YM.Integration.InletSusceptibility.JointSwitch
