import YM.LocalLTE.Marked.Roots
import YM.LocalLTE.Quartz.Lots
import YM.MergeProof.Prism

/-! A genuine selected compulsory source prevents any nonzero original wing
from lying in the low fragrance class, even at independent coarse fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalForcedClusters
open Filter Function Finset Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson
open ConnectedActivityE6 Blaze Blaze.March Captain Push Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Height LocalLTE MergeProof Marker Extra.Multi
open scoped Classical BigOperators

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {R : Rep G f}
  {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W x μ a : ℝ} {o : Target.Order G W}
  (H : Cash W x μ L Q o a T R) (χ : Push.SectorMeasure.Chi) {ι : Type} (M : ι→Lotus.Leaf R)

def compulsory (z : Fan.Stars H M) : Prop := ∃b i t,i∈(z.2 b).val ∧ (M i).turn=.gasKey t

/-- Each component may be tested on an independent coarse field. -/
def alive (z : Fan.Stars H M) : Prop := ∃U:Option (Fin z.1.1)→ Config G c,
  ∀b,Captain.waltz H χ M (z.1.2 b) (z.2 b) (U b)≠0

theorem classified (ℓ : ℕ) (z : Fan.Stars H M) (force : compulsory H M z) (live : alive H χ M z) :
    Height.tiredN H ℓ z.1 := by
  obtain ⟨U,nonzero⟩ := live
  obtain ⟨b,i,t,seen,tag⟩ := force
  by_contra low
  have row (j:Option (Fin z.1.1)) := Captain.silenced M (z.1.2 j) (z.2 j) (U j) (nonzero j)
  have elders := Height.aged (H:=H) (fun j=>⟨(row j).1,(row j).2.1⟩) low
  have touched : Merge.Palette.sign M S i∈(z.1.2 b).val := (row b).2.2.1 ((z.2 b).reaches_of seen)
  rw [Merge.Palette.sign,tag] at touched
  have owner : t∈Matter.own (z.1.2 b).val := Finset.mem_toLeft.mpr (Finset.mem_toRight.mpr touched)
  rw [(elders.1 b).noK] at owner
  exact Finset.notMem_empty _ owner

theorem true_branch (z : Fan.Stars H M) (U : Config G c)
    (nonzero : Captain.wingTerm (H:=H) (χ:=χ) z.1 M z.2 U≠0) : alive H χ M z := by
  refine ⟨fun _=>U,fun b h=>nonzero ?_⟩
  unfold Captain.wingTerm
  rw [Finset.prod_eq_zero (i:=b) (Finset.mem_univ b) h,mul_zero,zero_div]

theorem low_zero (ℓ : ℕ) (z : Fan.Stars H M) (force : compulsory H M z) (low : ¬Height.tiredN H ℓ z.1) :
    Captain.wingTerm (H:=H) (χ:=χ) z.1 M z.2=0 := by
  funext U
  exact not_not.mp (fun live=>low (classified H χ M ℓ z force (true_branch H χ M z U live)))

/-- The exact measured signed term is unchanged when dead compulsory bookings
are removed before taking a rooted absolute derivative price. -/
theorem measured {V : Type} [DecidableEq V] {Γ : Census V} (field : Fan.Stars H M→Poly Γ)
    (z : Fan.Stars H M) (U : Config G c) :
    (if compulsory H M z then (Captain.wingTerm (H:=H) (χ:=χ) z.1 M z.2 U:ℂ) • field z else 0)=
      (if compulsory H M z ∧ alive H χ M z then (Captain.wingTerm (H:=H) (χ:=χ) z.1 M z.2 U:ℂ) • field z else 0) := by
  classical
  by_cases force : compulsory H M z
  · by_cases live : alive H χ M z
    · simp [force,live]
    · have h : Captain.wingTerm (H:=H) (χ:=χ) z.1 M z.2 U=0 := not_not.mp (fun h=>live (true_branch H χ M z U h))
      simp [force,live,h]
  · simp [force]

/-- A full native high rooted expense buys all genuinely contributing
compulsory whole components on the identical reach and support exponent. -/
theorem rooted (ℓ : ℕ) (fee : Fan.Stars H M→ℝ) (hn : ∀z,0≤fee z) {B : ℕ} {σ cost : ℝ}
    (high : Ac.Hit (fun z:Fan.Stars H M=>Captain.reachability z.1) B
      (fun z=>if Height.tiredN H ℓ z.1 then fee z else 0) σ cost) :
    Ac.Hit (fun z:Fan.Stars H M=>Captain.reachability z.1) B
      (fun z=>if compulsory H M z ∧ alive H χ M z then fee z else 0) σ cost := by
  classical
  have non z : 0≤(if compulsory H M z ∧ alive H χ M z then fee z else 0) := by split_ifs <;> first | exact hn z | exact le_rfl
  have debit z : (if compulsory H M z ∧ alive H χ M z then fee z else 0)≤(if Height.tiredN H ℓ z.1 then fee z else 0) := by
    by_cases h : compulsory H M z ∧ alive H χ M z
    · rw [if_pos h,if_pos (classified H χ M ℓ z h.1 h.2)]
    · rw [if_neg h];split_ifs <;> first | exact hn z | exact le_rfl
  intro site
  apply Push.AbsoluteSums.budget_mono (high site)
  · intro z
    by_cases h : site∈Captain.reachability z.1
    · simp only [if_pos h];exact mul_nonneg (non z) (Real.exp_pos _).le
    · simp only [if_neg h,le_refl]
  · intro z
    by_cases h : site∈Captain.reachability z.1
    · simp only [if_pos h];exact mul_le_mul_of_nonneg_right (debit z) (Real.exp_pos _).le
    · simp only [if_neg h,le_refl]

/-- A hard label appears once for the complete integrated component, including
all of its other compulsory marks and ambient gas factors. -/
def selected (z : Fan.Stars H M) (b : Option (Fin z.1.1)) : Prop :=
  ∃ i t, i∈(z.2 b).val ∧ (M i).turn=.gasKey t

def count (z : Fan.Stars H M) : ℕ := (Finset.univ.filter (selected H M z)).card

def seeded (z : Fan.Stars H M) (b : Option (Fin z.1.1)) : Prop :=
  ((z.1.2 b).val.toLeft).Nonempty

def seedCount (z : Fan.Stars H M) : ℕ := (Finset.univ.filter (seeded H M z)).card

/-- This includes every original compulsory activity occurring in a connected
component, whether or not that particular activity carries an external mark. -/
def owned (z:Fan.Stars H M) (b:Option (Fin z.1.1)) : Prop :=
  (Matter.own (z.1.2 b).val).Nonempty

def ownerCount (z:Fan.Stars H M) : ℕ := (Finset.univ.filter (owned H M z)).card

lemma owner_seed (z:Fan.Stars H M) (live:alive H χ M z) {b:Option (Fin z.1.1)}
    (forced:owned H M z b) : seeded H M z b := by
  obtain ⟨t,occupied⟩ := forced
  obtain ⟨U,hU⟩ := live
  have troupe := (Captain.silenced M (z.1.2 b) (z.2 b) (U b) (hU b)).2.1
  obtain ⟨j,hj⟩ := (R.activities.forced t).inventory_ne
  obtain ⟨v,hv,_⟩ := troupe.2.2 _ occupied _ hj
  by_contra empty
  have zero : (z.1.2 b).val.toLeft=∅ := Finset.not_nonempty_iff_eq_empty.mp empty
  unfold Matter.roster Packets.store at hv
  rw [zero] at hv
  simp at hv

lemma all_owners (z:Fan.Stars H M) (live:alive H χ M z) :
    ownerCount H M z≤ seedCount H M z :=
  Finset.card_le_card fun _ hb => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,owner_seed H χ M z live (Finset.mem_filter.mp hb).2⟩

lemma incident (z : Fan.Stars H M) (live : alive H χ M z)
    {b : Option (Fin z.1.1)} (hb : selected H M z b) : seeded H M z b := by
  obtain ⟨i,t,seen,kind⟩ := hb
  obtain ⟨U,hU⟩ := live
  have row := Captain.silenced M (z.1.2 b) (z.2 b) (U b) (hU b)
  have ht : Merge.Palette.sign M S i∈(z.1.2 b).val := row.2.2.1 ((z.2 b).reaches_of seen)
  rw [Merge.Palette.sign,kind] at ht
  have occupied : t∈Matter.own (z.1.2 b).val :=
    Finset.mem_toLeft.mpr (Finset.mem_toRight.mpr ht)
  exact owner_seed H χ M z ⟨U,hU⟩ ⟨t,occupied⟩

lemma count_le_seed (z : Fan.Stars H M) (live : alive H χ M z) :
    count H M z≤ seedCount H M z :=
  Finset.card_le_card fun _ hb => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,incident H χ M z live (Finset.mem_filter.mp hb).2⟩

lemma seeds_le_overlap (z : Fan.Stars H M) (live : alive H χ M z) :
    seedCount H M z≤Height.overlap H z.1 := by
  obtain ⟨U,hU⟩ := live
  let used := Finset.univ.filter (seeded H M z)
  have charge (b) (hb : b∈used) : 1≤Cash.numP (z.1.2 b).val := by
    obtain ⟨w,hw⟩ := (Finset.mem_filter.mp hb).2
    have troupe := (Captain.silenced M (z.1.2 b) (z.2 b) (U b) (hU b)).2.1
    calc 1≤w.shares := by rw [←Packets.seeds_card]; exact Finset.card_pos.mpr (troupe.1.checkpoints w hw).1
         _≤Cash.numP (z.1.2 b).val := Finset.single_le_sum (f:=Mixed.shares S)
           (fun _ _=>Nat.zero_le _) (Finset.mem_toLeft.mp hw)
  calc seedCount H M z=∑ b∈used,1 := by simp [seedCount,used]
       _≤∑ b∈used,Cash.numP (z.1.2 b).val := Finset.sum_le_sum charge
       _≤Height.overlap H z.1 := Finset.sum_le_sum_of_subset_of_nonneg
         (Finset.filter_subset _ _) fun _ _ _=>Nat.zero_le _

lemma counted (z : Fan.Stars H M) (live : alive H χ M z) :
    count H M z≤Height.overlap H z.1 :=
  (count_le_seed H χ M z live).trans (seeds_le_overlap H χ M z live)

lemma positive (z : Fan.Stars H M) : 0<count H M z ↔ compulsory H M z := by
  change 0<(Finset.univ.filter (selected H M z)).card ↔ _
  rw [Finset.card_pos]
  exact ⟨fun ⟨b,hb⟩=>⟨b,(Finset.mem_filter.mp hb).2⟩,
    fun ⟨b,hb⟩=>⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩⟩⟩

/-- The conditional integral itself vanishes identically if its original whole
independently integrated product is dead. It has zero cost at every order. -/
lemma dead (z:Fan.Stars H M) (hz:¬alive H χ M z) :
    Captain.wingTerm (H:=H) (χ:=χ) z.1 M z.2=0 := by
  funext U
  by_contra nonzero
  exact hz (true_branch H χ M z U nonzero)

theorem differentiated {C d rv s A v y B e:ℝ} {j k:ℕ}
    (N:Captain H j C d rv s A v y B e k χ) (host:PhysicalNext.Repeat.Daisy.HostQ H N.conduit A B k)
    (z:Fan.Stars H M) (Z:BudgetPoint) (ht:Z.threshold=Pressure.temp x)
    (hord:Z.order≤j) (n:ℕ) (hn:Z.power≤n) :
    let X:=Captain.reachability z.1
    let f:=Captain.wingTerm (H:=H) (χ:=χ) z.1 M z.2
    ((fun U=>Ursell.coefficient H.seam z.1.2*(∏ b,Merge.Palette.act M H χ U (z.1.2 b).val (z.2 b)) /
      ↑(z.1.fst+1).factorial)=RG.masked Z.threshold X f) ∧ Z.Regular X f ∧
    ∀o∈X,Z.supBounds o X f (if alive H χ M z then Captain.wife N z.1 M z.2 n else 0) := by
  intro X f
  have native:=Captain.wing N z.1 M z.2 host Z ht hord n hn
  refine ⟨native.1,native.2.1,fun o ho=>?_⟩
  by_cases live:alive H χ M z
  · rw [if_pos live];exact native.2.2 o ho
  · rw [if_neg live,show f=0 from dead H χ M z live]
    exact Progress.DirectedRecipe.no_cost Z o X

end YM.Integration.ManuscriptQLocalForcedClusters
