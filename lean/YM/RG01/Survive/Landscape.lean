import YM.RG01.Vacuum.Exceptions
/-!
# Structure of the rare-filter complement with nonzero unmasked cost
The exceptional-filter sector with its all-order profit is in Vacuum.
Here discharge the first binding obligation in analysing the complement:
in any USED unmasked log label there (on the genuine E6 output) NO
compulsory label or input K slot can occur, and all remaining First
molecules, clusters, and setPrices sit below the indicated fixed
arities/depths. This is at real addresses after the actual both-level
component/log expansions (before any readout). The erasure of compulsory
labels (including no positive seeds, clocks, flags) uses structure of
actual tags, not just the arbitrary-arity inequality.
No converse from footprint bound to mask probability, no proof that warning
factors that are optional with respect to those seeds may be Taylor
expanded, and no summation of short jets in this file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Survive
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W m : ℝ} {n : ℕ} {R : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

/-- Parameterize by actual arity budget K and length budget (already includes
`till` if needed, so hypotheses usable before actual schedule issuance too). -/
def short (K : ℕ) (ℓ : ℝ) (z : H.fragrances) :=
  degree H z < K ∧ overlap H z = 0 ∧ depth H z < ℓ

/-- Geometric/arity dossier for each remaining unforced molecule. Remaining
hard factors here (if any) are warning factors and ones hidden in optional
log entry spelling, NOT paid via the hard-pressure reserve automatically.
Doesn't prove a uniform bound on spatial extent independent of period. -/
structure Narrow (K : ℕ) (ℓ : ℝ) (p : H.ThinP) : Prop where
  connected : Ac.Spark H.supportP p.val
  enters : troupe T R Q.halo (radiusB s) p.val
  unforced : p.val.toLeft = ∅
  noK : own p.val = ∅
  population : p.val.Nonempty
  size' : p.val.card ≤ K
  setPrice : H.shapeW p.val < ℓ

lemma worth {p:H.ThinP} {V:Config G c} (h:leaflet H χ V p ≠ 0):
    Ac.Spark H.supportP p.val ∧ troupe T R Q.halo (radiusB s) p.val := by
  by_contra he
  apply h; unfold leaflet Pond.likely; simp_rw [vacuity V p he,sum_const_zero,mul_zero]

lemma leaves {z:H.fragrances}{V:Config G c} (h : stream H χ V z ≠ 0) (i) :
    leaflet H χ V (z.2 i) ≠ 0 := fun hp=> h (by unfold stream Gas.term; rw [prod_eq_zero (Finset.mem_univ i) hp,mul_zero,zero_div])

lemma narrows {z:H.fragrances}{V:Config G c} (h : stream H χ V z ≠ 0)
    (K : ℕ)(ℓ : ℝ)(hh: short K ℓ z) :
    (∀ i, Narrow K ℓ (z.2 i)) ∧ z.fst+1≤K := by
  let p i := z.2 i
  have hg i := worth (leaves h i)
  have he (i) : (p i).val.card ≤ breadth H z:= single_le_sum (f:=fun i=> (p i).val.card) (fun i _=> Nat.zero_le _) (mem_univ i)
  have hb (i) : Cash.numP (p i).val≤ overlap H z:= single_le_sum (f:=fun j=> Cash.numP (p j).val) (fun _ _=> Nat.zero_le _) (mem_univ i)
  have hdep i : H.shapeW (p i).val ≤ depth H z := single_le_sum (f:=fun j=>H.shapeW (p j).val) (fun j _=> H.positive_volume _) (mem_univ i)
  have hx : breadth H z ≤ K := by have hi:= hh.1; unfold degree at hi; omega
  constructor
  · intro i
    have hp:= (hg i).2
    have hχ : (p i).val.toLeft=∅ := Finset.not_nonempty_iff_eq_empty.mp (by
      rintro ⟨b,hb'⟩
      have hh₁ : 1≤ b.shares:= by rw [← Packets.seeds_card]; exact Finset.card_pos.mpr (hp.1.checkpoints b hb').1
      have h' := hh₁.trans (show b.shares ≤ Cash.numP (p i).val from single_le_sum (f:=Mixed.shares S) (fun _ _=> Nat.zero_le _) (mem_toLeft.mp hb'))|>.trans (hb i)
      have h0:=hh.2.1
      omega)
    refine ⟨(hg i).1,hp,hχ,?_,(hg i).1.1,(he i).trans hx,(hdep i).trans_lt hh.2.2⟩
    refine Finset.not_nonempty_iff_eq_empty.mp ?_
    rintro ⟨j,hi⟩; obtain ⟨b,hB⟩:= (R.activities.forced j).inventory_ne
    obtain ⟨e,hv,hE⟩:= hp.2.2 j hi b hB
    unfold roster Packets.store at hv
    rw [hχ] at hv; simp at hv
  have ha : z.fst+1 ≤ breadth H z:= by
    refine le_trans ?_ (Finset.sum_le_sum (s:=univ) (fun i _=> Finset.card_pos.mpr (hg i).1.1))
    simp
  exact ha.trans hx

namespace Narrow
variable {K : ℕ}{ℓ:ℝ}{p:H.ThinP}(h:Narrow K ℓ p)
include h
lemma unmaskedLetters (i : Head S)(hi:i∈p.val) :
    ∃ u : ConnectedActivityE6.Coat.LogIndex c f ⊕ ConnectedActivityE6.WarningAt c f,
      i = Sum.inr (Sum.inr u) := by
  cases i with
  | inl b=>
    have hh : b∈ p.val.toLeft := mem_toLeft.mpr hi
    rw [h.unforced] at hh; simp at hh
  | inr x=> cases x with
    | inl t=> have ht:= (Matter.literal p.val t).mpr hi; rw [h.noK] at ht; simp at ht
    | inr t=> exact ⟨t,rfl⟩

lemma cover_bound : (coverNumber (radiusB s) (H.unionP p.val):ℝ) < ℓ:=
  (shaped p.val h.connected).trans_lt h.setPrice

lemma leg_bound (i : Head S)(hi:i∈p.val) : (coverNumber (radiusB s) (H.supportP i):ℝ)+
    Mixed.lengths S H.faresP (ConnectedActivityE6.lengths T R) i < ℓ:= by
  apply lt_of_le_of_lt _ h.setPrice
  apply Finset.single_le_sum (f:=fun v=> (coverNumber (radiusB s) (H.supportP v):ℝ)+ Mixed.lengths S H.faresP (ConnectedActivityE6.lengths T R) v) (fun i _=> ?_) hi
  refine add_nonneg (Nat.cast_nonneg _) ?_
  rcases i with i|i
  · exact mul_nonneg H.laws.acquired.extra (Nat.cast_nonneg _)
  exact Nat.cast_nonneg _

lemma bareLayout : roster p.val= AnalyticBridge.LocalGaussianLaws.bareStores S:= by
  unfold Matter.roster; rw [h.unforced]; rfl

open Coat Pulse Matter Poll Pond Polar in
/-- No implicit compulsory integration left at survivors: write the exact
remaining unmasked leaflet on the bare roster, including gauge averaging.
Subsequent analytic proofs can instead use `rainbow` to omit that average
near a healthy V, but must retain it in any global address equality. `bars`
still includes its conditional law and the real profiles. -/
theorem unfoldsLeaf (V : Config G c) :
    leaflet H χ V p = Pond.likely (fun i : Greenbelt.Reserve S=>
      let X:=prism T s χ o.K V (Greenbelt.allot i)
      ∫ z, Pond.likely (fun a:S.Choices=> Shield.bars (podium S G (H.unionP p.val) (radiusB s))
        ((preps (X.rinse z) (AnalyticBridge.LocalGaussianLaws.bareStores S)).taggedL a) p.val R Q.table W o.a Q.halo) ∂ Measure.pi (fun _:Site c=>G.probHaar)):= by
    unfold leaflet fringe Shield.shelter Shield.seating
    have hX (i : Greenbelt.Reserve S) (z : Site c→G.El): ((prism T s χ o.K V (Greenbelt.allot i)).rinse z).B=radiusB s:=rfl
    simp_rw [hX,if_pos (show Ac.Spark (areas R T Q.halo (radiusB s)) p.val ∧ troupe T R Q.halo (radiusB s) p.val from ⟨h.connected,h.enters⟩),h.bareLayout]; rfl

end Narrow
end YM.RG01.Survive
