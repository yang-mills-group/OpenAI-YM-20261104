import YM.LocalTaylorR2.Edition
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Rhyme
/-!
 # Local marked log ruler

 Unconditional for `Leaf` at either eligibility. No extra smoothness assumption
 on the *marker*. In fact its profile in the `floret` calculation is measured
 (masked). When crossing under a collar, `Glaze.changes` rotate noisy Y rather
 than varying the actual F on an opened map. Each moment remains shared with
 seed/sign/gauge/o.F boxes of the retained vacuum alphabet. Recharges insertions
 of log occupancies (same as in I), with permanent inventory. Later using this
 as auxiliary norm for full Mark output.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Marker
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Leaf R) (X:Coat T F) (H:Cash W x μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G}

local notation "i₀" => M.turn.badge S

abbrev stems (_H:Cash W x μ L Q o C T R): Port.Test T:= fun _ X w=> M.paidU X o.a (worldZ X R.beta w)

lemma stemEq (i:Finset ℕ) (u:Air f G): M.floret X {i₀} W o.a Q.table i Q.halo u=stems M H F X u:=by simp only [Leaf.floret,Finset.mem_singleton,erase_singleton,Polar.floating,prod_empty,if_true,mul_one]

lemma stemTest : Port.Kept H (H.supportP (i₀)) (stems M H) := by
  constructor
  · intro F X X' w v ht hK Z hh hl hV
    have hr : Intake P T X.x R:= ht.symm ▸ H.laws.intake
    have he : Room P S T X.x:= ht.symm ▸ H.laws.data.room
    have hx : ground R T Q.halo X.B {i₀}⊆Z := by unfold ground Coat.B; rw [singleton_biUnion,ht]; exact hh
    rw [← stemEq M X H ∅, ← stemEq M X' H ∅]
    exact M.census X _ hr he Q.buys (show Borough X X' Z w v ∅ ∅ R from ⟨hl,(observe _).1 hV,fun _ _=> Iff.rfl⟩) hx
  · intro E _ F X hx hk V Y w hp hv ht
    have hr : Intake P T X.x R:= hx.symm ▸ H.laws.intake
    simp_rw [← stemEq M _ H ∅]
    exact M.drift_b X _ _ _ _ (show ShellAccess S G X.x W X.width o.γ from (by rw [hx,hk]; exact H.laws.data.access)) hr Q.table_exists hp hv ht
  · intro F X hx hk hp z w
    have h : ShellAccess S G X.x W X.width o.γ:=by rw [hx,hk]; exact H.laws.data.access
    have hr : Intake P T X.x R:= hx.symm ▸ H.laws.intake
    unfold stems; rw [Stained.flight X z hr.ready h]; unfold Leaf.paidU Leaf.fond
    rw [Hues.banks X z _, M.glows]; exact congr_arg _ (show _=X.enforce _ _ _ from Hues.mandate X z (2*o.a) _ (X.plaza _))
  intro F X hx hk hp j b A E _ _ _ V x0 hq hz hA
  rw [← H.laws.data.funds.length_eq,← hx] at hA
  simp_rw [← stemEq M _ H (own ({i₀}:Molecule S))]
  exact M.supple _ _ (show Cash W X.x μ L Q o C T R from hx.symm ▸ H) hq hz hA

abbrev partners (M:Leaf R)(p:Molecule S): Molecule S:= p.erase (M.turn.badge S)
def treads (p:H.ThinP):Prop:= Candle.vetted H p ∧ i₀ ∈ p.val
-- no requirement that Badge itself is a log. Allows sharp bound through scaled reserve for actual input.
def lush (p:H.ThinP):Prop:= treads M H p ∧ Clear (partners M p.val)

lemma sees_set {p:H.ThinP} (h:treads M H p) : H.supportP (i₀) ⊆ H.smallAt p:=subset_biUnion_of_mem _ (h.2)

def hero (p:Molecule S):Port.Test T:= fun F X w=> stems M H F X w * compound H (partners M p) F X w
def team {k:ℕ} {p:H.ThinP} (q:Paint (partners M p.val) k):Port.Test T:= fun F X w => stems M H F X w * letters H q F X w

lemma enough {p:H.ThinP}: H.unionP (partners M p.val)⊆ H.smallAt p:= Finset.biUnion_subset.mpr (fun _ hi=> subset_biUnion_of_mem _ (Finset.mem_of_mem_erase hi))

lemma heroKept {p:H.ThinP}(h:treads M H p): Kept H (H.smallAt p) (hero M H p.val) := ((stemTest M H).mono (sees_set M H h)).times ((compSect H (partners M p.val)).mono (enough M H))
lemma teamKept {p:H.ThinP}(h:treads M H p)(q:Paint (partners M p.val) m): Kept H (H.smallAt p) (team M H (p:=p) q) := ((stemTest M H).mono (sees_set M H h)).times (letterSect H q _ (enough M H))

lemma squad (k:ℕ){p:H.ThinP}(w:Air f G): hero M H p.val F X w=∑ q:Paint (partners M p.val) k, team M H (p:=p) q F X w:=by unfold hero team; rw [running H k, Finset.mul_sum]

lemma floret_eq (h: Pure (partners M p)) (he : (i₀) ∈ p)(w:Air f G): M.floret X p W o.a Q.table k Q.halo w=hero M H p F X w:= by unfold Leaf.floret hero; rw [if_pos he,test_eq H k h]

lemma income (V : Config G c) (χ : Chi) {p:H.ThinP}(ha:treads M H p) (ht : Clear (partners M p.val)): Charity.libs M H χ V p = episode H χ p.val (hero M H p.val) V := by
  apply congr_arg likely; funext r; apply integral_congr_ae; filter_upwards with z
  let X:=(prism T x χ o.K V (Greenbelt.allot r)).rinse z
  change M.grove X p.val W o.a Q.table Q.halo=onFrame X p.val (H.unionP p.val) _
  rw [Leaf.grove,if_pos ⟨ha.1.1,ha.1.2⟩]; apply congr_arg likely; funext k
  unfold Port.average Leaf.cinema; simp_rw [floret_eq M _ H (isPure ht) ha.2]; rfl

lemma halt (V:Config G c) (χ:Chi){p:H.ThinP}(h:¬treads M H p): Charity.libs M H χ V p=0:=by
  let K' i:=(prism T x χ o.K V (Greenbelt.allot i)); letI : Nonempty (Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
  have he(r:Greenbelt.Reserve S): M.picture (K' r) p.val W o.a Q.table Q.halo=0:=by
    have hy z:M.grove ((K' r).rinse z) p.val W o.a Q.table Q.halo=0:=by
      unfold Leaf.grove; split
      next ht =>
        have hv:¬ (i₀)∈p.val:=fun hu=> h ⟨ht,hu⟩
        unfold Leaf.cinema Leaf.floret likely; simp only [if_neg hv, mul_zero,integral_zero,sum_const_zero]
      rfl
    unfold Leaf.picture; simp_rw [hy,integral_zero]
  unfold Charity.libs Daisy.escort; change likely (fun i=> M.picture (K' i) _ _ _ _ _)=0
  simp_rw [he]; exact Greenbelt.likely_constant _
end YM.LocalTaylorR2.Marker
