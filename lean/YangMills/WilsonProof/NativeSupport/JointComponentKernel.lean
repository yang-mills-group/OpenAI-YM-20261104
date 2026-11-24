import YangMills.WilsonProof.NativeSupport.JointMoleculeKernel
import YangMills.WilsonProof.NativeSupport.JointForest

/-! The measured mounted molecule has the original common local sector and the
same value when its unobserved forest is changed. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 25000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointTicket
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations
open SectorMeasure Oriented Work.E03 Mask Contract Work.F03 Presented LabelSum Sector Footprint
open Packets SliceRows Control Window Pulse Coat Matter Itinerary Census Horticulture ProbabilityTheory Poll Pond
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus JointCoat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {F : Forest S.ratio} {R : Rep G f} {W μ C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}
variable (M : Team R) (X : Coat T F) (J : Finset (Bond c)) (probe : Bond c→ℝ→ℝ)
def steep (k : Finset ℕ) (W a : ℝ) (Ñ : ChartRatio G) (m : ℕ) (p : Molecule S) :=
  likely fun v=>tithe M (X.taggedL v) J probe k W a Ñ m p
def bloom (W a : ℝ) (Ñ : ChartRatio G) (m : ℕ) (p : Molecule S) :=
  if standsIn X R m p then steep M (planted X p) J probe (Matter.own p) W a Ñ m p else 0

theorem tithe_off (k : Finset ℕ) (W a : ℝ) (Ñ : ChartRatio G) (m : ℕ) (p : Molecule S)
    (off : ¬M.signs S⊆p) : tithe M X J probe k W a Ñ m p=0 := by
  have zero (v : F.Slice G×Air f G) : raw (W:=W) M X k p a Ñ m J probe v=0 := by
    change _*(if M.signs S⊆p then _ else 0)=0
    rw [if_neg off,mul_zero]
  unfold tithe
  simp only [zero,integral_zero]

variable (H : Cash W X.x μ L Q o C T R) (hk : X.width=o.K)
variable (mh : ∀ b∈J,Measurable (probe b)) (unit : ∀ b∈J,∀ e∈Set.Icc 0 (linkCap S),‖probe b e‖≤1)
variable (V : Finset (Molecule S)) (h : joints T R Q.halo X.B V) {p : Molecule S}
private lemma plant_area {l : ℕ} (h : claimed X R l p) (o : Site c) (hp : o∈ ground R T l X.B p) :
    o∈ (planted X p).seeds.place ↔ o∈(roster p).place := by
  have he := h.2; unfold place; simp only [preps,planted,mem_union]; rw [← he,mem_inter]; simp [hp]

include H hk mh unit h in
theorem scents (fresh : ∀ b∈J,zone S X.B b⊆H.unionP p) (he : Matter.covers X V) (hi : p∈V) (hy : standsIn X R Q.halo p)
     : bloom M X J probe W o.a Q.table Q.halo p=steep M (preps X (roster (V.biUnion id))) J probe (Matter.own (V.biUnion id)) W o.a Q.table Q.halo p := by
  let Y:= planted X p; let A:= V.biUnion id; let Y':=preps X (roster A); let s:= H.unionP
  have hm : Y'.manifest := by unfold manifest Y' preps A; rw [totals]; exact he
  rw [bloom, if_pos hy];
  unfold steep; apply congr_arg likely; funext k
  have hl : (V:Set _).PairwiseDisjoint s := h.2
  have hv i (hc : i∈ V) (o) (hx : o∈s p) (hy : o∈ s i) : p=i := by
    by_contra hn; exact Finset.disjoint_left.mp (hl hi hc hn) hx hy
  have hp (x) (hx : x∈ s p) : x∈ (roster p).place ↔ x∈(roster A).place := by
    rw [← Packets.place_reads,← Packets.place_reads]; constructor
    · intro h; obtain ⟨v,hv,h⟩ := mem_biUnion.mp h
      exact mem_biUnion.mpr ⟨v,(star_sizes V _).2 ⟨p,hi,hv⟩,h⟩
    intro h; obtain ⟨j,hj,h⟩ := mem_biUnion.mp h; obtain ⟨i,hi,hb⟩ := (star_sizes V _).1 hj
    refine mem_biUnion.mpr ⟨j,(hv i hi _ hx (claim_zoneA R T _ _ i _ hb h)).symm ▸ hb,h⟩
  refine marginal (X:=Y.taggedL k) (Y:=Y'.taggedL k)
    (k:=Matter.own p) (l:=Matter.own A) (p:=p) M H J probe hk (planted_valid X p) hm mh unit
    ⟨rfl,rfl,rfl,fun i hi=> (plant_area X hy.2 i hi).trans (hp i hi), fun _ _=>rfl,
      fun _ _=> rfl, fun _ _=>rfl,fun _ _ _=> rfl⟩ fresh ?_
  intro i hj; constructor
  · intro hh; obtain ⟨j,hv,hh⟩ := mem_biUnion.mp hh; exact mem_biUnion.mpr ⟨j,(gloss V _).2 ⟨p,hi,hv⟩,hh⟩
  intro hq; obtain ⟨b,hb,hx⟩ := mem_biUnion.mp hq; obtain ⟨v,hb,hk⟩ := (gloss V _).1 hb
  exact mem_biUnion.mpr ⟨b,(hv v hb _ hj (claim_zoneK R T _ _ v _ hk hx)).symm ▸ hk,hx⟩

variable {F' : Forest S.ratio} (Y : Coat T F') (p : Molecule S)
variable (width : Y.width=o.K) (weather : Y.x=X.x) (held : X.V=Y.V) (chi : X.χ=Y.χ)
variable (wood : ∀ i : Site f,S.ratio.parent i∈H.unionP p → F.up i=F'.up i)
variable (fresh : ∀ b∈J,zone S X.B b⊆H.unionP p)
include hk width weather held chi H wood mh unit fresh in
private theorem forest_steep (k : Finset ℕ) (seed : X.seeds=Y.seeds) (good : X.manifest) (good' : Y.manifest) :
    steep M X J probe k W o.a Q.table Q.halo p=steep M Y J probe k W o.a Q.table Q.halo p := by
  apply congrArg likely
  funext z
  exact forest_marginal M (X.taggedL z) (Y.taggedL z) p hk width weather held chi H wood seed rfl good good' k J probe mh unit fresh

include hk width weather held chi H wood mh unit fresh in
private theorem forest_planted :
    steep M (planted X p) J probe (Matter.own p) W o.a Q.table Q.halo p=
      steep M (planted Y p) J probe (Matter.own p) W o.a Q.table Q.halo p := by
  let a:=planted X p
  let b:=planted Y p
  have same : a.seeds=b.seeds := by unfold a b planted preps; dsimp only; rw [held,weather]
  exact forest_steep M a J probe H hk mh unit b p width weather held chi wood fresh
    (own p) same (planted_valid X _) (planted_valid Y _)

include hk width weather held chi H wood mh unit fresh in
theorem forest_bloom :
    bloom M X J probe W o.a Q.table Q.halo p=bloom M Y J probe W o.a Q.table Q.halo p := by
  unfold bloom
  have he : standsIn X R Q.halo p↔standsIn Y R Q.halo p := by unfold standsIn claimed Coat.B; rw [held,weather]
  exact if_congr he (forest_planted M X J probe H hk mh unit Y p width weather held chi wood fresh) rfl

end YM.Integration.InletSusceptibility.JointTicket
