import YangMills.WilsonProof.NativeSupport.JointTagProduct
import YangMills.WilsonProof.NativeSupport.JointSwitch

/-! Selection of the actual finite list of measurements carried by a mounted
numerical ticket. A repeated bond may be carried by several input leaves. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointLeaves
open Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations
open SectorMeasure Oriented Work.E03 Mask Contract Work.F03 Presented LabelSum Sector Footprint
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Merge Merge.Palette JointCoat
open scoped Classical BigOperators
variable {ι β : Type} [DecidableEq β] {w : ι→β}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {F : Forest S.ratio} {R : Rep G f} {W μ C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}

variable (J : ι → Finset (Bond c)) (h : ι → Bond c → ℝ → ℝ)

def bonds (I : Finset ι) := I.biUnion J
def probe (I : Finset ι) (b : Bond c) (e : ℝ) :=
  ∏ i∈I, if b∈J i then h i b e else 1

theorem measurable_probe (I : Finset ι) (hm : ∀ i,∀ b∈J i,Measurable (h i b)) (b : Bond c) :
    Measurable (probe J h I b) := by
  apply Finset.measurable_fun_prod
  intro i _
  by_cases hb : b∈J i
  · simpa only [if_pos hb] using hm i b hb
  simp only [if_neg hb]
  exact measurable_const

theorem unit_probe (I : Finset ι) (unit : ∀ i,∀ b∈J i,∀ e∈Set.Icc 0 (linkCap S),‖h i b e‖≤1)
    (b : Bond c) (e : ℝ) (he : e∈Set.Icc 0 (linkCap S)) : ‖probe J h I b e‖≤1 := by
  unfold probe
  rw [norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  by_cases hb : b∈J i
  · simpa only [if_pos hb] using unit i b hb e he
  simp [hb]

theorem flatten (I : Finset ι) (v : Bond c→ℝ) :
    ∏ b∈bonds J I,probe J h I b (v b) = ∏ i∈I,∏ b∈J i,h i b (v b) := by
  unfold bonds probe
  rw [Finset.prod_comm]
  refine prod_congr rfl fun i hi => ?_
  calc
    _ = ∏ b∈J i,if b∈J i then h i b (v b) else 1 :=
      (prod_subset (subset_biUnion_of_mem J hi) (fun b _ out=> if_neg out)).symm
    _ = _ := prod_congr rfl fun b hb => if_pos hb

theorem by_components (I : Tickets w) (V : Finset (Finset β))
    (dis : (↑V : Set (Finset β)).PairwiseDisjoint (id : Finset β→Finset β))
    (covers : I.reach⊆V.biUnion id) (v : Bond c → ℝ) :
    ∏ b∈bonds J I.val,probe J h I.val b (v b)=
      ∏ p∈V,∏ b∈bonds J (I.select p).val,probe J h (I.select p).val b (v b) := by
  let part p := (I.select p).val
  have sets : I.val=V.biUnion part := by
    ext i
    constructor
    · intro hi
      obtain ⟨p,hp,hb⟩ := mem_biUnion.mp (covers (I.reaches_of hi))
      exact mem_biUnion.mpr ⟨p,hp,mem_filter.mpr ⟨hi,hb⟩⟩
    intro hi
    obtain ⟨_,_,hb⟩ := mem_biUnion.mp hi
    exact (mem_filter.mp hb).1
  have distinct : (↑V : Set (Finset β)).PairwiseDisjoint part := fun p hp q hq ne =>
    disjoint_left.mpr fun _ a b => disjoint_left.mp (dis hp hq ne) (mem_filter.mp a).2 (mem_filter.mp b).2
  simp_rw [flatten]
  rw [sets,Finset.prod_biUnion distinct]

theorem scope (X : Coat T F) (H : Cash W X.x μ L Q o C T R) (M : ι→Lotus.Leaf R)
    (root : ∀ i,∀ b∈J i,S.ratio.embed b.1∈(M i).crest)
    (I : Tickets (Palette.sign M S)) (p : Molecule S) (inside : I.reach⊆p) :
    ∀ b∈bonds J I.val,zone S X.B b⊆H.unionP p := by
  intro b hb
  obtain ⟨i,hi,bi⟩ := mem_biUnion.mp hb
  apply (zone_in_badge (X:=X) H (M i) b (root i b bi)).trans
  exact subset_biUnion_of_mem _ (inside (I.reaches_of hi))

end YM.Integration.InletSusceptibility.JointLeaves
