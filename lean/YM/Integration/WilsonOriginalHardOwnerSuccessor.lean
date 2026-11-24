import YM.Integration.WilsonOriginalHardOwnerReweight

/-! The countable forced output of the original Wilson block already records
the incoming operand of each occurrence. A numerical weight on that operand
commutes with its complete signed field value. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalHardOwnerSuccessor
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves Merge Palette Next.Scheduling
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Mosaic RemainderComparison.Muse
open RemainderComparison.Sleet RemainderComparison.Serif RemainderComparison.Typeface RemainderComparison.Flues
open Marker Mallow Ovens Progress.DirectedRecipe WilsonOriginalHardOwnerReweight
open scoped Topology BigOperators Classical

variable {ι : Type} {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G}
    {T : Tube G S} {R : Rep G f} {W x μ C d e a K σ Y γ v t τ θ : ℝ} {Q : ConnectedActivityE6.Target G P}
    {o : ConnectedActivityE6.Target.Order G W} {depth k j s J I : ℕ}
variable (use : ι → Prop)

def named (letters : Multiset ι) : Prop := ∃ i∈letters,use i

def factor (θ : ℝ) (depth : ℕ) (letters : Multiset ι) : ℝ :=
  (letters.map (raise use θ depth)).prod

theorem reserve (hθ : 0≤θ) (letters : Multiset ι) :
    1 ≤ factor use θ depth letters ∧
    (named use letters → Real.exp (θ*depth) ≤ factor use θ depth letters) := by
  induction letters using Multiset.induction_on with
  | empty => simp [factor,named]
  | cons i l ih =>
    have hi : 1≤raise use θ depth i := by
      unfold raise; split
      · exact Real.one_le_exp (mul_nonneg hθ (Nat.cast_nonneg _))
      · exact le_rfl
    rw [show factor use θ depth (i ::ₘ l)=raise use θ depth i*factor use θ depth l by
        simp [factor]]
    refine ⟨one_le_mul_of_one_le_of_one_le hi ih.1,?_⟩
    rintro ⟨z,hz,used⟩
    rcases Multiset.mem_cons.mp hz with h|h
    · subst z
      rw [raise,if_pos used]
      exact le_mul_of_one_le_right (Real.exp_pos _).le ih.1
    · exact (ih.2 ⟨z,h,used⟩).trans (le_mul_of_one_le_left (zero_le_one.trans ih.1) hi)

variable {α : Type*}
def marked (stock : Yard ι α G c) : Yard ι α G c :=
  {stock with glow := fun u i Z => if named use (stock.score i) then stock.glow u i Z else 0}

variable (H : Cash W x μ L Q o C T R) (χ : Chi) (U : Pad H j χ)
    (M : ι → Portrait R α) (u : α)
    (h : Roles H χ U k s J I a d e K σ Y γ v t)
    {R' : Rep G f} (H' : Cash W x μ L Q o C T R') (D : Match.Alliance H' H 1 0)
    (E : ℕ → RegularAddress c) (b : ℕ → Config G c → ℝ) [Countable ι]
local notation "K₁" => kettle H χ M u (fun _=>1) Set.univ 0 H' D E b
local notation "K₂" => kettle H χ M u (raise use θ depth) Set.univ 0 H' D E b

/-- The old forced address, tag and complete physical cofactor are the same
on both sides, including the real or imaginary choice of a marked input. -/
theorem literal (y : α) (i : ℕ) (Z : Config G c) :
    (K₂).glow y i Z = factor use θ depth ((K₁).score i) * (K₁).glow y i Z := by
  let embed := funnel H M u H' D
  by_cases hin : i∈Set.range embed
  · obtain ⟨p,rfl⟩:=hin
    unfold kettle
    dsimp only
    rw [stuffed,stuffed,stuffed]
    have fixed (r:ι→ℝ) : sits Set.univ r 0 = r := by
      funext i; simp [sits,Verse.marked]
    rw [fixed,fixed,Flues.written H χ M u y p]
    simp [Verse.emit,Verse.stock,factor]
  · unfold kettle
    dsimp only
    rw [blank _ _ hin,blank _ _ hin,blank _ _ hin]
    simp

include U h in
/-- The manuscript's first coarsening return for a genuine marked forced
occurrence, in the original countable inventory and at full outgoing support
width. The native hard allowance occurs once. -/
theorem received (hθ : 0≤θ) (hh : Motto (brand M u) (raise use θ depth) 0 H τ K Y I)
    (out : BudgetPoint) (width : out.B=radiusB x) :
    Yard.Pays (marked use K₁) Set.univ k out.B a
      (Real.exp (-(θ*depth))*(Real.exp ((-Q.mark L μ x)*(1/2:ℝ))*(gStep R.beta)^s)) := by
  obtain ⟨bill,pos,price,reads⟩ :=
    (Flues.silk H χ U M u (raise use θ depth) Set.univ 0 h hh H' D E b out width).wages
  let refund := Real.exp (-(θ*depth:ℝ))
  have hr : 0≤refund := (Real.exp_pos _).le
  refine ⟨fun i=>refund*bill i,fun i=>mul_nonneg hr (pos i),?_,?_⟩
  · intro y
    convert Extra.Multi.Budget.scale (price y) hr using 1
    apply funext
    intro i
    change (if y∈(K₁).plane i then _ else 0)=refund*(if y∈(K₁).plane i then _ else 0)
    split
    · exact mul_assoc refund (bill i) (Real.exp (a*coverNumber out.B ((K₁).plane i)))
    · exact (mul_zero _).symm
  · intro i low y Z
    change ‖if named use ((K₁).score i) then (K₁).glow y i Z else 0‖ ≤ refund*bill i
    split
    next used =>
      have paid := reads i low y Z
      rw [literal use H χ M u H' D E b y i Z,norm_mul,
        Real.norm_of_nonneg (zero_le_one.trans (reserve use hθ ((K₁).score i)).1)] at paid
      have result := (mul_le_mul_of_nonneg_right ((reserve use hθ ((K₁).score i)).2 used)
        (norm_nonneg ((K₁).glow y i Z))).trans paid
      change _ ≤ Real.exp (-(θ*depth))*bill i
      rw [Real.exp_neg,←div_eq_inv_mul]
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      rwa [mul_comm]
    next => simpa only [norm_zero] using mul_nonneg hr (pos i)

end YM.Integration.WilsonOriginalHardOwnerSuccessor
end
