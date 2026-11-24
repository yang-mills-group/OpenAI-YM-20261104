import YM.Integration.FVA1Physical.Marked.SignedLedger

/-! A support- and derivative-weighted, countable bound for the signed bank
omitted by the actual finite marked ledger. Keep the opened support exponent,
source dilation and original signed regular rows. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Filter Function Lattice RG Pressure Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AnalyticBridge VerifiedReset Collection
open Progress.DirectedRecipe Roof Extra.Iteration Time ThroughLaunch Roost JointLoad RGComparison.Core16
open RGComparison01 RGComparison01.Pledge Holdings Merge Qlocal Qlocal.Parabola
open AllOrder Transit WheelP Floe Floe.Step.PlanV Push.PriceCompiler RG.Supply Input Org
open MeasureTheory Canopy Leasing Marker Extra.Trajectories Comparison.RG02.Order
open scoped BigOperators Classical Topology

variable {G : Gauge} {X : Run G} {z N n k m : ℕ} {path : ℕ → Floe.Layout G} {Γ : ℕ → Pace.Coin}
    {x : (i : ℕ) → Rep G (X.alloy.B.a.S.side i n)}
    (track : Metre X.alloy X.kit X.T path Γ z N n k x) (lo : z ≤ m) (hi : m < N)
    {ι : Type} [Fintype ι] (M : ι→Lotus.Leaf (x (m+1))) (g : ι→ℝ)
    (H : Opera.Guide X.alloy.B X.kit.shape N m n (x (m+1)))
    (hH : Opera.Price X.alloy.B X.kit.shape N m n (x (m+1)) H)
    {k₀ j₀ : ℕ} (η : ℕ→ℝ) (B₀ : Bauble G (X.rolls.L (X.alloy.B.a.clock.J (m+1))))
    (funds : Opened X.kit η k₀ j₀ m B₀) (regular : Staircase.grows M)
local notation "π₀" => (X.alloy.B.a.S.oneStep m n).exact_size
local notation "p" => X.alloy.B.a.budget m
local notation "χ₀" => Chi.canonical
local notation "β₀" => X.alloy.B.a.clock.hatBeta m
local notation "Λ" => X.rolls.L (X.alloy.B.a.clock.J (m+1))
local notation "τ" => (X.kit.expense (X.alloy.B.a.clock.J (m+1)) (X.alloy.B.a.clock.J m)).earn

include track lo hi hH funds regular in
/-- Any ribbon actually admitting the inherited bank and containing the
selected source slots gives the countable native support/derivative bill for
the residual in the signed low-catalog identity. -/
theorem signed_tail_budget {d : ℕ} (ribbon : Ribbon (x (m+1)) d) (Ψ : ℕ→Prop)
    {e : ℝ} (income : (Tithe.portion (x (m+1)).activities Ψ).EBound (x (m+1)).p e)
    (allowed : e ≤ incomingE G Λ β₀) (opens : Drawing.Opens ribbon Ψ)
    (short : ∀ i, ¬ Luggage.long M ribbon i) {slack : ℝ} (pos : 0<slack) :
    let a := commonAperture M (B₀.mass β₀)
    let r := Fintype.card ι
    let cost := B₀.miss β₀*e + B₀.roi β₀/(Height.grow G Λ β₀)^k₀ + slack
    ∀ᶠ depth in atTop, ∀ s : Finset ι, s.Nonempty →
      let signed := ∏ i∈s,g i/a
      Checks.Rooted (Baked.origins M H)
        (fun z=> signed • Bridges.balance M (fun _=>a) H ribbon (j₀+r) depth s (χ:=χ₀) z)
        p τ (abs signed * cost) := by
  intro a r cost
  have band : (x (m+1)).beta ∈ RG.Shoot.band X.alloy.B.a (m+1) := by
    rw [(track.1.walk (m+1) (by omega) hi).beta]
    exact ((X.T.sticks N n).prices (m+1) (Nat.zero_le _) hi).2
  obtain ⟨_,admittedMass⟩ := common_aperture M regular (funds.paid _ (X.alloy.B.valid.pays m)).permission.crucial
  let leaves := fun _:Unit=>M
  let roster : Roster M leaves := ⟨fun _ _=>rfl,fun _ _=>rfl⟩
  have admitted := accounts X.kit η B₀ funds π₀ H hH hi band roster (fun _=>a) admittedMass income allowed
    ribbon (fun _=>True) r opens (fun _ _ i _=>short i) pos
  filter_upwards [admitted] with depth paid
  intro s hs signed
  have cut : (fun z : Baked.Cl M H=>Luggage.miss M H ribbon r (j₀+r) depth z ∧ True) =
      Luggage.miss M H ribbon r (j₀+r) depth := funext fun _=>and_true _
  have trimmed := (congrArg (fun mask : Baked.Cl M H→Prop => UniformRooted (Baked.origins M H)
    (crop H roster (fun _=>a) mask χ₀) p τ cost) cut).mp paid
  have coarse : Checks.Rooted (Baked.origins M H)
      (Checks.treat (Luggage.miss M H ribbon r (j₀+r) depth) (ρ:=fun _=>a) (χ:=χ₀)) p τ cost :=
    roster.miss H ribbon p () (j₀+r) depth r trimmed
  have bank : Checks.Rooted (Baked.origins M H)
      (Bridges.balance M (fun _=>a) H ribbon (j₀+r) depth s (χ:=χ₀)) p τ cost := by
    apply coarse.fresh
    intro z
    unfold Bridges.balance Checks.treat
    split
    next hy =>
      rw [if_pos (Bridges.universal M H ribbon s depth z hy (Finset.card_le_univ s) hs)]
      exact Or.inl rfl
    next => exact Or.inr rfl
  exact bank.scales (fun _=>signed) (fun _=>le_rfl) (abs_nonneg _)

def torusWidth (n:Side) : ℕ := (Finset.univ : Finset (Site n × Site n)).sup (fun v=> separation v.1 v.2)

/-- Exhaust all incoming regular rows on a fixed finite torus. Its allowed
radius scales with the torus; quantitative local-ribbon applications should
use the previous theorem when period-uniform locality is needed. -/
def torusRibbon {f:Side} (P : Rep G f) : Ribbon P (torusWidth f) where
  keep _ := True
  ride i := i.val
  finite j := by
    let s := Finset.range (j+1)
    let lift := fun i:ℕ => (⟨i,True.intro⟩:{v:ℕ // True})
    refine (s.finite_toSet.image lift).subset ?_
    intro i hi
    exact ⟨i.val,Finset.mem_range.mpr (Nat.lt_succ_of_le hi),Subtype.ext rfl⟩
  radius i _ := by
    intro y _
    apply (Animals.neighbors_mem ..).2
    exact Finset.le_sup (f:=fun q : Site f × Site f => separation q.1 q.2) (Finset.mem_univ ((P.activities.reg i).site,y))

include track lo hi hH funds regular in
/-- A compact finite torus permits the preceding complete-norm estimate
without an input income, a geometry sub-witness or a source incidence
assumption. The catalogue depth may vary with the particular torus. -/
theorem fixed_torus_tail {slack : ℝ} (pos : 0<slack) :
    let a := commonAperture M (B₀.mass β₀)
    let r := Fintype.card ι
    let cost := B₀.roi β₀/(Height.grow G Λ β₀)^k₀ + slack
    ∀ᶠ depth in atTop, ∀ s : Finset ι, s.Nonempty →
      let signed := ∏ i∈s,g i/a
      Checks.Rooted (Baked.origins M H) (fun z=> signed • Bridges.balance M (fun _=>a) H
        (torusRibbon (x (m+1))) (j₀+r) depth s (χ:=χ₀) z) p τ (abs signed * cost) := by
  let ribbon := torusRibbon (x (m+1))
  have opens : Drawing.Opens ribbon (fun _=>False) :=
    ⟨fun _ h=>h.elim,fun _ _ hk=> (hk True.intro).elim⟩
  have short (i) : ¬Luggage.long M ribbon i := by
    rintro ⟨_,_,hk⟩
    exact hk True.intro
  simpa only [mul_zero,zero_add] using signed_tail_budget track lo hi M g H hH η B₀ funds regular ribbon
    (fun _=>False) (Skating.Rune.falseB ..) (Skating.Rune.freeK ..) opens short pos
end YM.Integration.FVA1Physical.Marked
