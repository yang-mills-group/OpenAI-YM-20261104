import YM.Integration.FVA1Physical.Marked.CumulantCell
import YM.Qlocal.Skating.Cricket

/-! Identify the actual finite retained marked ledger and its signed
omitted-cluster bank on the same run, guide and source directions as the
physical vacuum. The input source mass is the opened physical lease. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2200000
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
    (T : Slices X.family.path.levels n)
    {ι : Type} [Fintype ι] (M : ι→Lotus.Leaf (x (m+1))) (g : ι→ℝ)
    (H : Opera.Guide X.alloy.B X.kit.shape N m n (x (m+1)))
    (hH : Opera.Price X.alloy.B X.kit.shape N m n (x (m+1)) H)
    {k₀ j₀ : ℕ} (η : ℕ→ℝ) (B₀ : Bauble G (X.rolls.L (X.alloy.B.a.clock.J (m+1))))
    (funds : Opened X.kit η k₀ j₀ m B₀)
    (sourceMass : Bench M g (B₀.mass (X.alloy.B.a.clock.hatBeta m)))
    (regular : Staircase.grows M) (inj : Injective fun i => (M i).turn)
local notation "σ" => (X.alloy.B.a.S.oneStep m n).exact_size
local notation "op" => X.family.path.levels.clock.op m n
local notation "p" => X.alloy.B.a.budget m
local notation "χ₀" => Chi.canonical
local notation "bank" => Reels.allotV M g H (χ:=χ₀)
local notation "B" => Button.universeP ι

include track lo hi hH funds sourceMass regular in
/-- Both the actual cluster-log identity and its retained ledger plus signed
omitted rows obtain their activation from one funded guide. The signed-mask
identity holds for arbitrary retained fields, also when flags are present. -/
theorem funded_ledger :
    Still.Coastal M g H (χ:=χ₀) p ∧
    ∀ {d : ℕ} (ribbon : Ribbon (x (m+1)) d) (s : Finset ι), s.Nonempty →
      ∀ (degree depth : ℕ) (V : Config G (X.family.side m n)),
        let tail := ∑' a:Baked.Cl M H, masked (p).threshold (Baked.origins M H a)
          (Bridges.balance M g H ribbon degree depth s (χ:=χ₀) a) V
        let cabinet := Drawing.cabinet H ribbon
        bank s V = Stowe.ship M g H cabinet degree depth s V (χ:=χ₀) + tail ∧
        (flags (p).threshold V = ∅ → bank s V = Stowe.tale M g H cabinet degree depth s V (χ:=χ₀) + tail) := by
  have band : (x (m+1)).beta ∈ RG.Shoot.band X.alloy.B.a (m+1) := by
    rw [(track.1.walk (m+1) (by omega) hi).beta]
    exact ((X.T.sticks N n).prices (m+1) (Nat.zero_le _) hi).2
  let leaves := fun _:Unit=>M
  let roster : Roster M leaves := ⟨fun _ _=>rfl,fun _ _=>rfl⟩
  have hR := resourceT X.kit η B₀ funds σ H hH hi band roster g sourceMass
    (Skating.Rune.falseB ..) (Skating.Rune.freeK ..) (Classical.choice (Tree.select (op).ratio (op).patch.odd_side))
  have earned := hR.2.1
  have shed : Lanes.Shed H M g p χ₀ := roster.stance H p () g earned.log_all earned.masking
  have native := roster.retag p g H χ₀ () earned.log_all
  have price := renter X.kit η B₀ funds σ H hi g sourceMass
  refine ⟨Tender.mission X.kit η B₀ funds σ H hH hi band M g sourceMass
    (Skating.Rune.falseB ..) (Skating.Rune.freeK ..) regular,?_⟩
  intro d ribbon s nonempty degree depth V tail cabinet
  have decomp := Bridges.alpine M g H p ribbon s nonempty rfl rfl shed.filtered native price depth degree V
  refine ⟨decomp,fun clear => decomp.trans ?_⟩
  exact congrArg (· + tail) (Lanes.garden H M g ribbon p shed V s clear)

include track lo hi hH funds sourceMass regular inj in
/-- On the actual physical step the low marked bank, restored by its explicit
signed omitted clusters, is exactly the joint cumulant of the actual source
readings over the full independently reconstructed Wilson vacuum history. -/
theorem low_ledger_history {d : ℕ} (ribbon : Ribbon (x (m+1)) d) (s : Finset ι) (nonempty : s.Nonempty)
    (degree depth : ℕ) (V : Config G (X.family.side m n)) (clear : flags (p).threshold V = ∅) :
    Stowe.tale M g H (Drawing.cabinet H ribbon) degree depth s V (χ:=χ₀) +
      (∑' a:Baked.Cl M H, masked (p).threshold (Baked.origins M H a)
        (Bridges.balance M g H ribbon degree depth s (χ:=χ₀) a) V) =
      Button.Earmark (fun t=>source_path_moment hi T M g t V) (Fintype.card ι) s := by
  obtain ⟨coast,ledger⟩ := funded_ledger track lo hi M g H hH η B₀ funds sourceMass regular
  have patch := ((ledger ribbon s nonempty degree depth V).2 clear).symm
  have logs := congrFun (Still.coast M g H regular coast V clear (le_refl (Fintype.card ι))) s
  exact patch.trans (logs.trans (congrArg (fun f=> Button.Earmark f (Fintype.card ι) s)
    (funext fun t=>projection_history track lo hi T M g inj t V)))
end YM.Integration.FVA1Physical.Marked
