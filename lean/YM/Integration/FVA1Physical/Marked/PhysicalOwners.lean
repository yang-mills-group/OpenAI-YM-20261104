import YM.Integration.FVA1Physical.Marked.SeparatedOwners

/-! On the purchased trajectory the exact occurrence expands into labelled
physical host blocks. Their separate native invoices are uniform under arbitrary
relative translations of the source positions. Empty vacuum hosts are retained
as their original amplitudes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Finset Pressure Marker Qlocal Quipu Quipu.Sonnet Tern
open Push.AbsoluteSums
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {M Ω I : Type} [Fintype M]

def touched (π : M → ℕ) := univ.image π
def fibre (π : M → ℕ) (i : ℕ) := univ.filter (fun t => π t = i)

/-- Fixed assignment in the occurrence sum, grouped exactly by host.
The unselected vacuum labels remain in the original product. -/
theorem group_assignment (P : Rep G n) (S : M → Support n)
    (F : Ω → M → Config G n → ℝ) (u : Ω) (rows : Finset ℕ) (π : M → ↥rows) (U : Config G n) :
    let map := fun k => (π k).val
    (∏ j, flagShare P (S j) (map j) U * F u j U) * (∏ i ∈ rows, P.activities.K i U) =
      (∏ i ∈ touched map, ownerBlock P (fibre map i) S F u i U) *
        ∏ i ∈ rows \ touched map, P.activities.K i U := by
  let map := fun k => (π k).val
  let letters := fun j => flagShare P (S j) (map j) U * F u j U
  have sub : touched map ⊆ rows := by
    intro a ha
    obtain ⟨k,_,rfl⟩ := mem_image.mp ha
    exact (π k).property
  have group := prod_fiberwise_of_maps_to (s:=univ) (t:=touched map) (g:=map)
    (fun j hj => mem_image_of_mem map hj) letters
  change (∏ j, letters j) * _ = (∏ i ∈ touched map, _) * _
  have localize (i) : ownerBlock P (fibre map i) S F u i U =
      P.activities.K i U * ∏ j ∈ fibre map i, letters j := by
    unfold ownerBlock
    congr 1
    apply prod_congr rfl
    intro j hj
    exact congr_arg (fun i => flagShare P (S j) i U * F u j U) ((mem_filter.mp hj).2.symm)
  have rebuilt : (∏ i ∈ touched map, ownerBlock P (fibre map i) S F u i U) =
      (∏ i ∈ touched map, P.activities.K i U) * ∏ j,letters j := by
    rw [prod_congr rfl (fun i _ => localize i),prod_mul_distrib]
    exact congr_arg ((∏ i ∈ touched map, P.activities.K i U) * ·) group
  rw [rebuilt,← prod_sdiff (f:=fun i => P.activities.K i U) sub]
  ring

/-- Exact mixed failed-source occurrence in the same blocks used by the
absolute budgets, allowing all repeated and coincident sources. -/
theorem grouped_occurrence (P : Rep G n) (S : M → Support n)
    (F : Ω → M → Config G n → ℝ) (u : Ω) (rows : Finset ℕ) (U : Config G n) :
    P.activities.gasOccurrence P.p rows U * failedProduct P S F u U =
      if P.activities.admissible P.p U rows then
        ∑ π : M → ↥rows, (∏ i ∈ touched (fun j => (π j).val),
          ownerBlock P (fibre (fun j => (π j).val) i) S F u i U) *
            ∏ i ∈ rows \ touched (fun j => (π j).val), P.activities.K i U else 0 := by
  rw [failedProduct,mixed_failed_occurrence]
  split
  · exact sum_congr rfl (fun π _ => group_assignment P S F u rows π U)
  · rfl

variable {V : Type} [DecidableEq V] {B : Census V} {ξ : V → ℕ} {qd b : ℕ}
    {o : V → Site n} {P : Rep G n}

omit [Fintype M] in
/-- At every scale each short source halo costs at most one native tile and
contains at most the physical hit width in sites. -/
theorem local_block_invoice (P : Rep G n) (J : Finset M) (pos : M → Site n)
    (C : M → ℝ) (hC : ∀ j, 0 ≤ C j) (anchor : M) {κ : ℝ} (hκ : 0 ≤ κ) :
    blockInvoice P J (fun j => Tale.court P.p.B (pos j)) C anchor κ ≤
      (∏ j ∈ J, (Real.exp P.p.supportExponent * C j)) * (Push.Local.hitWidth P.p * κ) := by
  let S := fun j => Tale.court P.p.B (pos j)
  have oneTile (j) : coverNumber P.p.B (S j) ≤ 1 := Vase.halo_cost _
  have cardBound : ((S anchor).card:ℝ) ≤ Push.Local.hitWidth P.p := by
    unfold Push.Local.hitWidth
    exact_mod_cast (Corona.pays (S anchor) P.p.B).trans
      (by simpa only [one_mul] using Nat.mul_le_mul_right ((P.p.B+P.p.B+1)^4) (oneTile anchor))
  apply mul_le_mul _ (mul_le_mul_of_nonneg_right cardBound hκ)
    (mul_nonneg (Nat.cast_nonneg _) hκ) (prod_nonneg (fun j _ => mul_nonneg (Real.exp_nonneg _) (hC j)))
  exact prod_le_prod (fun j _ => mul_nonneg (Real.exp_nonneg _) (hC j))
    (fun j _ => mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_of_le_one_right P.p.exponent_pos.le (by exact_mod_cast oneTile j))) (hC j))

end YM.Integration.FVA1Physical.Marked

namespace YM.Qlocal.Actual.Season.Exchequer
open Lattice RG Wilson Pressure Tree Marker Extra.Trajectories RG3.Script.Picnic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song
open Push Push.Uniform Metric Height Roof Input Org Supply Pane Slide Further.PhysicalPeriodLimitF933
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost AllOrder Transit Transit.WheelP
open Floe Floe.Step.PlanV Pace Ink Ink.Money Quipu Quipu.Sonnet Tern
open Program Program.Certificate Calendars Moonset Rooms Studio Squall Parabola
open Emissions Integration LocalComparison FVA1Physical.Marked Finset Push.AbsoluteSums
open scoped BigOperators Classical

/-- Uniform native bound for the true mixed forced component, partitioned by
its actual hosts. The sole geometric factor is the hit-width per occupied
host. There is no dependence on source positions, period or separation. -/
theorem purchased_host_blocks {V Ω M I : Type} [Fintype V] [DecidableEq V] [Fintype I]
    {G : Gauge} {X : Run G} {R : Roots (G := G) X.metals.p.profile X.metals.K X.metals.p.kernel}
    {B : Census V} {ξ : V → ℕ} {b i k qd N z j p m : ℕ} {δ : ℝ}
    {path : ℕ → Floe.Layout G} {Γ : ℕ → Pace.Coin}
    {x : (t : ℕ) → RG.Rep G (X.alloy.B.a.S.side t p)}
    {o : (t : ℕ) → V → Site (X.family.side t p)} {S : (t : ℕ) → V → Support (X.family.side t p)}
    {price : Ray B} {W : Rooms.Wallet Ω (o m) (x m) B ξ qd b}
    (track : Metre X.alloy X.kit X.T path Γ z N p k x) (lo : z ≤ m) (hi : m ≤ N)
    (shell : Studio.Shell X R ξ b i price o S δ m W (x := x) (j := j) (k := k))
    (modes : M → Senses B) (blocks : I → Finset M) (anchor : I → M)
    (occ : ∀ i, anchor i ∈ blocks i) :
    let κ := Hull.divisor X.alloy.B.a m * Hull.divisor X.alloy.B.a m
    let pos := fun s => o m (Sonnet.root (modes s))
    let src := fun s => Tale.court (x m).p.B (pos s)
    let g := Coat.gStep (X.T.history N p m).beta
    let ray := Studio.tagScale B X m j price
    let bill := fun s => (ray (modes s).val)⁻¹ * valueInvoice G ξ qd b (modes s) g
    let F := fun u s => shortValue W (modes s) (Stores.till (X.alloy.B.a.clock.hatBeta m)) g u
    ∃ bound : I → ℕ → ℝ, (∀ k i, 0 ≤ bound k i) ∧
      (∀ u (π : I ↪ ℕ) U, |∏ k, ownerBlock (x m) (blocks k) src F u (π k) U| ≤ ∏ k, bound k (π k)) ∧
      SumBudget (fun π : I ↪ ℕ => ∏ k, (x m).p.mass (enlarged (x m) (blocks k) src (π k)) (bound k (π k)))
        (∏ k, (∏ s ∈ blocks k, Real.exp (x m).p.supportExponent * bill s) * (Push.Local.hitWidth (x m).p * κ)) := by
  intro κ pos src g ray bill F
  have hv := (Hull.luminous X.alloy.B.a m)
  have hk : (x m).activities.KBound (x m).p κ := by
    unfold κ
    rw [← hv.2.2]
    exact (track.1.walk m lo hi).truep.valid.labels.boundK
  have charge (s) : 0 ≤ bill s :=
    mul_nonneg (inv_nonneg.mpr (shell.rental.pos _).le)
      (sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (Vase.ticketC_pos ..))
  have bounded (u s U) : |F u s U| ≤ bill s := by
    let A := Stanza.son (W.prediction u) b
    have weight : |W.weight u (modes s)| ≤ (ray (modes s).val)⁻¹ :=
      ((le_inv_mul_iff₀ (shell.rental.pos _)).mpr (shell.starts u _)).trans_eq (mul_one _)
    unfold F shortValue
    rw [abs_mul]
    exact mul_le_mul weight (wake_bound A (modes s) _ (shell.optics u) (Prior.yard_p ..) g U) (abs_nonneg _)
      (inv_nonneg.mpr (shell.rental.pos _).le)
  obtain ⟨bound,nonneg,values,pay⟩ := assigned_blocks_budget (x m) blocks anchor occ src F bill charge bounded hk
  refine ⟨bound,nonneg,values,budget_loosen pay ?_⟩
  have posκ : 0 ≤ κ := mul_nonneg hv.1.le hv.1.le
  apply prod_le_prod _ (fun k _ => local_block_invoice (x m) _ pos bill charge (anchor k) posκ)
  intro k _
  unfold blockInvoice
  exact mul_nonneg (prod_nonneg fun t _ => mul_nonneg (Real.exp_nonneg _) (charge t))
    (mul_nonneg (Nat.cast_nonneg _) posκ)

end YM.Qlocal.Actual.Season.Exchequer
