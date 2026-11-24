import YM.Integration.FVA1Physical.Sources.Round2.SignedOuter
import YM.Integration.FVA1Physical.Sources.Round2.ThermalFlags
import YM.Integration.FVA1Physical.Sources.Round2.TwoThermalSeasons

/-! Two adjacent actual blocking posteriors on one physical run. One local
hotel suffices; all distant failed plaquettes remain allowed under the true
measure. The independent mixed field polynomial is tested in the same hotel. -/
set_option autoImplicit false
set_option maxHeartbeats 2300000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior Source Labels Extra.Histories
open MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk MSbar.Lis MSbar.Mosaic
open Comparison.RG02 MSbar.Midpoint MSbar.Whisk MSbar.Rolling MSbar.Bakery MSbar.Bakery.Film MSbar.Cacao Push.Uniform
open Push Push.AbsoluteSums ConnectedActivityE6 Pressure Comparison.RG02.Order RGComparison.Core16 RGComparison.Core16.Spool
open YM.Integration.FVA1Physical.Wilson Progress.DirectedRecipe Next.SectorChange PhysicalNext.Repeat.Legato
open PhysicalNext PhysicalNext.Repeat
open YM.Integration.FVA1Physical.Marked Next.Foundations Push.GridApprox.Attach
open RG.Supply Input Org ThroughLaunch Roof Push.PriceCompiler UVNext.CouplingReset Graces Roost
open LocalLTE LocalLTE.Vinca LocalLTE.Concourse MergeProof Planned.GuardedAtom Planned.GuardedAtom.Guard
open Push.Local GapsR2RG GapsR2RG.Anchor
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι] {d:ℕ}

def measuredBirth (R:PhysicalNext.Repeat.Legato.Run G) (a:ι → CoverLabel G d) (N n m:ℕ)
    (anchor:Site (R.family.side (m+1) n)) (o:ι→Site (R.family.side (m+1) n)) (part:Bool) (rad:ℕ) : ℝ :=
  let H:=R.family.path
  let v:=fun i=>o i-anchor
  let P:=(H.rep N n (m+1)).p
  Doors.rate (H.S.block m)*birthCost P (lampSupport a v) (H.levels.clock.forcedAllowance (m+1))
    (localFieldTariff P a (R.alloy.B.a.params (m+1)).columns rad+‖(look part (tally (freshLamps a) v 1):ℂ)‖)
    (2*stencilBound (freshLamps a))

private theorem admits {c f : Side} {S : StepData c f} {R : Rep G f} {P : Rep G c}
    {Q : Voice G} {H H' : Stage} {x val : ℝ} (h : Season Q H H' x R P S val) :
    ∀ V, Admitted V R S H'.width H'.paths (ability (tip G S.patch.L x)) (lbt (tip G S.patch.L x)) 1 :=
  fun V=>⟨h.case_.lawful,fun U=>(h.shine U).le,push_strict S R.beta h.bends.1 h.shine
    ((R.envelope h.case_.lawful).integrable _) V,S.isKernel h.bends.1 _⟩

private theorem collar_fits {h:ℕ} (large:4 ≤ h) : h*leg h+8 ≤ h^4 := by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le large
  simp only [leg]
  nlinarith only [Nat.zero_le (k^4),Nat.zero_le (k^3),Nat.zero_le (k^2),Nat.zero_le k]

theorem signed_two_seasons (a:ι → CoverLabel G d) (V : Voice G) (cle : Clear G V) (χ : ChartRatio G)
    (hχ : LocalRatio χ) (simple : G.Simple) (H H' H'' : Stage) (P₀ P₁ : Patch) (K₀ K₁ : KernelChoices)
    (h₀ : P₀.Branches K₀ G) (h₁ : P₁.Branches K₁ G) (p s L : ℕ) (part : Bool) {D η : ℝ}
    (hD : 0 ≤ D) (hη : 0 < η) (hp : η < (p:ℝ)+1) (exp : ℝ) : ∃ pal : Palisade,
    ∀ᶠ x : ℝ in atTop, ∀ (R:PhysicalNext.Repeat.Legato.Run G) {N n j k : ℕ} (_depth:j+1<N)
      (_start:R.t 0 ≤ j+1) (_ready:∀ i,R.t (a i).1.val ≤ j+2) (T : Scene R.family.path.levels n k)
      (F : Forest (R.family.path.levels.clock.op j n).ratio) (v : (R.family.path.levels.clock.op j n).Choices)
      (F' : Forest (R.family.path.levels.clock.op (j+1) n).ratio) (v' : (R.family.path.levels.clock.op (j+1) n).Choices),
      let B:=sceneIssue (N:=N) (j:=j) (RunFormalChain.fromRun R) T F v
      let A:=sceneIssue (N:=N) (j:=j+1) (RunFormalChain.fromRun R) T F' v'
      let y:=tip G P₀.L x
      let z:=tip G P₁.L y
      B.S.patch=P₀ → B.S.kernel=K₀ → Season V H H' x B.pre B.post B.S (courage G P₀.L x) →
      A.S.patch=P₁ → A.S.kernel=K₁ → Season V H' H'' y A.pre A.post A.S (courage G P₁.L y) →
      Kind A.T → Expanse A.T 1 (p+2) → Alto.Wedge A.T Alto.Dean (hatW z) (Alto.cWidth z) s (p+2) →
      Premier (main A.f A.pre.clip A.pre.path) → Critical A.F A.pre.clip A.pre.path A.ρ →
      (mold A.pre A.F A.v).PosDef →
      ∀ (Z : Positions (Primary B.c G)) (anchor : Site A.f) (o : ι → Site A.f) (rad:ℕ),
      ‖Z‖ ≤ D*room y → (∀ i : Slice (freshLamps a), separation anchor (legs (freshLamps a) o i).1 ≤ L*closeN z) →
      (∀ i,separation (o i-anchor) 0 ≤ rad) →
      (∀ X : Positions (Primary A.c G), ‖A.fClock • X‖ ≤ (2*fluctuationFee pal V D)*room z →
        FieldPort A χ V (p+2) L (freshLamps a) part z (z^pawn (p+2)) anchor X) →
      let b:=A.S.ratio.parent anchor
      let O:=represent (tint G (Body 1 B.c) Z)
      let μ:=vest (priced B.F B.v B.pre.clip B.pre.path) Z
      let live:=hotel B.F (boxX y b) (boxY y b) V O μ (pillow y) (room y)
      let copy:=chambers B.F (boxY y b) V O μ
      let E:=expect B.S B.pre O
      let M:=measuredBirth R a N n (j+1) anchor o part rad
      |E (boundaryStencil (freshLamps a) A o part)-E (live.indicator (independentStencil (freshLamps a) A χ p o part ∘ copy))| ≤
        courage G P₀.L x*(kappa R.family.path (j+1)*M)+(stencilBound (freshLamps a)+M)*y^exp+
          2*Real.exp (-B.pre.p.supportExponent*(radiusB y))*M+A.fClock^((p:ℝ)+1-η) := by
  obtain ⟨pal,purchase⟩:=purchased_fluctuation_chance V cle simple H H' P₀ K₀ h₀ hD exp
  have fee : 0 ≤ fluctuationFee pal V D := by
    unfold fluctuationFee ceilingP
    have h:=zero_le_one.trans cle.cost; have t:0 ≤ shade G:=(shade_pos G).le; positivity
  let Bnd:=2*fluctuationFee pal V D
  have bnd : 0 ≤ Bnd := mul_nonneg zero_le_two fee
  let J:=freshLamps a
  have applyInner:=fluctuation_field_season J V cle χ hχ simple H' H'' P₁ K₁ h₁ p s L part bnd hη hp
  have growth:=Work.E09.betaF_growth G P₀.L
  refine ⟨pal,?_⟩
  filter_upwards [purchase,growth.eventually applyInner,growth.eventually (thermal_step simple P₁),
    growth.eventually (thermal_flags pal V cle (fluctuationFee pal V D)), tale P₀ V cle,
    growth.eventually (Work.E08.eventual_radiusB 4)] with x outerOffer innerOffer compare clearCopy quiet size
  intro R N n j k depth start ready T F v F' v' B A y z p₀ k₀ out p₁ k₁ inn kind plane wedge prem crit pd Z anchor o rad hZ loc foot ports b O μ live copy E M
  obtain ⟨_,money,window,_⟩:=outerOffer B p₀ k₀ out Z b hZ
  have hb : 0 < B.fClock := inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos (zero_lt_one.trans out.case_.enough)).trans_le out.case_.beta))
  have ha : 0 < A.fClock := inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos (zero_lt_one.trans inn.case_.enough)).trans_le inn.case_.beta))
  have price := innerOffer A p₁ k₁ inn kind plane wedge anchor
  have fit:radiusB y * leg B.pre.p.B+8 ≤ spotN y:=by
    rw [out.case_.size,p₀]
    exact collar_fits size
  have near:halo (radiusB y*leg B.pre.p.B+8) {b} ⊆ boxY y b :=
    (Corona.halo_mono fit subset_rfl).trans money.first.extendsX
  obtain ⟨Q,form,dens,paid⟩:=current_run_field R simple depth start a ready anchor o part rad foot
  have exactness (W:Config G A.c) : (boundaryStencil J A o part W:ℂ)=
    Q.exponentialEntry b (localSection G 0) B.pre W + forcedShare Q B.pre W :=
    current_all_boundaries R.family.path R.makes.wilson depth b (fun U=>look part (tally J o U)) Q dens W
  have shape := signed_outer Q b (localSection G 0) form (show Q.remBound b B.pre (kappa R.family.path (j+1)) M from paid)
    O (admits out O) out.shine out.storm (voids money.first.folds (quiet.trans_eq out.hull.threshold.symm))
    (Real.exp_pos _).le (boundaryStencil J A o part) (independentStencil J A χ p o part)
    (boundaryStencil_cont J A o part inn.bends.1 (admits inn)).measurable (independentStencil_meas J A χ p o part)
    (fun W=>boundaryStencil_bounded J A o part W (admits inn W)) exactness live
    (garden_main F (boxX y b) (boxY y b) V O μ cle money.first.extendsX).from_here money.sails copy
    (informed F (boxX y b) (boxY y b) V O μ cle money.first.extendsX).1 (fun U=>F.foldAt U) (radiusB y)
    (fun U hit=>by
      have small:=clearCopy hb (copy U) (window U hit)
      have healthy:flags B.pre.p.threshold (copy U)=∅:=by simpa only [out.case_.threshold,p₀] using small
      have agree:=cognizant F (boxX y b) (boxY y b) V O μ cle money.first.extendsX hit money.first.goes
      exact ⟨healthy,agrees_mono agree near,thermalStencil_price J A χ p L o part anchor z η Bnd loc inn.bends.1
        prem crit pd ha (fun X hx => price X hx (ports X hx)) _ (regularInputs_thermal (copy U) hb ha fee compare (window U hit))⟩)
    (Real.rpow_nonneg ha.le _)
  exact shape

end YM.Integration.FVA1Physical.Round2.Curvature
