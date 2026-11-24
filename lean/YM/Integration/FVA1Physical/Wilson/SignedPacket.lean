import YM.Integration.FVA1Physical.Wilson.PacketTail
import YM.Integration.FVA1Physical.Sources.Round2.SignedSeasons
import YM.Integration.FVA1Physical.Sources.Round2.SignedCost

/-! A signed, genuinely inherited physical source and a diffuse Wilson bank with the same anchored seed can be compared under the next full physical Haar kernel from their collar values alone. All distant failed polymers remain integrated, and their cost has no period factor. -/
set_option autoImplicit false
set_option maxHeartbeats 2300000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
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
variable {G : Gauge}
open YM.Integration.FVA1Physical.Round2.Curvature

theorem signed_polynomial_cost (L:Side) {τ:ℝ} (hτ:0<τ) (u e:ℝ) :
    ∀ᶠ x:ℝ in atTop,∀ (B M κ:ℝ),0 ≤ M → M ≤ (tip G L x)^e → B ≤ (tip G L x)^e → κ ≤ 1 →
      let y:=tip G L x
      courage G L x*(κ*M)+(B+M)*y^(u-e-1)+2*Real.exp (-τ*radiusB y)*M ≤ 3*y^u := by
  filter_upwards [signed_cost_decay (G:=G) L hτ 1 1 (u-e),(Work.E09.betaF_growth G L).eventually_gt_atTop 0]
    with x prices pos B M κ M0 cap₁ cap₂ κ₁ y
  let t:=y^e
  have tpos:0<t:=Real.rpow_pos_of_pos pos _
  have h:=prices (M/t) κ (div_nonneg M0 tpos.le) ((div_le_one tpos).mpr cap₁) κ₁
  dsimp only at h
  have pay:=mul_le_mul_of_nonneg_right h tpos.le
  have a:M/t*t=M:=div_mul_cancel₀ M tpos.ne'
  have b:y^(u-e)*t=y^u:=by dsimp only [t];rw [←Real.rpow_add pos];congr 1;ring
  have chance:=Real.rpow_nonneg pos.le (u-e-1)
  calc
    _ ≤ courage G L x*(κ*M)+(t+M)*y^(u-e-1)+2*Real.exp (-τ*radiusB y)*M := by gcongr
    _ = (courage G L x*(κ*(M/t))+(1+M/t)*y^(u-e-1)+2*Real.exp (-τ*radiusB y)*(M/t))*t := by
      conv_lhs => rw [←a]
      ring
    _ ≤ 3*y^(u-e)*t := pay
    _ = 3*y^u := by rw [mul_assoc,b]

theorem signed_packet_transfer (V:Voice G) (cle:Clear G V) (simple:G.Simple) (H H':Stage)
    (P:Patch) (K:KernelChoices) (br:P.Branches K G) (p m s:ℕ) {D:ℝ} (hD:0 ≤ D) (u e:ℝ) :
    ∃ pal:Palisade,∀ᶠ x:ℝ in atTop,∀ (A:Issue G),A.S.patch=P → A.S.kernel=K →
      Season V H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x;let g:=A.fClock
      ∀ (Z:Positions (Primary A.c G)) (b:Site A.f), ‖g•Z‖ ≤ D*room y →
      ∀ (Q:Coefficient ((frames G).level 0) A.f) (φ:Config G A.f → ℝ) (T:Nesting G A.f) (B M κ ε:ℝ),
        Q.Format b (hol G) A.pre → Q.remBound b A.pre κ M →
        (∀ W,(φ W:ℂ)=Q.exponentialEntry b (localSection G 0) A.pre W+forcedShare Q A.pre W) →
        Measurable φ → (∀ W,|φ W| ≤ B) → B ≤ y^e → M ≤ y^e → κ ≤ 1 → 0 ≤ ε →
        BankPaid b y s p m 1 T →
        (∀ W∈regularInputs g (fluctuationFee pal V D*room y/g),
          |φ W-clockReading p g T (chartLog g W)| ≤ ε) →
        |expect A.S A.pre (postcard G A.c g Z) φ-expect A.S A.pre (postcard G A.c g Z)
          (fun W=>clockReading p g T (chartLog g (canoe (S:=A.S) A.F W)))| ≤ ε+5*y^u := by
  obtain ⟨pal,localBuy⟩:=purchased_fluctuation_chance V cle simple H H' P K br hD (u-e-1)
  have rise:=Work.E09.betaF_growth G P.L
  refine ⟨pal,?_⟩
  filter_upwards [localBuy,signed_polynomial_cost (G:=G) P.L H'.price_pos u e,packet_tail_season V cle simple H H' P K br p m s hD u,
      rise.eventually (thermal_flags pal V cle (fluctuationFee pal V D)),rise.eventually (Work.E08.eventual_radiusB 4),tale P V cle]
    with x buy price tail flags' size fire
  intro A patch kernel season y g Z b width Q φ T B M κ ε form paid exactness mφ bound Bcap Mcap κcap ε0 bank close
  let O:=postcard G A.c g Z;let μ:=vest (priced A.F A.v A.pre.clip A.pre.path) (g•Z)
  let X:=boxX y b;let Y:=boxY y b;let copy:=chambers A.F Y V O μ;let live:=hotel A.F X Y V O μ (pillow y) (room y)
  let reading:=fun W=>clockReading p g T (chartLog g W)
  obtain ⟨_,money,window,_⟩:=buy A patch kernel season (g•Z) b width
  have g0:0 < g:=inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos (zero_lt_one.trans season.case_.enough)).trans_le season.case_.beta))
  have fit:radiusB y*leg A.pre.p.B+8 ≤ spotN y:=by
    rw [season.case_.size,patch]
    obtain ⟨i,hi⟩:=Nat.exists_eq_add_of_le size
    unfold spotN
    rw [hi]
    simp only [leg]
    nlinarith only [Nat.zero_le (i^4),Nat.zero_le (i^3),Nat.zero_le (i^2),Nat.zero_le i]
  have near:halo (radiusB y*leg A.pre.p.B+8) {b} ⊆ Y:=(Corona.halo_mono fit subset_rfl).trans money.first.extendsX
  have adm:Admitted O A.pre A.S H'.width H'.paths (ability (tip G A.S.patch.L x)) (lbt (tip G A.S.patch.L x)) 1 :=
    ⟨season.case_.lawful,fun W=>(season.shine W).le,Progress.DirectedRecipe.push_strict A.S A.pre.beta season.bends.1 season.shine
    ((A.pre.envelope season.case_.lawful).integrable _) O,A.S.isKernel season.bends.1 _⟩
  have mT:Measurable reading:=(clockReading_continuous ..).measurable.comp (chartLog_meas g)
  have outer:=signed_outer Q b (localSection G 0) form paid O adm season.shine season.storm
    (voids money.first.folds (fire.trans_eq season.hull.threshold.symm)) (Real.exp_pos _).le φ reading mφ mT bound exactness live
    (garden_main A.F _ _ V O μ cle money.first.extendsX).from_here money.sails copy
    (informed A.F X Y V O μ cle money.first.extendsX).1 (fun W=>A.F.foldAt W) (radiusB y) (fun W hit=>by
      have z:=flags' g0 (copy W) (window W hit)
      have healthy:flags A.pre.p.threshold (copy W)=∅:=by simpa only [season.case_.threshold,patch] using z
      exact ⟨healthy,agrees_mono (cognizant A.F X Y V O μ cle money.first.extendsX hit money.first.goes) near,
        close _ (window W hit)⟩) ε0
  have M0:0 ≤ M:=by obtain ⟨v,w,hv,hw,cost,_⟩:=paid;exact (add_nonneg hv hw).trans cost
  have scaled:=price B M κ M0 Mcap Bcap κcap
  rw [←season.case_.support] at scaled
  have seam:=tail A patch kernel season Z b width 1 le_rfl T bank
  exact ((abs_sub_le _ (expect A.S A.pre O (live.indicator (reading ∘ copy))) _).trans (add_le_add outer seam)).trans
    (by linarith only [scaled])

end YM.Integration.FVA1Physical.Wilson
