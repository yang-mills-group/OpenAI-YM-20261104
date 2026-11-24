import YM.Integration.WilsonOriginalPublicFiniteInversion
import YM.Integration.WilsonPositionProgramDeclaredForest

/-! On the chosen public inversion mesh, the original chronological catalogue
has one finite angular table on each physical period. The two finite regulators
are independent. A single signed variation pays the two errors on the same
submitted numerical coordinates, for every occupied angular degree. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRegulatorHearing
open Exterior Wilson Tree RegulatorIR.Binding RegulatorIR.FVAAlt2.Period.Field RegulatorIR.FVAAlt2.Pipeline
open WilsonOriginalPublicFiniteInversion
open WilsonPositionProgramSubmittedFaces WilsonPositionProgramSeriesRead WilsonPositionProgramInversionMaterial
open Set Filter Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
open Next.Foundations RegulatorIR.Calibration RegulatorIR.FVAAlt2.Kick WilsonPositionProgramSubmittedGeometry
open scoped Classical Topology ENNReal BigOperators
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} {simple : G.Simple} {a : Axis} {ε : ℝ}
variable (first : WilsonPositionProgramArithmetic.course simple a ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit) (slow : WilsonWindowReportingPace.Slow C.kit)
    (Z : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G) (p : ℕ) (color : G.ColorIndex)
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
include first paid slow in
theorem original {n : ℕ} (nonempty : 0 < n) (K : Set (Points n)) (compact : IsCompact K) : ∃ H : ℝ, 0 ≤ H ∧
    ∃ start : ℕ, ∀ (m j i : X → ℕ) (w : X → ℕ → ℕ)
      (blocks : ∀ x k, (C.family.S.block (m x+k)).val=D.ratio^(w x k))
      (_reach : ∀ x, WilsonPositionProgramCommonWindow.elapsed (w x) (j x)=D.reserve*(i x)*(i x)+i x),
      (∀ x, start ≤ m x) → ∀ (z : X → Fin n → Cover) (c : X → Four ℝ),
      (∀ x, c x ∈ (D.step (i x)).Box) → (∀ x, (D.step (i x)).rel (z x) (c x) ∈ K) →
      let S := WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
      let H' := WilsonPositionProgramInfraredCircuit.history C D m j w blocks
      ∀ F : Tent j, Notebook S Y G Z color (Rocket.native j) F p →
      ∃ T : See.Times (sheet F) p, ∀ (I : Type) [Fintype I] [LinearOrder I]
        (child : I → Fin n) (A : Type) [DecidableEq A] [Fintype A] (mask : Marker.Census A) (a : A),
      let sites := fun x => z x ∘ child
      ∃ V : (per:ℕ) → Sound.Figure.Activation (I:=I) C H' per mask,
        (∀per,Sound.Figure.Course C H' sites (sheet F) per a mask p T (V per)) ∧
        (∀per (d:I→ℕ)(ax:(i:I)→(C.family.labels.level (d i)).Index) (page : Page j)
          (U : fieldDir G (C.family.side (H'.vol page) per) 1) e, e≤p →
          See.prime H' mask a (sheet F) per p T (V per d ax) (x:=page) U e =
            Booth.Uniforms.cuff (See.observe Z (RunFormalChain.fromRun C) H' (Sound.Figure.prop C sites d ax)
              (sheet F) per page) (Kick.depthF Finset.univ d ax) e U ∧
          let recs:=H'.records S C.family.path per page
          See.visible mask recs.clip recs.path (T.cloth page) (V per d ax page) e U =
            Booth.Uniforms.cloth recs.clip recs.path (See.work Z (RunFormalChain.fromRun C) H'
              (sheet F) per page) e U) ∧
        ∀(d:I→ℕ)(trees:∀x,(D.step (i x)).p.Tree)(q:ℕ),q≤p→∀strength:ℕ,
        ∃cutoff:ℕ, ∀x,cutoff ≤ i x→1≤C.family.path.levels.clock.hatBeta (m x) →
          RG16.Lambda C.family.path.levels (m x)≤(i x:ℝ)*Real.log D.ratio →
        ∀δ:ℝ,0<δ→ ∀ᶠ per:ℕ in atTop,∀(P:ChartRatio G),LocalRatio P →
          ∀ζ:Axes C d → PowerSeries ℂ,
          ‖PowerSeries.coeff (q+ceiling C d) (XSpace.Bare.normalized (trees x) G
              (finite C (D.step (i x)).p d (sites x) (trees x) ζ)) -
            ∑u:Terms C d q, weight C d q ζ u *
              See.prime H' mask a (sheet F) per p T (V per d (axis C d u.1))
                (x:=(final j).choose x) 0 u.2.val.2‖ₑ ≤
            (ENNReal.ofReal ((D.step (i x)).spacing^strength)+ENNReal.ofReal δ)*
              ∑u:Terms C d q,‖weight C d q ζ u‖ₑ :=by
  obtain ⟨H,hH,start,grant⟩:=WilsonPositionProgramSharedInversionTariff.original (X:=X)
    C D first paid slow Z p color nonempty K compact
  refine ⟨H,hH,start,?_⟩
  intro m j i w blocks reach mature z c box support S H' F book
  have prices:=grant m j i w blocks reach mature z c box support F book
  obtain ⟨T,register⟩:=WilsonPositionProgramDeclaredForest.original C D m j w blocks Z color p F book
  refine ⟨T,?_⟩
  intro I _ _ child A _ _ mask a sites
  obtain ⟨V,course,same,_⟩:=register I sites A mask a
  refine ⟨V,course,same,?_⟩
  intro d trees q hq strength
  obtain ⟨cutoff,next⟩:=prices I child d trees q hq strength
  refine ⟨cutoff,?_⟩
  intro x above hot room δ pos
  filter_upwards [WilsonOriginalPublicFiniteInversion.original C D m j w blocks Z F sites d x q δ pos] with per close
  intro P valid ζ
  have actual(u:Terms C d q):See.prime H' mask a (sheet F) per p T (V per d (axis C d u.1))
      (x:=(final j).choose x) 0 u.2.val.2 =
      observed C D m j w blocks Z F sites d x q per u :=by
    have atGrade:=Finset.HasAntidiagonal.mem_antidiagonal.mp u.2.property
    exact (same per d _ _ _ _ (by omega)).1
  simp_rw [actual]
  let α := weight C d q ζ
  let middle := ∑u:Terms C d q,α u * terminal C D m j w blocks Z F sites d x q u
  let last := ∑u:Terms C d q,α u * observed C D m j w blocks Z F sites d x q per u
  let inv := PowerSeries.coeff (q+ceiling C d) (XSpace.Bare.normalized (trees x) G
    (finite C (D.step (i x)).p d (sites x) (trees x) ζ))
  have one:‖inv-middle‖ₑ ≤ ENNReal.ofReal ((D.step (i x)).spacing^strength) * ∑u,‖α u‖ₑ :=
    next x above hot room P valid ζ
  have two:‖middle-last‖ₑ ≤ ENNReal.ofReal δ * ∑u,‖α u‖ₑ :=by
    have bill:=close α
    change ‖last-middle‖≤_ at bill
    rw [norm_sub_rev] at bill
    simpa only [ofReal_norm,ENNReal.ofReal_mul pos.le,ENNReal.ofReal_sum_of_nonneg (fun u _=>norm_nonneg (α u))]
      using ENNReal.ofReal_le_ofReal bill
  change ‖inv-last‖ₑ ≤ _ * ∑u,‖α u‖ₑ
  rw [←sub_add_sub_cancel inv middle last,add_mul]
  exact (enorm_add_le ..).trans (add_le_add one two)

end YM.Integration.WilsonOriginalPublicRegulatorHearing
end
