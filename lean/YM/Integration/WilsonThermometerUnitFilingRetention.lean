import YM.Integration.WilsonThermometerUnitFilingDeposit
import YM.Integration.WilsonMacroscopicRichPortfolioCapture
import YM.Integration.WilsonMacroscopicRichEnrolledFiling

/-! The complete compact marked source is grouped on its true physical
vacuum and filed at one older unit station. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingRetention
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Source Labels Cells Extraction Spec Table
open OPE Marker Next.Extract PhysicalNext.Repeat.Legato XSpace MergeProof RG12 RG16 RG16.Literal
open Extra.Histories Relay Next.Rank Primitives.GCC.Anchor Push.GridApprox
open Climb Trace.Pilot Next.UVStress RG17 PhysMS MergeProof.Accent MergeProof.East
open FVA1 OriginalForcedAddresses XSpace.Normalize XSpace.Rose Work.G08 Trace.Physical
open Trace.Physical.GermGraph Bid
open WilsonPositionThermometerCapStation WilsonThermometerCourseIntake WilsonThermometerUnitFilingCylinder
open WilsonThermometerUnitFilingFeed
open scoped BigOperators Topology Classical
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
local notation "J!" => Stock.census (Fin 3)

private theorem compressed {X V : Type*} [Fintype X] [AddCommMonoid V]
    (c : X → ℂ) (v : X → V) (zero : ∀ x, c x = 0 → v x = 0) :
    (∑x : {x // c x ≠ 0}, v x.val) = ∑x,v x := by
  rw [←Finset.sum_subtype (Finset.univ.filter fun x => c x ≠ 0)
    (fun x => by simp) v,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : c x = 0
  · simp [hx,zero x hx]
  · simp [hx]

private theorem continuous_face (z : UVIndex) (y : Sites R z) (s : (J!).Mode) :
    Continuous (placed R A z s.val y) := by
  apply continuous_finsetProd
  intro i _
  exact R.family.continuousO z.1 z.2 _ _ _

private theorem continuous_source (z : UVIndex) (y : Sites R z) (Q : Poly J!) :
    Continuous (WilsonThermometerUnitFilingCylinder.source R A z y Q) := by
  unfold WilsonThermometerUnitFilingCylinder.source
  rw [show (∑ s : (J!).Mode,wallet Q s • placed R A z s.val y)=_ from
    funext (fun U=>Finset.sum_apply U _ _)]
  exact continuous_finsetSum _ fun s _ => (continuous_face R A z y s).const_smul _

include simple in
/-- Each submitted coefficient is for the actual full, unnormalized older
marked polynomial at that child placement. The original merge files one
coefficient for the compact field, with each charge multiplied by the
absolute physical cell weight. -/
theorem original {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (units : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t)=(Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, ∀ (b u : ℕ) (top : b ≤ z.1) (_ : u ≤ b) (_ : R.family.ref 0 ≤ u)
      (r : ℝ) (φ : Test 3) (Q : Sites R z → Poly J!)
      (o : Sites R z → Positions (Fin 3) (R.family.side z.1 z.2)) (_ : ∀ y,(o y).origin=y)
      (rent : Sites R z → ℝ) (η : ℝ), 0 < η →
      let w := WilsonSeparatedOriginalThermometerCells.weight φ (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z)
      let Y := cylinder R A z r φ Q
      let Ψ := R.family.path.rep z.1 z.2 b
      let S := R.family.localSection 0
      let F := R.family.labels.level 0
      let gross := ∑ y, ‖w y‖*rent y
      let E := WilsonMacroscopicRichCaptureFilingBudget.capital R.family b gross η
      (∀ y, w y ≠ 0 → ∃ q : Coefficient (R.family.labels.level 0) (R.family.side b z.2),
        q.Format 0 R.family.params Ψ ∧ q.remBound 0 Ψ (safety R.family b) (rent y) ∧
        F.coeffSize q.x ≤ rent y ∧ ∀ U, q.density 0 S Ψ U =
            ∑ s : (J!).Mode,wallet (Q y) s * (incoming R A simple top (o y) U).part s) →
      (∃ q : Coefficient (R.family.labels.level 0) (R.family.side b z.2), q.Format 0 R.family.params Ψ ∧
        q.remBound 0 Ψ (safety R.family b) gross ∧ F.coeffSize q.x ≤ gross ∧
        credit R.family z.1 z.2 0 Y b top = q.density 0 S Ψ) ∧
      ∃ B : R.family.label 0, Next.UVStress.quota R.family 0 b z.1 z.2 B ≤ 2*E ∧
        ∀ j, u ≤ j → ∀ jb : j ≤ b, Opened R.family 0 j z.2 →
          Booked R.family z.1 z.2 0 Y j (jb.trans top) ∧
          ‖report R Y j - B 0‖ ≤ E/gainChart R.family.path b j := by
  filter_upwards [WilsonThermometerUnitFilingReturn.density R A simple checked units] with z row
  intro b u top ub start r φ Q o located rent η pos w Y Ψ S F gross E submit
  let V := {y : Sites R z // w y ≠ 0}
  let g (y : Sites R z) := WilsonThermometerUnitFilingCylinder.source R A z y (Q y)
  choose q fmt rem sz valued using fun a : V => submit a.val a.property
  have read (a : V) : credit R.family z.1 z.2 0 (g a.val) b top = (q a).density 0 S Ψ := by
    funext U
    rw [valued]
    unfold g WilsonThermometerUnitFilingCylinder.source
    rw [IntrinsicProductLinearity.credit_sum R.family z.1 z.2 0 b top _ _ (continuous_face R A z a.val)]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro s _
    apply congrArg (_ * ·)
    simpa only [located] using (congrFun (row b top (o a.val) s) U).symm
  obtain ⟨qB,hB,bound,size,account⟩ := WilsonMacroscopicRichPortfolioCapture.merged R.family
    z.1 z.2 0 b R.makes (start.trans ub) top (fun a : V => w a.val) (fun a : V => g a.val)
    (fun a => continuous_source R A z a.val (Q a.val)) (fun a : V => rent a.val) q
    (fun a => ⟨fmt a,rem a,sz a,read a⟩)
  have htot : (∑a : V, ‖w a.val‖*rent a.val)=gross :=
    compressed w (fun y => ‖w y‖*rent y) (fun y hy => by simp [hy])
  have src : (∑a : V,w a.val • g a.val)=Y :=
    compressed w (fun y => w y • g y) (fun y hy => by simp [hy])
  rw [htot] at bound size
  rw [src] at account
  refine ⟨⟨qB,hB,bound,size,account⟩,?_⟩
  obtain ⟨B,hq,all⟩ := WilsonMacroscopicRichEnrolledFiling.original R.family z.1 b u z.2 0
    R.makes (R.again simple).1.scrim Y (continuous_cylinder R A z r φ Q) qB gross η pos
    start ub top hB bound size account
  refine ⟨B,hq,?_⟩
  intro j uj jb door
  obtain ⟨booked,price⟩ := all j uj jb door
  refine ⟨booked,?_⟩
  have alive := jb.trans top
  have freeze := terminal R simple (p:=z.2) (door.post.trans alive)
    ((R.family.factory 0 z.1 z.2).terminal.symm B)
  rw [LinearEquiv.apply_symm_apply] at freeze
  rw [scalar_cost R simple door alive,←freeze] at price
  simpa only [report,dif_pos (And.intro door alive),terminal R simple (door.post.trans alive),
    Pi.sub_apply] using price

end YM.Integration.WilsonThermometerUnitFilingRetention
