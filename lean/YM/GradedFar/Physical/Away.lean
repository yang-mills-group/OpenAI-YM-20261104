import YM.GradedFar.Physical.Homet

/-!
# r-scaled true homogeneous kernels on compact profiles in the price book
(One portion in (G.1), unselected, for all-power comparison)
Here just the compacta. Rolling prices need **more**.
-/
namespace YM.FVA2.GradedFar.Physical
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open Moving Growth Pose Books
open Scale Dframe
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m d h : ℕ} {I:Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple}
    {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book} (T : Filter I)
    (U : Spec.Final R f P) (J K : FramesH P)
    (B : (d:ℕ) → ℝ→FieldEnd G d) (Y : (d:ℕ)→ℝ→ Prediction G d) (θ : ℝ→ℝ)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "F"=> familyPoint U J
local notation "F'"=> familyPoint U K
local notation "α"=>Scale.Measure.adjust N.scheme N.criterion
variable (W : Bookshelf N U J K B Y θ) (Q : Earned N M U J K θ)
  (hq : ∀ (d:ℕ), ∀ᶠ r:ℝ in 𝓝[>] (0:ℝ), ∀ v:Sec G d, K r d v=J r d (B d r v))
variable {L : Set (Points n)} (hL : IsCompact L) (hLK : L⊆conf n)
  (r : I→ℝ) (x:I→Points n) (hx : ∀ᶠ i in T, x i∈L) (hr : Tendsto r T τ)

/-- Ordinary predictor *after* adjustment. Uniform all x; every horizon.
Use `GradedFar.Yx_configuration` to read `Boundary` comparisons incl.
with Far scaled at price on K operators already proved; this lemma alone applies
only on compact horizons. -/
abbrev boundary (N : WilsonPrescription G) (u:Tags G d n) (x:Points n) := shop (Jury.fxt (book N d) x) u
include H W Q hq hL hLK hr hx

theorem sun (p : ℕ) (v : Tags G d n) : Pays T (fun i=> familyPoint U K d (r i) n (x i) v)
    (fun i=> tells (boundary N v (x i))) (g∘r) p (fun i=>(θ (r i):ℂ)) := by
  have hz l: ∀ x:Points l, Jury.fxt (book N d) x=Dframe.status (α d) (Jury.fxt (Pose.Bbook N d) x) := Jury.fxt_m _ _
  have ht:=measuring T N M r hr H θ Q.clock
  have hi := titles T (g∘r) _ ((shrink simple).comp hr) ht (fun _=>α d)
    (fun i=> Jury.fxt (Pose.Bbook N d) (x i)) (fun i=>B d (r i)) v
    (primary T N M r hr H θ (Z:=next J d) (W.layers d)) («F»:=fun i=>F d (r i) n (x i))
    (fun a=> born T N M r hr H θ x hL hLK hx (Q.pre_meter d) a) (p:=p)
  unfold boundary; simp_rw [hz n]
  refine ⟨hi.1,hi.2.congr' ?_ (EventuallyEq.refl ..)⟩
  filter_upwards [hr.eventually (hq d)] with i hi
  apply congrArg (·- (_:ℂ)); apply congrArg (P.classMoment (OPE.spectator U none) (fun _:Fin n=>d) (r i • x i))
  funext j; exact (hi _).symm
omit hr hx in
lemma pointPrice (p : ℕ) (v : Tags G d n) : Pose.Terms τ (fun r=>g r^(p+1)) (fun r (x:↥L)=> familyPoint U K d r n x.val v - crop p (θ r) (boundary N v x.val)) := by
  apply (sun N M H (comap (Prod.fst : ℝ × ↥L→ℝ) τ) U J K B Y θ W Q hq hL hLK Prod.fst (fun i=>i.2.val) (Eventually.of_forall (fun i=>i.2.property)) tendsto_comap p v).2.congr_left
  intro i
  exact congr_arg (fun z : ℂ => familyPoint U K d i.1 n i.2.val v - z)
    (crop_by (boundary N v i.2.val) p (θ i.1)).symm

end
end YM.FVA2.GradedFar.Physical
