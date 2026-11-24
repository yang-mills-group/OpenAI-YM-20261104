import YangMills.WilsonProof.NativeSupport.Commissioned259.Delete

/-!
# Proper subarrays and empty measurement. No frame discrepancy for unit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259
open Function Filter Set PowerSeries MeasureTheory Maxwell
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus XSpace.Rose
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe
variable {G : Gauge} {n m j k a h : ℕ}
    (N : WilsonPrescription G) {sim : G.Simple} (ν : ℝ)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "V" => Scale.Measure.outlook N.scheme N.criterion
local notation "B" => GroupS.gaugeN N.scheme N.criterion M ν

variable (f : Fin j ↪ Fin n) (g : Fin k ↪ Fin m)
def chooseSub : Fin (j+k) ↪ Fin (n+m) := finSumFinEquiv.symm.toEmbedding.trans
    ((Embedding.sumMap f g).trans finSumFinEquiv.toEmbedding)
@[simp] lemma chooseSub_left (i : Fin j) : chooseSub f g (Fin.castAdd k i) = Fin.castAdd m (f i) := by simp [chooseSub]
@[simp] lemma chooseSub_right (i : Fin k) : chooseSub f g (Fin.natAdd j i) = Fin.natAdd n (g i) := by simp [chooseSub]
lemma restrict_forest (x : Points n) (y : Points m) :
    restrictPt (chooseSub f g) (forest x y) = forest (restrictPt f x) (restrictPt g y) := by
  ext1 i; induction i using Fin.addCases <;> simp [restrictPt]

abbrev faceSlots {d : Fin n → ℕ} (u : Slots G d) : Slots G (d ∘ f) := fun i => u (f i)

variable {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : ∀ i, d i ≤ a) (he : ∀ i, e i ≤ a)

lemma append_face (u : Slots G d) (v : Slots G e) :
    Fin.append (liftSlots hd u) (liftSlots he v) ∘ (chooseSub f g) =
    Fin.append (liftSlots (d:=d∘f) (fun i => hd (f i)) (faceSlots f u))
      (liftSlots (d:=e∘g) (fun i => he (g i)) (faceSlots g v)) := by
  funext i; induction i using Fin.addCases <;> simp [liftSlots,faceSlots] <;> rfl

variable (x : Points n) (y : Points m) (hx : forest x y ∈ conf (n+m))
include H ν hx
lemma honor (u : Slots G d) (v : Slots G e) (hu : padLeaf f u) (hv : padLeaf g v) (q : ℕ) :
    bareRow V hd he x y q u v =
    bareRow V (fun i => hd (f i)) (fun i => he (g i)) (restrictPt f x) (restrictPt g y) q (faceSlots f u) (faceSlots g v) := by
  rw [bareRow_apply, bareRow_apply, kernel_on V hx, ←restrict_forest, kernel_on V (restrict_conf _ hx)]
  let vf := Fin.append (liftSlots hd u) (liftSlots he v)
  have h_v : padLeaf (d:=fun _=>a) (chooseSub f g) vf := by
    intro i ni
    induction i using Fin.addCases with
    | left i =>
      have hh : i∉range f := by
        rintro ⟨r,rfl⟩; exact ni ⟨_,chooseSub_left f g r⟩
      unfold vf; rw [Fin.append_left]; unfold liftSlots; rw [hu i hh]; rfl
    | right i =>
      have hh : i∉range g := by
        rintro ⟨r,rfl⟩; exact ni ⟨_,chooseSub_right f g r⟩
      unfold vf; rw [Fin.append_right]; unfold liftSlots; rw [hv i hh]; rfl
  exact (outlook_delete N (chooseSub f g) ν M H ⟨_,hx⟩ q a vf h_v).trans (congr_arg _ (append_face f g hd he u v))

theorem measurement_face (η : ℝ) (u : Slots G d) (v : Slots G e) (hu : padLeaf f u) (hv : padLeaf g v) :
    measurement V B hd he x y η u v = measurement V B (fun i => hd (f i)) (fun i => he (g i))
      (restrictPt f x) (restrictPt g y) η (faceSlots f u) (faceSlots g v) := by
  ext1 p
  simp_rw [measurement, coeff_mk, inserted_apply]
  exact tally_shrink g (fun i=>conversion B η (e i)) (fun k=>bareRow V hd he x y k u)
    _ v hv p (fun v hv q=> honor N ν M H f g hd he x y hx u v hu hv q)
    (fun i k=> conversion_unit ((H.dilation ν).check) η _ _)

omit hx

omit H ν in
lemma face_smul (T : ℝ) (x : Points n) : restrictPt f (T • x) = T • restrictPt f x := rfl

include hx
lemma center_unit (h_a : h ≤ a) (hy : y∈ Outside m) (η : ℝ) (v : Slots G e) :
    measurement V B hd he x y η (fun i=>leaf G (d i)) v =
      center V B he y h_a η (leaf G h) v := by
  let f : Fin 0 ↪ Fin n := Function.Embedding.ofIsEmpty
  let f' : Fin 0 ↪ Fin 1 := Function.Embedding.ofIsEmpty
  let g : Fin m ↪ Fin m := Embedding.refl _
  have hg : padLeaf g v := fun i h => False.elim (h ⟨i,rfl⟩)
  rw [measurement_face N ν M H f g hd he x y hx η _ v (fun _ _=>rfl) hg]
  unfold center
  rw [measurement_face N ν M H f' g _ _ _ y hy η _ v (fun _ _=>rfl) hg]
  ext1 p
  simp_rw [measurement, coeff_mk, inserted_apply, bareRow_apply]
  rw [Subsingleton.elim (restrictPt f x) (restrictPt f' 0)]
  congr! -- Near lifted from empty slots

omit hx

lemma measurement_nil (η : ℝ) (u v : Tags G a 0) :
    measurement V B (d:=fun (_:Fin 0) => a) (e:=fun (_:Fin 0) => a) (fun _=>le_rfl) (fun _=>le_rfl) 0 0 η u v = 1 := by
  have hh : forest (0:Points 0) (0:Points 0)∈ conf (0+0) := fun (i : Fin 0) => Fin.elim0 i
  ext1 k; rw [measured_layout V _ _ _ _ _ hh, vacant_tally, Finset.sum_singleton, Finsupp.single_eq_same]
  exact outlook_zero N M H _ _ _ _

include hx
lemma all_absent (η : ℝ) :
    measurement V B hd he x y η (fun i=>leaf G (d i)) (fun i=> leaf G (e i)) = 1 := by
  let f : Fin 0 ↪ Fin n := Function.Embedding.ofIsEmpty
  let g : Fin 0 ↪ Fin m := Function.Embedding.ofIsEmpty
  rw [measurement_face N ν M H f g hd he x y hx η _ _ (fun _ _=>rfl) (fun _ _=> rfl)]
  have hc : forest (restrictPt f x) (restrictPt g y)∈ conf (0+0) := fun (i : Fin 0) => Fin.elim0 i
  ext1 k; rw [measured_layout V _ _ _ _ _ hc, vacant_tally, Finset.sum_singleton, Finsupp.single_eq_same]; exact outlook_zero N M H _ _ _ _
end YM.FVA2.GradedFar259
