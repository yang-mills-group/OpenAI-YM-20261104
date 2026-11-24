import YM.GradedFar.Pose.Receipt

/-!
# Execute the full thermometer log on the proper faces
-/
namespace YM.FVA2.GradedFar.Pose
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d : ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "ν"=> Teller.logNu 1
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=> gYM G
variable {F : Plans G 6} (t : ℝ → ℝ) (ht : Tendsto (fun r=> t r / gYM G r) (𝓝[>] (0:ℝ)) (𝓝 1))
variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
open XSpace.Rose

section operate
variable {I : Type}
def Kept (G : Gauge) (x : ℝ→I→ℂ) (t : ℝ → ℝ) (Y : I→PowerSeries ℂ) (k q : ℕ) :=
    (∀ i ≤ q, Proper τ (fun (_:ℝ) (z:I)=>coeff i (Y z))) ∧
    Terms τ (fun r=>gYM G r^k) (fun r z=> x r z - crop q (t r) (Y z))
variable {x y : ℝ→I→ℂ}{X Y : I→PowerSeries ℂ} {q k : ℕ}
namespace Kept
lemma add (a : Kept G x t X k q) (b : Kept G y t Y k q) : Kept G (fun r z=> x r z+y r z) t (fun z=> X z+Y z) k q := by
  refine ⟨fun i hi=> ?_, (a.2.add b.2).eq (fun i j=> by rw [crop_add]; dsimp; ring)⟩
  simp only [map_add]; exact (a.1 i hi).add (b.1 i hi)
lemma sub (a : Kept G x t X k q) (b : Kept G y t Y k q) : Kept G (fun r z=> x r z-y r z) t (fun z=> X z-Y z) k q := by
  refine ⟨fun i hi=> ?_, (a.2.sub b.2).eq (fun i j=> by rw [crop_sub]; dsimp; ring)⟩
  simp only [map_sub]; exact (a.1 i hi).sub (b.1 i hi)
include H ht
lemma crop (a : Kept G x t X k q) : Proper τ (fun r z=> crop q (t r) (X z)) := by
  simp only [crop_eq]; exact Terms.sum _ fun i hi=> (proper_power N M t H i ht).left (a.1 i (Finset.mem_range_succ_iff.mp hi))
local notation "cropped"=> GradedFar.crop
lemma proper (a : Kept G x t X k q) : Proper τ x :=
  ((a.2.mono (fine N M H k)).add (crop N M t ht H a)).eq fun _ _=>sub_add_cancel ..
lemma times (a : Kept G x t X k q) (b : Kept G y t Y k q) (h : k ≤ q+1) : Kept G (fun r z=>x r z*y r z) t (fun z=> X z*Y z) k q := by
  constructor
  · intro i hi; simp_rw [coeff_mul]; exact Terms.sum _ fun j hj=> (a.1 _ (by have h:=Finset.HasAntidiagonal.mem_antidiagonal.mp hj; omega)).left
      (b.1 _ (by have h:=Finset.HasAntidiagonal.mem_antidiagonal.mp hj; omega))
  let A r z:= cropped q (t r) (X z); let B r z:= cropped q (t r) (Y z)
  let u (s : ℕ × ℕ) r z:= cross (t r) (X z) (Y z) s
  have pay s (hs : s∈pairsAbove q) : Terms τ (fun r=>g r^k) (u s) := by
    obtain ⟨⟨hx,hy⟩,ht'⟩:= (mem_pairsAbove _ _).1 hs
    exact Terms.left (terms_power N M t H _ _ (by exact h.trans ht') ht) ((a.1 _ hx).left (b.1 _ hy))
  have price := Terms.sum _ pay
  have he (r z) : x r z*(y r z-B r z)+(x r z-A r z)*B r z + ∑ i∈pairsAbove q,u i r z =
      x r z*y r z - cropped q (t r) (X z * Y z) := by
    unfold A B u; rw [mul_sub, sub_mul, crop_mul]; abel
  exact (((Terms.right (proper N M t ht H a) b.2).add (a.2.left (crop N M t ht H b))).add price).eq he
end Kept
end operate

def value (Y : Badge → ℂ) : ℂ := Y Finset.univ - (Y {0,1}*Y {2} + Y {0,2}*Y {1} + Y {1,2}*Y {0}) + 2*(Y {0}*Y {1}*Y {2})
abbrev watchRose (F : Plans G 6) (r : ℝ) (x : Points 3) := fun s=> F r 3 x (missing (tag G) s)
include H ht
lemma posed (q k : ℕ) (hq : k ≤ q+1)
    (acts : ∀ s:Badge, Terms τ (fun r=>g r^k)
      (fun r (x: ↥(tsupport (Rose.test N.criterion)))=> watchRose F r x.val s - crop q (t r) (line N x.val (missing (tag G) s)))) :
    Terms τ (fun r=>g r^k) (fun r (x: ↥(tsupport (Rose.test N.criterion)))=> value (watchRose F r x.val) -
      crop q (t r) (Select.Single (Bbook N 6) x.val)) := by
  let I:= ↥(tsupport (Rose.test N.criterion)); let a s r (x:I):= watchRose F r x.val s
  let pay s (x:I):= Rose.batchT (fxt (Bbook N 6) x.val) s
  have h (s : Badge) : Kept G (a s) t (pay s) k q := ⟨fun i _=> proper_line N M (Rose.test N.criterion).hasCompactSupport (Rose.test N.criterion).tsupport_subset H (missing (tag G) s) _, acts s⟩
  have a01:= Kept.times N M _ ht H (h {0,1}) (h {2}) hq; have a02:= Kept.times N M _ ht H (h {0,2}) (h {1}) hq
  have a12:= Kept.times N M _ ht H (h {1,2}) (h {0}) hq
  have v:= Kept.times N M _ ht H (Kept.times N M _ ht H (h {0}) (h {1}) hq) (h {2}) hq
  have W:=(Kept.add t (Kept.sub t (h Finset.univ) (Kept.add t (Kept.add t a01 a02) a12)) (Kept.add t v v)).2
  simp only [value, Select.Single, b3, two_smul,two_mul]; exact W

lemma posed_crop (q : ℕ) (hQ : 1 ≤ q) (r : ℝ) :
    (Rose.test N.criterion).applyTo (fun x=> crop q (t r) (Select.Single (Bbook N 6) x))=
      (Rose.cT N.criterion.cut G N.criterion.image:ℂ)*(t r:ℂ) := by
  rcases (ht.eventually (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists with ⟨_, _⟩
  simp only [crop_eq]; rw [Read.smear_sum]
  · simp_rw [Read.smear_one, registered N M H]; rw [Finset.sum_eq_single 1]; · simp [mul_comm (t r:ℂ)]
    · intro b hb h; simp [coeff_X, h]
    intro h; simp at h; omega
  intro i _; exact ((Select.steady _ (birth N M H 6).1).const_mul _).mono (Rose.test N.criterion).tsupport_subset

/-- Keep the actual signed mass. -/
theorem test_price (q k : ℕ) (hQ : 1≤q) (hq : k ≤ q+1)
    (h : ∀ s:Badge, ∀ᶠ r in τ, ContinuousOn (fun x=> watchRose F r x s) (conf 3))
    (acts : ∀ s:Badge, Terms τ (fun r=>g r^k)
      (fun r (x: ↥(tsupport (Rose.test N.criterion)))=> watchRose F r x.val s - crop q (t r) (line N x.val (missing (tag G) s)))) :
    (fun r=> (Rose.test N.criterion).applyTo (fun x=>value (watchRose F r x)) -
      (Rose.cT N.criterion.cut G N.criterion.image:ℂ)*(t r:ℂ))=O[τ] (fun r=>g r^k) := by
  let T:= Rose.test N.criterion
  obtain ⟨C,hC,hv⟩:= (posed N M t ht H q k hq acts).price
  apply IsBigO.of_bound (Read.Value T*C)
  filter_upwards [hv,eventually_all.mpr h] with r hh hp
  let A x:= value (watchRose F r x); let B x:= crop q (t r) (Select.Single (Bbook N 6) x)
  rw [← posed_crop N M t ht H q hQ]; change ‖T.applyTo A - T.applyTo B‖ ≤ _
  have he : ContinuousOn A (tsupport T) := by
    refine ContinuousOn.mono (t:=tsupport T) ?_ T.tsupport_subset
    unfold A value
    exact ((hp _).sub ((((hp _).mul (hp _)).add ((hp _).mul (hp _))).add ((hp _).mul (hp _)))).add
      (ContinuousOn.const_mul (((hp _).mul (hp _)).mul (hp _)) _)
  have hb : ContinuousOn B (tsupport T) := by
    unfold B; simp only [crop_eq]; exact continuousOn_finsetSum _ fun i _=> ((Select.steady _ (birth N M H 6).1).const_mul _).mono T.tsupport_subset
  rw [← Read.smear_sub T he hb,mul_assoc]; exact Read.value_le T (he.sub hb) (fun i hi=> hh ⟨i,hi⟩)
end
end YM.FVA2.GradedFar.Pose
