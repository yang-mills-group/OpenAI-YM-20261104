import YM.XSpace.LiftCyl
import YM.MS.Wilson.Sew
import YM.MS.Lifting.PureMark
import YM.FVA2.Change.Prescription
/-!
# The physical nonlinear Survey stencil, on full MS log fields

Use arbitrary `YM.XSpace.Survey`. This really has the nonlinear holonomy jet assertion (see
A.projects). Implement with shared finite panel for real and complex linear extension and
aliases. Then in downstream file show that its leading rank is the same leading
free representative in the manuscript MS lift. This is not using a different stencil for each
phase or test location. See e.g. `reflecting` for use even with wrapping offsets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Press
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Source.Drops Bid Work XSpace
open MS MS.Koszul MS.Plane MS.Orbit MS.Swirl MS.Native MS.Cylinder Lab Sew MS.Native.Draft
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge} {d:ℕ} {H:Hol G} (A:XSpace.Survey G H d)
local notation "T" => Fin A.size

-- enough to keep all positive links at the vertices in these stencils, not only used edges
def knots := ( (Finset.univ:Finset (Fin A.size)).biUnion fun i=> (A.looks i).stencil ) ×ˢ (Finset.univ:Finset Axis)
abbrev Local (A:XSpace.Survey G H d) := {x:Edge Cover // x∈knots A}
abbrev tilt (A:XSpace.Survey G H d) := Local A→G.Color
instance : Fintype (Local A):= (knots A).fintypeCoeSort
local notation "J" => Local A
local notation "E" => tilt A
local notation "V" => CoverConfig G
local notation "B" => GaugePanel G A.size
local notation "C" => G.Color

def pad (u:E) : V:= fun i=> if h:i∈ knots A then G.lieExp (u ⟨i,h⟩) else 1
def lamp (u:E)(x:Fin A.size): G.Color := (A.looks x).eval (pad A u)
lemma looks (x:E): lamp A x= mapped A.looks (pad A x):= rfl
lemma beams (x:Fin A.size){i:Edge Cover} (h:i.1 ∈ (A.looks x).stencil) : i∈knots A:= mem_product.mpr ⟨ mem_biUnion.mpr ⟨x,mem_univ _,h⟩,mem_univ _⟩
lemma reception (x:E){t: CoverConfig G}(h:∀ i : J, t i.val = G.lieExp (x i)): mapped A.looks t=lamp A x := by
    funext i; rw [lamp]; apply (A.looks i).covered; intro j hj _; unfold pad; rw [dif_pos (beams A i hj)]; exact h ⟨j,beams A i hj⟩
lemma lamp_map (x:Edge Cover→ C) : mapped A.looks (G.lieExp ∘ x) = lamp A (x ∘ Subtype.val):= reception _ _ (by intro i;rfl)
lemma basic_walk (x:Cover)(w:Walk) : travel (K:=G.El) (1:CoverConfig G) x w=1:= by induction w generalizing x with | nil=> rfl | cons i w h=> rw [travel,h,mul_one,Step.read];split <;> simp
lemma lamp0 : lamp A 0=0:= by
    funext i; unfold lamp Slot.eval; rw [show pad A 0 =1 from ?_, faceValue, basic_walk,basic_walk,G.curvature_unit, map_zero];rfl
    ext1 j; unfold pad; split <;> simp
lemma mat_hot (l:Edge Cover) : ContDiff ℝ ω (fun x:E => G.mat (pad A x l)):= by unfold pad; split; exact G.exp_jet.comp (contDiff_apply ..); exact contDiff_const
lemma walkg (l:Cover)(w:Walk): ContDiff ℝ ω (fun x:E=> G.mat (travel (pad A x) l w)):= by
    induction w generalizing l with
    | nil=> exact contDiff_const
    | cons i w h => simp_rw [travel,G.mat_mul]; refine ContDiff.mul ?_ (h _); unfold Step.read; split;exact ((starL ℝ : G.Mat≃L[ℝ]G.Mat).contDiff.comp (mat_hot A _)); exact mat_hot ..
lemma lamp_smooth : ContDiff ℝ ω (lamp A):= by
    apply contDiff_pi.mpr; intro i
    let f:= fun x:E=> faceValue (pad A x) (((A.looks i).offset),(A.looks i).plaq); let g:= fun x:E=> travel (pad A x) 0 (A.looks i).walk
    let c:=fun x:E=>g x * f x * (g x)⁻¹; have hh : ContDiff ℝ ω (fun x:E=> G.mat (c x)):= ((walkg A _ _).mul (walkg A _ _)).mul ( (starL ℝ : G.Mat≃L[ℝ] G.Mat).contDiff.comp (walkg A _ _) )
    let D:= G.projectColor.toContinuousLinearMap; rw [show (fun x:E=>lamp A x i)=fun x:E=> G.curvature (c x) from funext fun i=>(G.curvature_conjugate ..).symm]; unfold Gauge.curvature; exact D.contDiff.comp ( (hh.sub ( (starL ℝ : G.Mat≃L[ℝ]G.Mat).contDiff.comp hh )).const_smul (1/2:ℝ) )
variable {n: Side}
def threaded (n:Side)(x: Chart.City G (Site n)):= Sew.pull (Sew.thread (wrap n) (fun i:J=>i.val)) x
lemma wrapped (l:Site n)(x:Wilson.Config G n): (expandAt 0 (Lattice.translate l x))=expandAt l x:= by funext i; simp [expandAt,Lattice.translate]
lemma reflecting (x: Chart.City G (Site n)): mapped A.looks (expandAt 0 (Chart.nation x))= lamp A (threaded A n x):= reception A _ (by intro i; unfold expandAt; rw [add_zero]; rfl)
end YM.FVA2.Press
