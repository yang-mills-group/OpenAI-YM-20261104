import YM.Dict06.Wilson.Walk
import YM.Dict06.Series.Lowest
import YM.Dict06.Series.Smooth
import YM.Bid.Source
import YM.Work.G06.TurnSlot

/-! Slot coefficient algebra on the cover: walk to the plaquette base,
plaquette, return on the reverse walk, then 
  `κ(Y) = projectColor( (Y-Y^*) / 2 )`.
Includes the effects of transports at higher orders. `path.length` counts
the outward walk only for the stored RG slot; loopSeries in this module uses
twice the walk length plus four. No limiting stencil or on-shell relation.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Dict06.Wil
open PowerSeries Function Series Lattice Wilson Exterior RG
open scoped BigOperators Matrix.Norms.Frobenius Topology ContDiff
attribute [local instance] Gauge.frobInner
variable {G : Gauge}

def basedWalk (s : Slot) : Walk :=
  s.walk ++ square s.plaq.val.1 s.plaq.val.2 ++ Lattice.reverse s.walk
lemma walkLength (s : Slot) : (basedWalk s).length=2*s.walk.length+4 := by
  simp [basedWalk,Lattice.reverse,square]; omega

def curvatureRead (G : Gauge) : G.Mat →L[ℝ] G.Color :=
  G.projectColor.toContinuousLinearMap ∘L ((1/2:ℝ) • ((ContinuousLinearMap.id ℝ G.Mat) -
    (starL' ℝ : G.Mat ≃L[ℝ] G.Mat).toContinuousLinearMap))
lemma curvature_at (m : G.Mat) :
    curvatureRead G m = G.projectColor ((1/2:ℝ) • (m-star m)) := rfl
lemma curvature_unit : curvatureRead G 1=0 := by simp [curvature_at]
lemma curvature_letter (a : G.Color) : curvatureRead G (G.colorMat a)=a := by
  rw [curvature_at,G.colorMat_skew,sub_neg_eq_add,←two_smul ℝ,smul_smul]; norm_num

/-- Exact evaluation through one matrix loop. -/
lemma loop_read (s : Slot) (U : CoverConfig G) :
    s.eval U = curvatureRead G (G.mat (travel U 0 (basedWalk s))) := by
  rw [basedWalk, travel_append,travel_append,stop_append,square_stop,travel_reverse]
  exact (G.curvature_conjugate (travel U 0 s.walk) (faceValue ..)).symm

private lemma telescopic_append {X D : Type*} [AddCommGroup X] [One X] [AddCommGroup D]
    (A : Links X D) (x : Four X) (w q : Walk) :
    linkSum A x (w++q)=linkSum A x w + linkSum A (stop x w) q := by
  induction w generalizing x <;> simp_all [linkSum,stop,add_assoc]
private lemma telescopic_reverse {X D : Type*} [AddCommGroup X] [One X] [AddCommGroup D]
    (A : Links X D) (x : Four X) (w : Walk) :
    linkSum A (stop x w) (Lattice.reverse w) = -linkSum A x w := by
  induction w generalizing x with
  | nil => simp [linkSum, stop,Lattice.reverse]
  | cons d w ih=>
    rw [Lattice.reverse,List.reverse_cons,List.map_append,telescopic_append]
    simp only [stop, show w.reverse.map Step.rev = Lattice.reverse w from rfl,ih,reverse_stop,List.map_cons,List.map_nil,linkSum,add_zero]
    rcases d with ⟨a,(_|_)⟩ <;> simp [Step.vec, Step.used, Step.rev,sub_eq_add_neg, add_comm]
lemma cancel (A : Links ℤ G.Color) (s : Slot) :
    linkSum A 0 (basedWalk s) = linkSum A s.offset (square s.plaq.val.1 s.plaq.val.2) := by
  rw [basedWalk,telescopic_append,telescopic_append,stop_append,square_stop,telescopic_reverse]; dsimp only [Slot.offset]; abel
lemma gradient_walk {X D : Type*} [AddCommGroup X] [One X] [AddCommGroup D] (p : Four X→D)
    (x : Four X) (w : Walk) :
    linkSum (fun e : Edge (Four X)=>p (e.1+step e.2)-p e.1) x w=p (stop x w)-p x := by
  induction w generalizing x with
  | nil => simp [linkSum,stop]
  | cons d w ih=>
    rw [linkSum,ih]; rcases d with ⟨a,(_|_)⟩ <;> simp [Step.vec,Step.used,stop,sub_eq_add_neg] <;> abel
lemma gradient_square {X D : Type*} [AddCommGroup X] [One X] [AddCommGroup D] (p : Four X→D)
    (x : Four X) (a b : Axis) :
    linkSum (fun e : Edge (Four X)=>p (e.1+step e.2)-p e.1) x (square a b)=0 := by
  rw [gradient_walk,square_stop,sub_self]

def slotInk (c : G.ColorIndex) : G.Mat →L[ℝ] ℂ :=
  Complex.ofRealCLM ∘L EuclideanSpace.proj (𝕜:=ℝ) c ∘L curvatureRead G

def slotSeries (A : Links ℤ G.Color) (s : Slot) (c : G.ColorIndex) : PowerSeries ℂ :=
  PowerSeries.mk fun n => slotInk (G:=G) c (coeff n (path A 0 (basedWalk s)))

lemma honest_slot (A : Links ℤ G.Color) (s : Slot) (c : G.ColorIndex) :
    ContDiff ℝ ∞ (fun t => ((s.eval (positive A t) c:ℝ):ℂ)) ∧
      ps (fun t => ((s.eval (positive A t) c:ℝ):ℂ)) = slotSeries A s c := by
  let T (t :ℝ) := G.mat (travel (positive A t) 0 (basedWalk s))
  have he : (fun t => ((s.eval (positive A t) c:ℝ):ℂ)) = slotInk (G:=G) c ∘ T := by
    funext t; rw [loop_read]; rfl
  obtain ⟨h,hp⟩:=honest_walk A 0 (basedWalk s)
  change ps T=path A 0 (basedWalk s) at hp
  have h : ContDiff ℝ ∞ T := h
  rw [he]; refine ⟨(slotInk c).contDiff.comp h,?_⟩
  ext1 n
  rw [ps_at]; erw [ordinary_map T n (h.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) (slotInk c),←ps_at, hp, slotSeries, coeff_mk]; rfl

/-- First link-degree content, with unshifted positive plaquette curls read
at shifted slots. Compatible with the access direction in Source.Drops.glow.
-/
lemma initial_slot (A : Links ℤ G.Color) (s : Slot) (c : G.ColorIndex) :
    Initial 1 (slotSeries A s c) ((linkSum A s.offset (square s.plaq.val.1 s.plaq.val.2) c : ℝ) : ℂ) := by
  constructor
  · intro i hi; obtain rfl : i=0 := by omega
    rw [slotSeries,coeff_mk,(path_first A 0 (basedWalk s)).1]
    change (((curvatureRead G 1) c : ℝ):ℂ)=0
    simp [curvature_unit]
  rw [slotSeries,coeff_mk,(path_first A 0 (basedWalk s)).2, cancel]
  change (((curvatureRead G (G.colorMat _)) c:ℝ):ℂ)=_
  rw [curvature_letter]

open Lattice Wilson Bid Source.Drops
variable {m : ℕ}

def palette (A : Links ℤ G.Color) (B : Fin m → Slot) : Fin m×G.ColorIndex → PowerSeries ℂ :=
  fun i => slotSeries A (B i.1) i.2

def poseSymbol (A : Links ℤ G.Color) (B : Fin m → Slot) := poly (palette A B)
lemma honest_pose (A : Links ℤ G.Color) (B : Fin m → Slot) (P:Pose G m) :
    ContDiffAt ℝ ∞ (fun t=>lumin P (mapped B (positive A t))) 0 ∧
      ps (fun t=>lumin P (mapped B (positive A t))) = poseSymbol A B P := by
  let f := fun (i : Fin m×G.ColorIndex) t=> (((B i.1).eval (positive A t) i.2:ℝ):ℂ)
  have he := readPoly_ps f P (fun i=>(honest_slot A (B i.1) i.2).1.contDiffAt)
  have hh : (fun t=>lumin P (mapped B (positive A t))) = readPoly f P := by
    funext t
    simp only [lumin, readPoly, mapped,MvPolynomial.aeval_eq_eval₂Hom,Algebra.algebraMap_self,MvPolynomial.eval] -- test
    rfl
  rw [hh]; unfold poseSymbol; exact ⟨he.1,he.2.trans (congrArg (fun k=>poly k P) (funext fun i=>(honest_slot A (B i.1) i.2).2))⟩

def curlPose (A : Links ℤ G.Color) (B : Fin m → Slot) (i:Fin m×G.ColorIndex) : ℂ :=
  let v:= B i.1
  ((linkSum A v.offset (square v.plaq.val.1 v.plaq.val.2) i.2:ℝ):ℂ)

def linearStart (A : Links ℤ G.Color) (B : Fin m → Slot) (P : Pose G m) (k:ℕ) : ℂ :=
  ∑ d∈P.support,
     if count d=k then MvPolynomial.coeff d P * ∏ j∈d.support, curlPose A B j ^ d j
     else 0
lemma initial_pose (A : Links ℤ G.Color) (B : Fin m → Slot) (P : Pose G m)
    (k : ℕ) (hp : lows P k) :
    Initial k (poseSymbol A B P) (linearStart A B P k) :=
  Initial.scalarPoly P k (palette A B) (curlPose A B) (fun i=>initial_slot A (B i.1) i.2) hp
end YM.Dict06.Wil
