import YM.FVA2.Press.Ports
/-!
# Linearized Survey on all oriented links on Cover
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Press
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Source.Drops Bid Work XSpace
open MS.Native
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge} {d:ℕ} {H:Hol G} (A:XSpace.Survey G H d)
local notation "T" => Fin A.size
local notation "J" => Local A
local notation "E" => tilt A
local notation "V" => CoverConfig G
local notation "B" => GaugePanel G A.size
local notation "C" => G.Color
local notation "X" => Edge Cover

/-- Plane log without a stagger. -/
private def glow (x:Edge Cover→C) (t:ℝ) : CoverConfig G:= fun e=>G.lieExp (t • x e)
private lemma glow_zero (x:X→C) : glow x 0=1:= by funext l; simp [glow]
open Exterior
lemma walk_D (x:X→C)(o:Cover)(p:Walk) : HasDerivAt (fun t:ℝ=> G.mat (travel (glow x t) o p)) (G.colorMat (linkSum x o p)) 0:= by
 induction p generalizing o with
 | nil=> rw [linkSum,map_zero]; exact hasDerivAt_const ..
 | cons i w ih=>
    let f(i:Step)(p:Cover):= if i.neg then -x (i.used p) else x (i.used p); have he : HasDerivAt (fun t=>G.mat (i.read (glow x t) o)) (G.colorMat (f i o)) 0:= by
       unfold Step.read f; split
       · rw [map_neg]; simp_rw [G.mat_inv, ← G.colorMat_skew]; exact (MS.Bare.Maurer.colorDerivative (x _)).star
       exact MS.Bare.Maurer.colorDerivative (x _)
    have hh:= he.mul (ih (o+i.vec)); have hu: i.read (glow x 0) o=1:= by rw [glow_zero]; unfold Step.read; split<;>simp
    rw [hu, glow_zero, basic_walk, G.mat_one,mul_one,one_mul] at hh
    rw [linkSum,map_add]; simp_rw [travel,G.mat_mul]; exact hh
lemma slot_D (x:X→C)(a:Slot) : HasDerivAt (fun t:ℝ=> a.eval (glow x t)) (Exterior.linkSum x a.offset (square a.plaq.val.1 a.plaq.val.2)) 0:= by
    let f:=fun t=>faceValue (glow x t) (a.offset,a.plaq); let g:= fun t=> travel (glow x t) 0 a.walk
    have h:= walk_D x a.offset (square a.plaq.val.1 a.plaq.val.2); have he:= walk_D x 0 a.walk; simp_rw [Slot.eval,← G.curvature_conjugate]; apply Work.F03.curvature_of_hasDerivAt; simp_rw [G.mat_mul,G.mat_inv]; convert! ((he.mul h).mul he.star) using 1; simp [glow_zero,basic_walk, G.colorMat_skew]

def coord (A:XSpace.Survey G H d) : (Edge Cover→ G.Color)→ₗ[ℝ] Local A→G.Color:= LinearMap.pi fun i=> LinearMap.proj i.val
lemma curl_link (x:X→C)(a:Fin A.size): fderiv ℝ (lamp A) 0 (coord A x) a= linkSum x (A.looks a).offset (square (A.looks a).plaq.val.1 (A.looks a).plaq.val.2):= by
    let c := coord A x; let p:=A.looks a; let L:=lamp A; have he(t:ℝ): p.eval (glow x t)= L (t • c) a:= congr_fun (reception A (t • c) (t:=glow x t) (by intro i; rfl)) a
    let q : (B) →L[ℝ] C:=ContinuousLinearMap.proj a
    have h : HasDerivAt (fun t=>p.eval (glow x t)) (q (fderiv ℝ L 0 c)) 0:= by
       rw [funext he]; have H:= (q.hasFDerivAt.comp 0 ((lamp_smooth A).differentiable (by simp) 0).hasFDerivAt) ; have ht: HasDerivAt (fun t:ℝ=> t • c) c 0:= by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const c
       exact H.comp_hasDerivAt_of_eq 0 ht (zero_smul ..).symm
    exact h.unique (slot_D x p)
lemma project_d (x:Snap G d) : A.extract (fderiv ℝ (lamp A) 0 (coord A (access x))) = x:= by
    refine Eq.trans (congr_arg A.extract ?_) (A.linear_jet x); exact funext fun i=> curl_link A _ i
lemma gauge_d (x: Cover→ C) : A.extract (fderiv ℝ (lamp A) 0 (coord A (fun l=> x (l.1+step l.2)-x l.1)))=0:= by
    let f (l:X):= x (l.1+step l.2)-x l.1; have he: fderiv ℝ (lamp A) 0 (coord A f)=0:= by
       funext i; rw [curl_link,Work.G03.square_sum]; dsimp only [f]; rw [add_right_comm (A.looks i).offset];change _= (0:C); abel
    change A.extract (fderiv ℝ _ _ (coord A f))=_; rw [he,map_zero]
end YM.FVA2.Press
