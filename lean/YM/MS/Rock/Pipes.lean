import YM.MS.Rock.Generate
/-!
# Arity and line algebra after theta scale

Omit Wick0 comparison assumption. Handy exact for real argument t (m integral out). -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock.Oceans
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Path Landau Arts Pilot Spin Arc Wire
open Metric
open scoped Topology ContDiff
variable {G:Gauge}{b c: Bool}{F H L:Mob G}{U V W:Rip G}{m:ℕ}
variable (hU: Knot b U)(hF : Form0 b F)(hV:Knot b V)(hH: Form0 b H){i:ℂ}(hi:i∈Town) (c:ℂ)
include hi hF hH hV hU
omit hH in
lemma oceanLsub : ocean i (U-V) F=ocean i U F-ocean i V F:= by simpa only [neg_one_smul,← sub_eq_add_neg] using Eq.trans (oceanL hU hF (hV.smul (-1)) hi) ( congr_arg (ocean i U F+ ·) (scaleL hV hF (-1)))
omit hV in
lemma oceanRsub : ocean i U (F-H)= ocean i U F-ocean i U H:= by simpa only [neg_one_smul, ← sub_eq_add_neg] using Eq.trans (oceanR hU hF (hH.smul (-1)) hi) (congr_arg (ocean i U F + ·) (scaleR hU hH (-1)))
omit hH hV hi in
lemma depth0 : ocean i U 0=0 := by simpa using scaleR (i:=i) hU (G:=G) hF 0 -- hF shouldn't needed next
lemma core_difference : ocean i U F-ocean i V H=ocean i U (F-H)+ocean i (U-V) H:= by rw [oceanLsub hU hH hV hi,oceanRsub hU hF hH hi]; abel
omit hF hH hU hV hi
lemma two_leg (U V:Rip G)(F H:Mob G): arbor (U+V) F H=arbor U F H+arbor V F H:= by
   funext i l; unfold arbor; let p:= Landau.parity (C:= G.ColorIndex) (A:=Arts.L i); let A:=(U i); let V0:= V i; let P:=allocate (field p) l (R:=ℂ); change P _=P (attaches p A _ _)+P (attaches p V0 _ _); rw [← map_add]; congr! 1; funext a b; simp only [attaches, Pi.add_apply, add_mul, sum_add_distrib]; abel
lemma down_leg (U:Rip G)(α:ℂ)(F H:Mob G): arbor (α • U) F H=α • arbor U F H:= by
   funext i l; let p:= Landau.parity (C:= G.ColorIndex) (A:=Arts.L i); let P:= allocate (field p) l (R:=ℂ); change P _= α • P (attaches p _ _ _); rw [← map_smul]; congr! 1; funext a b; simp only [attaches,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_add,mul_assoc]; rfl

-- algebra, Pair assembler
abbrev Pair (G:Gauge):= Signal.Pair (Mob G)
def squad (U: Rip G): Pair G where
   toFun F:= { toFun H i:= boulevard Landau.parity (U i) (F i) (H i), map_add' x y:= funext fun i=> map_add (boulevard Landau.parity (U i) (F i)) (x i) (y i), map_smul' c x:= funext fun i=> map_smul (boulevard Landau.parity (U i) (F i)) c (x i) }
   map_add' H F:= LinearMap.ext (fun G=> funext fun i=> map_add ( LinearMap.flip (boulevard Landau.parity (U i)) (G i)) (H i) (F i))
   map_smul' c F:= LinearMap.ext (fun G=> funext fun i=> map_smul ( LinearMap.flip (boulevard Landau.parity (U i)) (G i)) c (F i))
def sweepQ (Q:Shade G): Signal.MH (Mob G) where
  toFun:=portZ Q
  map_smul' c F:= funext fun i=> map_smul ((Q i).raise) c (F i)
  map_add' F H:= funext fun i=> map_add ((Q i).raise) (F i) (H i)
lemma schedule (U:Rip G)(F H:Mob G): squad U F H=arbor U F H:=rfl
lemma upcoming (Q:Shade G)(F: Mob G): sweepQ Q F=portZ Q F:= rfl
end YM.MS.Rock.Oceans
