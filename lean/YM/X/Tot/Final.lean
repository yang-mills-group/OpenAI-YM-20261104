import YM.X.Tot.Figure
/-!
# Absorbs masks. Programs credited full notation. Uses compact physical positions, masks centered there. This is the actual Expression for the PT first and unconditioned moments at unselected T fields subject H from Try.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri Plate LiftMark Hinge Bare Pulse Labels Pert.RawLabels Crystal Gravity
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {F: Labels.Frames G} {d k:ℕ} {V I:Type*} {r R:ℝ} {n:Side}
variable (S:Shop F)(q:ℕ+)(χ:Floor R)
local notation "μ"=> flow G n
local notation "N"=> side q k
local notation "Q"=> qu q G
local notation "ε"=>epsilon q k
variable (X:Fin 3→Fielding.Walk) (o:Site (side q k)) (v:Fin 3→ Pert.Position.E F d)
local notation "κ"=> Hinge.shock
local notation "Z"=> handV d v
local notation "P"=> pV S q d v
local notation "T"=> pV₁ S q χ d v
local notation "P₀"=> held S ε⁻¹ d 0
local notation "s₀"=> (postal X o k)
def gap (i:Fin 3):= chapters (Function.update (fun j=> sales (d:=d) S 0 ε (s₀ j)) i ((hairAt (s₀ i)).toLinearMap ∘ₗ splurge q χ d S k)) 1 Z
def Φ (q:ℕ+) (X:Fin 3→ Fielding.Walk) (U V:Fin 3→Foam G) (i j l:Fin 3):ℕ→ℂ:=gather q (X i) (X j) (X l) (V i) (U j) (U l)
abbrev leafπ (i:Fin 3) := Lift (X i) (P i) k
local notation "η"=> leafπ (k:=k) S q X v
lemma dealt (i:Fin 3): gap S q χ X o v i= let f:=Function.update (P₀∘Z) i (splurge q χ d S k (Z i)); tri (Q k) (liftedA (X 0 k) N (f 0)) (liftedA (X 1 k) N (f 1)) (liftedA (X 2 k) N (f 2)):= by dsimp only; rw [gap,patchA,root3]
def poi (i:Fin 3):= liftedA (X i k) N (splurge q χ d S k (Z i))
lemma poiN (i:Fin 3) : liftedA (X i k) N ((P₀∘Z) i)= η i:= by unfold liftedA; rw [← Fund.milked];exact stances S q X v i
lemma pocket :∑ i:Fin 3,gap S q χ X o v i=tri (Q k) (poi S q χ (k:=k) X v 0) (η 1) (η 2)+tri (Q k) (poi (k:=k) S q χ X v 1) (η 2) (η 0)+tri (Q k) (poi (k:=k) S q χ X v 2) (η 0) (η 1):= by
   let v₁(i:Fin 3):= gap S q χ X o v i; rw [Fin.sum_univ_three]; simp_rw [dealt];
   simp only [Function.update_self, Function.update_of_ne (show (0:Fin 3)≠1 by decide),Function.update_of_ne (show (1:Fin 3)≠0 by decide), Function.update_of_ne (show (1:Fin 3)≠2 by decide),Function.update_of_ne (show (2:Fin 3)≠1 by decide), Function.update_of_ne (show (0:Fin 3)≠2 by decide), Function.update_of_ne (show (2:Fin 3)≠0 by decide),poiN];
   unfold poi; nth_rw 1 [tri_spin _ (η 0), tri_rotate _ (η 0) (η 1)]
lemma vertex_hours : hours S s₀ ε (gas G N) d Z= crow q (fun i z=> space (Q i) (Lift (X 0) (P 0) i) (Lift (X 1) (P 1) i) (Lift (X 2) (P 2) i) (EngineP q G i z)) k:= by
    rw [nook,←mul_assoc (dress _ _),basin_shock]; unfold crow; apply congr_arg (volS q k * ·); apply Finset.sum_congr rfl; intro i hi; dsimp only; simp_rw [stances]; -- k beta
-- ∗budget formula units∗
def displayY (q:ℕ+)(χ:Floor R)(X:Fin 3→Fielding.Walk)(U V:Fin 3→Foam G)(v:Billboard G q): ℕ→ℂ:=
    Φ q X U V 0 1 2 + Φ q X U V 1 2 0+ Φ q X U V 2 0 1-bill q (X 0) (X 1) (X 2) χ (cloak q (X 0) (U 0)) (cloak q (X 1) (U 1)) (cloak q (X 2) (U 2)) v
lemma per_current (i j l:Fin 3) : tri (Q k) (poi (k:=k) S q χ X v i) (η j) (η l)= Φ q X P T i j l k + tri (Q k) (dress (X i k) (multi (Q k) (P i k) (mask q χ k))) (η j) (η l):= by
   unfold poi liftedA; change tri (Q k) (dress (X i k) (milk (Q k) _)) _ _=_; rw [show milk (Q k) _= T i k+multi (Q k) (P i k) (mask q χ k) from ?_,map_add,tri_plus]; rfl
   change _= highs q χ S d (Z i) k + multi (Q k) _ _; rw [stitch,show ((stance S q d) (Z i))=P i from rfl, sub_add_cancel]
lemma shows (h:∀ z∈ (Floor.maskL q χ k).support, lift (wrap (side q k) z)=z) : probeX q S (Pulse.away (k:=k) (q:=q) S χ d) k s₀ v= displayY q χ X P T (EngineP q G) k:= by rw [first_sum S q χ X o v, vertex_hours (v:=v)]; change (∑ i:Fin 3,gap S q χ X o v i)-_=_; rw [pocket]; unfold displayY; simp only [Pi.sub_apply,Pi.add_apply, per_current, absorb (k:=k) q χ (X 0) (X 1) (X 2) (P 0) (P 1) (P 2) h]; unfold leafπ; ring
end YM.PositionX.Tot
