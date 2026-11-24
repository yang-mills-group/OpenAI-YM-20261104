import YM.GradedFar.Physical.Actual
import YM.OPE.Orbits.System
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! The operand check for the continuation.

Quantify over an actual `Family`, `Spec.Final` etc. in this project. And work
on any frames provided as linear isomorphisms, in order to specialize to precisely
the prescribed physical H (in the downstream application). Here the fields are in the
actual quotients on this `Table`.
-/
namespace YM.FVA2.GradedFar.Physical
noncomputable section
open Filter Function Real PowerSeries Set
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open Continuation Continuation.Window
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m h : ℕ} (N : WilsonPrescription G) {d : Fin n → ℕ} {e : Fin m → ℕ}
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple}
    {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P)
variable (J : FramesH P)
def atPos (r : ℝ) (o : E4) (x : Points n) : Fin n → E4 := fun i => o + r • x i
def here (r : ℝ) (v : Inputs G d) : OPE.Orbits.Labels P d := fun i => J r (d i) (v i)

def Ywide (w : Window) (i : View U) (x : Points n) (y : Points m) (u : Inputs G d) (v : Inputs G e) : ℂ :=
  OPE.Orbits.whole (OPE.spectator U i.1) (atPos w.len i.2 x) (here J w.len u)
    (atPos w.Coarse i.2 y) (here J w.Coarse v)
def Dwide (w : Window) (i : View U) (y : Points m) (v : Inputs G e) (a : Sec G h) : ℂ :=
  Ywide U J w i (0:Points 1) y (d:=fun _ => h) (fun _ => a) v

-- expose as in M.2 first arithmatic lemma
private def holdF (u : OPE.Orbits.Labels P d) (x : Fin n → E4) (y : Fin m → E4) (i : View U) :
    MultilinearMap ℂ (fun k => P.Field (e k)) ℂ :=
  MultilinearMap.currySum (OPE.Orbits.moment (S:=P) (OPE.spectator U i.1) (d:=Sum.elim d e) (OPE.beside x y)) u
private lemma holdF_apply (u : OPE.Orbits.Labels P d) (v : OPE.Orbits.Labels P e) (x : Fin n → E4)
    (y : Fin m → E4) (i : View U) :
    holdF U u x y i v = OPE.Orbits.whole (OPE.spectator U i.1) x u y v := by
  change OPE.Orbits.moment (d:=Sum.elim d e) (S:=P) (OPE.spectator U i.1) (OPE.beside x y) (Sum.rec u v) = _
  unfold OPE.Orbits.whole; congr 1; funext t; cases t<;>rfl

def Y0 (d : Fin n → ℕ) (e : Fin m → ℕ) : ReadAt G d e (View U) := fun w i x y u =>
  (holdF (e:=e) U (here J w.len u) (atPos w.len i.2 x) (atPos w.Coarse i.2 y) i).compLinearMap
    (fun k => (J w.len (e k)).toLinearMap)
lemma Y0_value (w : Window) (i : View U) (x : Points n) (y : Points m) (u : Inputs G d) (v : Inputs G e) :
    Y0 U J d e w i x y u v =
      OPE.Orbits.whole (OPE.spectator U i.1) (atPos w.len i.2 x) (here J w.len u)
        (atPos w.Coarse i.2 y) (here J w.len v) := holdF_apply U _ _ _ _ _

def adjusted : ChangeAt G := fun d w => ((J w.Coarse d).trans (J w.len d).symm).toLinearMap

lemma unchanged (d : Fin n → ℕ) (u : Inputs G d) (w : Window) : here J w.Coarse u=here J w.len (Coat (adjusted J) w u) := by
  funext j; change _ = J w.len _ ((J w.len _).symm _)
  rw [LinearEquiv.apply_symm_apply]; rfl
lemma full_same (w : Window) (i : View U) (x : Points n) (y : Points m) (u : Inputs G d) (v : Inputs G e) :
    Ywide U J w i x y u v = YCoat (adjusted J) (Y0 U J d e) w i x y u v := by
  unfold YCoat Ywide
  rw [Y0_value,unchanged J e v]
lemma center_same (w : Window) (i : View U) (y : Points m) (v : Inputs G e) (a : Sec G h) :
    Dwide U J w i y v a = DCoat (adjusted J) (Y0 U J (fun _ : Fin 1 => h) e) w i y v a := full_same ..
lemma at_center (w : Window) (i : View U) (y : Points m) (v : Inputs G e) (a : Sec G h) :
    Dwide U J w i y v a =
      OPE.Orbits.whole (OPE.spectator U i.1) (fun _ : Fin 1 => i.2) (here J w.len (d:=fun _ : Fin 1 => h) (fun _ => a))
        (atPos w.Coarse i.2 y) (here J w.Coarse v) := by
  unfold Dwide Ywide; rw [show atPos w.len i.2 0=(fun _ : Fin 1 => i.2) by funext i; simp [atPos]]

/-- True (one inserted central field, on the same H_r) replacement operator. -/
def receive (w : Window) (i : View U) (y : Points m) (v : Inputs G e) (h : ℕ) : Sec G h →ₗ[ℂ] ℂ :=
  let B := (OPE.Orbits.sectionLabels (d:=Sum.elim (fun _ : Fin 1 => h) e) (here J w.Coarse v)
    (OPE.Orbits.moment (OPE.spectator U i.1) (OPE.beside (fun _ : Fin 1 => i.2) (atPos w.Coarse i.2 y))))
  -- restrict this MLM to its single slot
  (B.toLinearMap 0 0) ∘ₗ (J w.len h).toLinearMap

lemma receive_leg (w : Window) (i : View U) (y : Points m) (v : Inputs G e) (a : Sec G h) :
    receive U J w i y v h a = Dwide U J w i y v a := by
  rw [at_center]
  let p := OPE.Orbits.moment (S:=P) (d:=Sum.elim (fun _:Fin 1=>h) e) (OPE.spectator U i.1) (OPE.beside (fun _ : Fin 1=> i.2) (atPos w.Coarse i.2 y))
  let L:= OPE.Orbits.sectionLabels (d:=Sum.elim (fun _:Fin 1=>h) e) (here J w.Coarse v) p
  have h0 : ∀ u: OPE.Orbits.Labels P (fun _ : Fin 1=>h), L u = p (OPE.Orbits.stages u (here J w.Coarse v)):= fun u=>OPE.Orbits.sectionLabels_apply (e:=e) (here J w.Coarse v) p u
  let d':Fin 1→ℕ:=fun _=>h
  let u': OPE.Orbits.Labels P d':=update (β:=fun _=>P.Field h) (fun _=>0) (0:Fin 1) (J w.len _ a)
  have hu':u'=here J w.len (d:=fun _ :Fin 1=> h) (fun _=>a) := by funext i; fin_cases i; simp [u',here]
  change L u' = _; exact (h0 u').trans (congrArg (fun u:OPE.Orbits.Labels P d'=> p (OPE.Orbits.stages u (here J w.Coarse v))) hu')

def packet (Q : OPE.Orbits.Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (d : Fin n → ℕ) (h : ℕ) : PacketAt G d (View U) h :=
  fun r i x u => (J r h).symm (Q.packet h (atPos r i.2 x) (here J r u) i.2)
end
end YM.FVA2.GradedFar.Physical
