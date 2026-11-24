import YM.RG11Proof.Fields.Compatible
import YM.RG11Proof.Fields.Response
import YM.RG11Proof.Bridge.All

/-!
# Formal comparison on the actual graded field system, per separated Test

Input two complex coefficient arrays on exactly the `E` through ALL
horizons. Same test tags continuously across horizons (pack all finite arities
only at separated geometry). Extract real coordinates in the built real nested
basis; detector→regulator absorption yields a common reverse coupling & matrix
there; we prove the full transformed coefficient equality on complex fields and
tests as a consequence. This file is a CONSUMER: do not supply arrays defined
by measurement of the desired correlations without a construction/identity with
the independent prescriptions! Standalone version needs the actual free `Frozen` above weight (proved for hSimple by RG11Proof/Rigidity/Frozen)
four (and actual predicate/load witnesses, e.g. hC.Makes and higher estimates on
one F, for physical use); only a conditional algebra/leading/regulator implication.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.RG11.Fields
open PowerSeries YM.RG11.Jets YM.PertExtension.Position YM.RG11.Horizon YM.RG11.Bridge YM.Pert.Triangle Labels Maxwell Function Set
open YM.Pert.Position (E wickReading Frozen)
open scoped Classical BigOperators Topology ContDiff
variable (G:Gauge)(F:Frames G)
/-- The shape reports at the level needed for this separated criterion; no
implication of scale law, origin/lift of insertions, locality or construction.
The exact physical Field d quotient and MS packing data must be supplied in the
PROVIDER. -/
structure ShapeReport where
  table (power horizon r:ℕ) : YM.Test r →ₗ[ℂ] MultilinearMap ℂ (fun _:Fin r=> E F horizon) ℂ
  maxwell (d r : ℕ)(v:YM.Test r)(t : Fin r→ E F d): table 0 d r v t= wickReading F d v t
  -- unrestricted field horizons; d<6 not used by detectors
  packs (d e r k : ℕ)(h:d ≤ e)(v:YM.Test r)(t:Fin r→ E F d):
       table k d r v t=table k e r v (up F h ∘ t)
variable {G F}

namespace ShapeReport
def realAt (A:ShapeReport G F) {d} (B:Basis F d) : ArrayAt B.J ℝ form:=
   fun v=>PowerSeries.mk fun k=> (A.table k d v.1.order v.1.test (fun i=>B.b (v.2 i))).re

@[simp] theorem price0 (A:ShapeReport G F) {d} (B:Basis F d) (v:Fields.point B): constantCoeff (A.realAt B v)=rowZero B v := by
   simp only [realAt,PowerSeries.constantCoeff_mk,A.maxwell]; rfl

def ticket (A:ShapeReport G F)(hg:G.Simple)(T: A.table 1 6 3 profileChoice (basic F) = cTest G) {d} (h:6≤d)(B:Basis F d)
    (hf:Frozen F d): Detector B.guard (A.realAt B):= by
  have hi:=free_from_frozen B (A.price0 B) hf
  let X := A.table 1 d 3
  have he (z v) : X (z • profileChoice) v = z * X profileChoice v := by rw [map_smul]; rfl
  have hu : X profileChoice (Fields.triple h F) = cTest G:= (A.packs 6 d 3 1 h profileChoice (basic F)).symm.trans T
  let t : RulerTest B.guard (A.realAt B):= probeRuler F hg h B (A.realAt B) (A.price0 B) X (fun _=> coeff_mk ..) he hu
  exact RulerTest.pin t (Detector.ofSees (Sees.of_parts hi t))

def mesh(A B : ShapeReport G F): Mesh ℝ form := asMesh F (fun i=>realAt A (tower F (6+i)).toBasis) (fun i=>realAt B (tower F (6+i)).toBasis)

theorem linked (A B : ShapeReport G F) : (mesh A B).Steady:=by
   have hp(C:ShapeReport G F){i j:ℕ}(h:i ≤ j):
       slice (rise F h) (C.realAt (tower F j).toBasis) = C.realAt (tower F i).toBasis:=by
     funext v; ext k
     simp_rw [slice,realAt,coeff_mk,view]
     apply congrArg Complex.re
     have he : (fun b=> (tower F j).b ((rise F h) (v.2 b)))=
        up F h ∘ (fun b=> (tower F i).b (v.2 b)):=funext fun b=> basis_rise F h _
     rw [he]; exact Eq.symm (C.packs _ _ _ _ h v.1.test (fun b=> (tower F i).b (v.2 b)))
   exact ⟨fun h=> (basis_rise F (Nat.add_le_add_left h _)).coherent,fun h=>hp A _,fun h=>hp B _⟩ -- binder implicit

/-- Exact array comparison, including a common inverse with the indicated
direction. Need one successful common-regulator proof for every large enough
finite demand, PROPERLY instantiated (Bridge.High), plus Frozen and prescribed
slope. Need these on SAME A,B arrays. -/
theorem consistent {α} (A B : ShapeReport G F)(hg:G.Simple)
   (ha: A.table 1 6 3 profileChoice (basic F) = cTest G)
   (he : ∀ d≥6,Frozen F d)
   (hw:Bridge.High (mesh A B) α):
    ∃ (T f : PowerSeries ℝ) (Z D:∀ n,Square (tower F (6+n)).toBasis.J ℝ⟦X⟧),
    (Coupling T ∧ Coupling f) ∧ PowerSeries.subst f T=X ∧ PowerSeries.subst T f=X ∧
    (∀ n, let V:=(tower F (6+n)).toBasis; Change.Good V.guard ⟨f,Z n⟩ ∧ Change.Good V.guard ⟨T,D n⟩ ∧
        Z n*subs f (D n)=1 ∧ D n*subs T (Z n)=1 ∧ B.realAt V=Change.act ⟨T,D n⟩ (A.realAt V) ∧ A.realAt V= Change.act ⟨f,Z n⟩ (B.realAt V)) ∧
    (∀ {n m:ℕ}(h:n ≤ m), Horizon.take (rise F (Nat.add_le_add_left h 6)) (D m)=D n ∧
                      Horizon.take (rise F (Nat.add_le_add_left h 6)) (Z m)=Z n):= by
  let M:=mesh A B
  obtain ⟨H⟩:= Bridge.all_compatible M (D:=fun n=> A.ticket hg ha (show 6≤6+n by omega) (tower F (6+n)).toBasis (he _ (by omega))) hw (A.linked B)
  obtain ⟨T,f,Z,D,hF,hTf,hfT,hi,hu⟩ := Bridge.read M H (A.linked B)
  refine ⟨T,f,Z,D,hF,hTf,hfT,fun i=> ?_,fun h=> hu h⟩
  convert! hi i
end ShapeReport
end YM.RG11.Fields
