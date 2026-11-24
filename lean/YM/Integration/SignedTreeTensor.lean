import YM.Integration.SignedTreeTransport
import YM.Integration.SignedTensor
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! Multilinearity of the independent MS tree output and the original
normalized finite joint input/exterior moment, including the physical
horizon inclusions before applying the running frame. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.SignedTreeTensor
open Function Set Spec OPE OPE.Orbits PhysMS Wilson
open Pert.Position Maxwell Maxwell.Free Maxwell.Wick MSbar.OPE RG11.Fields RG11.Grove
open Next.Rank.Normal OPETreeRemainder SignedTreeTransport
open scoped Classical BigOperators

variable {G : Gauge} {n m i d : ℕ}

def polynomial (F : Labels.Frames G) (x : conf n) (k : ℕ) :
    MultilinearMap ℂ (fun _ : Fin n => E F i) (WickPol G) :=
  ((tier scaleW k).comp ((send x.val k 1).toLinearMap.comp (milk (frameX x.property)))).compMultilinearMap
    ((MultilinearMap.mkPiAlgebra ℂ (Fin n) (poly (Mark G n))).compLinearMap
      (fun a => (post a).toLinearMap.comp (Maxwell.Free.address F i)))

theorem polynomial_apply (F : Labels.Frames G) (x : conf n) (k : ℕ) (v : Fin n → E F i) :
    polynomial F x k v = glued x.property (polynomials F i v) k := rfl

/-- Every complete finite-part MS tree output is multilinear in the
original independently chosen filtered fields. -/
def coefficient (F : Labels.Frames G) (x : conf n) (k : ℕ) :
    MultilinearMap ℂ (fun _ : Fin n => E F i) (E F k) :=
  (fields F k).symm.toLinearMap.compMultilinearMap
    ((polynomial F x k).codRestrict (shellSector G k)
      (fun v => glued_physical (fun g a => (sector.mp (address_in F i (v a))).2 g) x.property k))

theorem coefficient_apply (F : Labels.Frames G) (x : conf n) (k : ℕ) (v : Fin n → E F i) :
    coefficient F x k v = output F x v k := rfl

variable {C : Family G} {S : Table C.book}

def projectOutside (j d m : ℕ) (L : E C.labels d →ₗ[ℂ] E C.labels j) :
    MultilinearMap ℂ (fun _ : Fin m => E C.labels j) ℂ →ₗ[ℂ]
      MultilinearMap ℂ (fun _ : Fin m => E C.labels d) ℂ where
  toFun T := T.compLinearMap (fun _ => L)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pair (T : Table C.book) (J : ℝ → PhysMS.tower S) (r : ℝ) (x : Points (n+m)) :
    MultilinearMap ℂ (fun _ : Fin n => E C.labels i)
      (MultilinearMap ℂ (fun _ : Fin m => E C.labels d) ℂ) :=
  let A := (S.classMoment T (fun _ : Fin (n+m) => max i d) (r • x)).compLinearMap
    (fun _ => (J r (max i d)).toLinearMap)
  (projectOutside (max i d) d m (RG11.Fields.up C.labels (le_max_right i d))).compMultilinearMap
    (((A.domDomCongr finSumFinEquiv.symm).currySum).compLinearMap
      (fun _ => RG11.Fields.up C.labels (le_max_left i d)))

theorem pair_apply (T : Table C.book) (J : ℝ → PhysMS.tower S) (r : ℝ) (x : Points (n+m))
    (v : Fin n → E C.labels i) (w : Fin m → E C.labels d) :
    pair T J r x v w = S.classMoment T (fun _ : Fin (n+m) => max i d) (r • x)
      (Frame.born J r (jointFields v w)) := by
  apply congrArg (S.classMoment T (fun _ : Fin (n+m) => max i d) (r • x))
  funext a
  refine Fin.addCases (fun b => ?_) (fun b => ?_) a <;>
    simp [jointFields, Frame.born]

theorem finite_pair (J : ℝ → PhysMS.tower S) (r : ℝ) (x : Points (n+m))
    (v : Fin n → E C.labels i) (w : Fin m → E C.labels d) (N p : ℕ) :
    pair (StressFlux.Matching.rounded C N p) J r x v w =
      moment (C.beta N p) (observable J r x v w N p) :=
  pair_apply _ J r x v w

end YM.Integration.SignedTreeTensor
