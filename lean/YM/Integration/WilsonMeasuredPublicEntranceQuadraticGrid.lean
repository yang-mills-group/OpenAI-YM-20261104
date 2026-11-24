import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
/-! A finite collection of coordinate and bisector reflections generates all symmetric
+forms on the six two-forms in the original order 01,02,03,12,13,23. The integer
+certificate is evaluated by Lean's kernel. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace YM.Integration.WilsonMeasuredPublicEntranceQuadraticGrid
open Matrix
open scoped BigOperators
abbrev Four:=Fin 4
abbrev Six:=Fin 6
abbrev BasisKey:=Fin 21
abbrev Plane (R:Type):=Matrix Six Six R
def edge:Six→Four×Four:=![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]
def reflection (a b i j:Four):ℤ:=
  if i=a then (if j=b then -1 else 0) else
  if i=b then (if j=a then -1 else 0) else if i=j then 1 else 0
def exterior (a b:Four):Plane ℤ:=fun i j=>
  reflection a b (edge i).1 (edge j).1 * reflection a b (edge i).2 (edge j).2 -
  reflection a b (edge i).1 (edge j).2 * reflection a b (edge i).2 (edge j).1
inductive Word where
  | one
  | ray (a b:Four)
  | pair (x y:Word)
def form:Word→Plane ℤ
  | .one=>1
  | .ray a b=>exterior a b
  | .pair x y=>form x * form y + form y * form x
def words:BasisKey→Word:=
  let w0:=Word.one
  let w1:=Word.ray 3 3
  let w2:=Word.ray 2 2
  let w3:=Word.ray 2 3
  let w4:=Word.ray 1 1
  let w5:=Word.ray 1 3
  let w6:=Word.ray 1 2
  let w7:=Word.ray 0 3
  let w8:=Word.ray 0 2
  let w9:=Word.ray 0 1
  let w10:=Word.pair w1 w2
  let w11:=Word.pair w1 w4
  let w12:=Word.pair w1 w6
  let w13:=Word.pair w1 w8
  let w14:=Word.pair w1 w9
  let w15:=Word.pair w2 w5
  let w16:=Word.pair w2 w7
  let w17:=Word.pair w3 w4
  let w18:=Word.pair w3 w9
  let w19:=Word.pair w5 w8
  let w20:=Word.pair w10 w19
  ![w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20]
def ports:BasisKey→Six×Six:=![(0,0), (1,1), (2,2), (3,3), (4,4), (5,5), (0,1), (0,2), (0,3), (0,4), (0,5), (1,2), (1,3), (1,4), (1,5), (2,3), (2,4), (2,5), (3,4), (3,5), (4,5)]
def cell (k:BasisKey):Plane ℤ:=fun i j=>if (i,j)=ports k ∨ (j,i)=ports k then 1 else 0
def address:Six→Six→BasisKey:=![![0, 6, 7, 8, 9, 10],
    ![6, 1, 11, 12, 13, 14],
    ![7, 11, 2, 15, 16, 17],
    ![8, 12, 15, 3, 18, 19],
    ![9, 13, 16, 18, 4, 20],
    ![10, 14, 17, 19, 20, 5]]
def budget:BasisKey→BasisKey→ℤ:=![![4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 4, 0, 4, 0, 0, 0, 0, 0, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -4, 0, -4, 0, 0, 0, 0, 0, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, -4, 0, 0, -4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, -4, -4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 4, 0, 4, 0, -8, 0, 0, 0, 2, 2, -4, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-4, 4, 0, 0, 4, -8, 0, 0, 0, 0, 0, -2, 0, 0, 0, -4, 0, 0, 0, 0, 0],
    ![4, 4, 0, 0, 4, 0, 0, 0, 8, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 4, 0, 4, 0, 0, 8, 0, 0, -2, -2, 0, 0, 0, 0, 4, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1],
    ![-4, 4, 4, -8, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0],
    ![-4, -4, -4, 0, 0, 0, 0, 0, 0, -8, -2, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0],
    ![16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 0, 8, 4, -1],
    ![0, 0, 4, 0, 4, 0, 0, 8, 0, 0, 2, 2, 0, 0, 0, 0, -4, 0, 0, 0, 0],
    ![-8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, -4, 1],
    ![4, -4, -4, 0, 0, 0, 0, 0, 0, -8, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0],
    ![4, -4, 0, 0, -4, 0, 0, 0, -8, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0],
    ![4, 4, 4, -8, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0],
    ![-4, -4, 0, 0, -4, 8, 0, 0, 0, 0, 0, -2, 0, 0, 0, -4, 0, 0, 0, 0, 0],
    ![0, 0, 4, 0, 4, 0, -8, 0, 0, 0, -2, -2, 4, 0, 0, 0, 0, 0, 0, 0, 0]]
theorem covers:∀i j:Six,(ports (address i j)=(i,j) ∨ ports (address i j)=(j,i)):=by decide
theorem located:∀(k:BasisKey)(i j:Six),cell k i j=if k=address i j then 1 else 0:=by decide
private def printed:BasisKey→Plane ℤ:=![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]],
    ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, -1]],
    ![![1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, -1]],
    ![![1, 0, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0], ![0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0], ![0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, -1]],
    ![![-1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, 1]],
    ![![0, 0, -1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, -1, 0], ![0, 0, 0, 1, 0, 0]],
    ![![0, -1, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, -1, 0]],
    ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, -1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]],
    ![![0, 0, 0, 1, 0, 0], ![0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, -1], ![1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, -1, 0, 0, 0]],
    ![![-1, 0, 0, 0, 0, 0], ![0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, -1, 0], ![0, -1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, 0, 1]],
    ![![2, 0, 0, 0, 0, 0], ![0, -2, 0, 0, 0, 0], ![0, 0, -2, 0, 0, 0], ![0, 0, 0, -2, 0, 0], ![0, 0, 0, 0, -2, 0], ![0, 0, 0, 0, 0, 2]],
    ![![-2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, -2, 0, 0, 0], ![0, 0, 0, -2, 0, 0], ![0, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 0, -2]],
    ![![0, -2, 0, 0, 0, 0], ![-2, 0, 0, 0, 0, 0], ![0, 0, -2, 0, 0, 0], ![0, 0, 0, -2, 0, 0], ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 2, 0]],
    ![![0, 0, 0, 2, 0, 0], ![0, -2, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 2], ![2, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -2, 0], ![0, 0, 2, 0, 0, 0]],
    ![![-2, 0, 0, 0, 0, 0], ![0, 0, 0, -2, 0, 0], ![0, 0, 0, 0, 2, 0], ![0, -2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 0, -2]],
    ![![0, 0, -2, 0, 0, 0], ![0, -2, 0, 0, 0, 0], ![-2, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, -2], ![0, 0, 0, 0, -2, 0], ![0, 0, 0, -2, 0, 0]],
    ![![0, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 0, -2], ![0, 0, -2, 0, 0, 0], ![0, 0, 0, -2, 0, 0], ![2, 0, 0, 0, 0, 0], ![0, -2, 0, 0, 0, 0]],
    ![![-2, 0, 0, 0, 0, 0], ![0, 0, -2, 0, 0, 0], ![0, -2, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, -2]],
    ![![-2, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 0, -2]],
    ![![0, 0, 0, 0, 0, 2], ![0, -2, 0, 0, 0, 0], ![0, 0, 0, -2, 0, 0], ![0, 0, -2, 0, 0, 0], ![0, 0, 0, 0, -2, 0], ![2, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 8], ![0, 8, 0, 0, 0, 0], ![0, 0, 0, 8, 0, 0], ![0, 0, 8, 0, 0, 0], ![0, 0, 0, 0, 8, 0], ![8, 0, 0, 0, 0, 0]]]
private theorem checked:∀(k:BasisKey)(i j:Six),printed k i j=form (words k) i j:=by decide
private theorem balance:∀(k:BasisKey)(i j:Six),∑t:BasisKey,budget k t*printed t i j=16*cell k i j:=by decide
theorem exactRows (k:BasisKey)(i j:Six):
    ∑t:BasisKey,budget k t*form (words t) i j=16*cell k i j:=by
  simpa only [←checked] using balance k i j
end YM.Integration.WilsonMeasuredPublicEntranceQuadraticGrid

