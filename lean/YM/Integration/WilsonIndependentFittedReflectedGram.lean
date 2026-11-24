import YM.Integration.WilsonIndependentFittedDirectoryNode
import YM.Integration.WilsonOriginalPublicPlantedGramFilms

/-! The two numerical coefficients in the reflected Gram are the same fitted vector and its adjoint. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentFittedReflectedGram
open Finset Lattice Maxwell XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register
open MS MS.Land MS.Menus MS.Theater Local.Physical PowerSeries
open WilsonIndependentFittedNumericalProduct (numerical fitted pivot gross)
open WilsonOriginalPublicPlantedGramFilms (reflected pupil)
open WilsonOriginalPublicPlantedGram (measured)
open WilsonPositionProgramPublicContrast (assay)
open WilsonPositionProgramPublicReflectedRead (signed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped BigOperators Classical
variable {I:Type}[Fintype I]{G:Gauge}{β:Deck G}{d:ℕ}(Z:WilsonPrescription G)(ax:Axis)(leg:I→Glyph β d)
    (j:ℕ)(s:Sample 2)

def fields:Fin 2→I→Bare.Series (Z.scheme.tree s.F.p) G:=
  ![fun i=>reflected Z ax j (leg i) s,fun k=>pupil Z j (leg k) s]

def paired (D:I→PowerSeries ℂ):Fin 2→I→PowerSeries ℂ:=
  ![fun i=>PowerSeries.map (starRingEnd ℂ) (D i),D]

private theorem conj (Q:ℕ)(u:ℝ)(f:PowerSeries ℂ):
    cash Q u (PowerSeries.map (starRingEnd ℂ) f)=star (cash Q u f):=by
  simp [cash,PowerSeries.coeff_map]

private def pair: I×I≃(Fin 2→I) where
  toFun z:=![z.1,z.2]
  invFun z:=(z 0,z 1)
  left_inv _:=rfl
  right_inv f:=by funext i;fin_cases i <;>rfl

omit [Fintype I] in
theorem stamped (j:ℕ){B:ℕ}(P:Handoff.Directory Z j B)(s:Sample 2)(i k:I)(q:ℕ)(u:ℝ)
    (board:s.F=Z.run.step j)(cap:Handoff.Directory.budget G 2 d+q≤B):
    cash q u (pivot Z.scheme s (fields Z ax leg j s) ![i,k])=measured Z ax leg q P u s i k:=by
  rw [measured,WilsonOriginalPublicPlantedPivotFields.drawn β Z P s (signed ax leg i k) board q cap u]
  unfold cash pivot
  apply sum_congr rfl
  intro k _
  rw [Fin.prod_univ_two,Fin.prod_univ_two,mul_comm]
  rfl

theorem purchased (j:ℕ){B:ℕ}(P:Handoff.Directory Z j B)(s:Sample 2)(D:I→PowerSeries ℂ)(Q J:ℕ)(u:ℝ)
    (board:s.F=Z.run.step j)(cap:Handoff.Directory.budget G 2 d+J≤B):
    numerical Z.scheme s (fields Z ax leg j s) (paired D) Q J u=
      assay (fun a=>cash Q u (D a)) (fun a=>cash Q u (D a)) (measured Z ax leg J P u s):=by
  let one(a:Fin 2→I):=(∏b,cash Q u (paired D b (a b)))*cash J u (pivot Z.scheme s (fields Z ax leg j s) a)
  calc
    _=∑a:Fin 2→I,one a:=sum_congr (by ext; simp) fun _ _=>rfl
    _=∑b:I×I,one (pair b):=(pair.sum_comp one).symm
    _= _:=by
      rw [Fintype.sum_prod_type]
      unfold assay
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro k _
      dsimp only [one]
      rw [Fin.prod_univ_two]
      change (cash Q u (PowerSeries.map (starRingEnd ℂ) (D i))*cash Q u (D k))*
        cash J u (pivot Z.scheme s (fields Z ax leg j s) ![i,k])=_
      rw [conj,stamped Z ax leg j P s i k J u board cap]

end YM.Integration.WilsonIndependentFittedReflectedGram
