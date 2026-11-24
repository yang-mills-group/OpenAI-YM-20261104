import YM.Integration.WilsonPhysicalMeasuredLowerSolve

/-! An actual reflected two-point receiver at its own reported position. A source raised from a
lower physical field gives exactly its own lower-height reading there. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationLowerReceiver
open Function Set Filter Finset Lattice Wilson RG Source Cells
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalBlissMixedGram (grades)
open WilsonOriginalPublicRelativeGramAddresses (ports)
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt)
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→PhysMS.tower S)(B:Deck G)(e:ℕ)(a:Axis)(avoid:Finset E4)

def pair {e h:ℕ}(u:S.Field e)(z:S.Field h):(i:Fin 2)→S.Field (grades e h i):=
  Fin.cons (α:=fun i=>S.Field (grades e h i)) u (fun _=>z)

def ear {e h:ℕ}(x:Points 2)(z:S.Field h):S.Field e→ₗ[ℂ]ℂ:=
  (S.classMoment S (grades e h) x).toLinearMap (pair R (S:=S) (0:S.Field e) z) (0:Fin 2)

theorem evaluated {e h:ℕ}(x:Points 2)(z:S.Field h)(w:S.Field e):
    ear R (S:=S) x z w=S.classMoment S (grades e h) x (pair R w z):=by
  change S.classMoment S (grades e h) x (Function.update (pair R (0:S.Field e) z) (0:Fin 2) w)=_
  congr 1
  funext i
  fin_cases i <;> simp [pair,Function.update]

theorem raised {e h d:ℕ}(le:e≤h)(x:Points 2)(clear:x∈conf 2)(z:S.Field d):
    (ear R (S:=S) (e:=h) x z).comp (F.sector.derivatives.rise le)=ear R x z:=by
  apply LinearMap.ext
  intro u
  change ear R x z (F.sector.derivatives.rise le u)=ear R x z u
  simp only [evaluated]
  let other:Fin 2→S.Tag:=fun _=>⟨d,z⟩
  have tags (l:ℕ)(v:S.Field l):
      Function.update other (0:Fin 2) ⟨l,v⟩=fun i=>⟨grades l d i,pair R v z i⟩:=by
    funext i
    fin_cases i <;> simp [other,Function.update,grades,pair] <;> rfl
  have low:=F.sector.derivatives.inclusion_slot F.phase.transport.injection F.room.kernel.laws.toSymmetric
    le clear (0:Fin 2) other u
  rw [tags,tags] at low
  exact low

def point (m:ℕ)(r:ℝ):Points 2:=Extraction.Order.grid R.family m (ports R avoid (pointsAt a) m r)
def pivot (r:ℝ)(i:Glyph B e):S.Field e:=S.adj F.room.kernel.spin e a (J r e (named R B e i))
def peer (r:ℝ)(m:ℕ)(j:Glyph B e):S.Field e→ₗ[ℂ]ℂ:=
  ear R (point R a avoid m r) (J r e (named R B e j))
def gram (r:ℝ)(m:ℕ):Matrix (Glyph B e) (Glyph B e) ℂ:=
  fun i j=>peer R (S:=S) J B e a avoid r m j (pivot R F J B e a r i)

/-- These actual reflected original sources determine every complex-linear functional
on the whole lower field, including its scalar. -/
theorem complete (r:ℝ)(L M:S.Field e→ₗ[ℂ]ℂ)
    (same:∀i:Glyph B e,L (pivot R F J B e a r i)=M (pivot R F J B e a r i)):
    L=M:=by
  let E:Module.Basis (Glyph B e) ℂ (S.Field e):=(named R B e).map (J r e)
  let A:=S.adj F.room.kernel.spin e a
  have signed:L.comp A=M.comp A:=E.ext fun i=>same i
  apply LinearMap.ext
  intro X
  have atX:=DFunLike.congr_fun signed (A X)
  simpa only [LinearMap.comp_apply,A,Table.reflect_twice] using atX

end YM.Integration.WilsonPhysicalStationLowerReceiver
end
