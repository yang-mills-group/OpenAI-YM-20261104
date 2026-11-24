import YM.RG17.Cord
import YM.Integration.WilsonThermometerUnitFilingFourSquare

/-! The full source, including its exterior, is measured on the same selected Wilson
law before the ultraviolet and physical volume limits. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicForkPooledHearing
open Function Filter Set MeasureTheory Extraction Table Spec OPE OPE.Orbits RG17
open Lattice Cells Wilson Next.Rank WilsonThermometerUnitFilingFourSquare
open scoped Classical Topology BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {l:Filter (ℕ×ℕ)}[l.NeBot](order:l≤f.fuse){n:ℕ}

include F order

def markedCut (v:Fin n→S.Tag)(arms:∀i,Arm C S l (v i).1 (v i).2)(φ:Test n)(z:ℕ×ℕ):ℂ:=
  Order.smears C z.1 z.2 (fun i=>⟨(v i).1,(arms i).source z⟩) φ

theorem product (v:Fin n→S.Tag)(arms:∀i,Arm C S l (v i).1 (v i).2)(φ:Test n):
    Tendsto (markedCut v arms φ) l (𝓝 (φ.applyTo fun x=>S.useAt S x v)):=by
  exact WilsonThermometerUnitFilingFourSquare.measured F order (fun i _=>arms i) (fun _=>false) φ

theorem whole {d:Caps n}(v:Labels S d)(X:External C S){r:ℝ}(rp:0<r)(ψ:Test n)
    (covered:packs X r ψ)(income:Integrable (fun z:Points (X.n+1)=>X.test z*query F v (X.offset z) X.labels none r ψ))
    (arms:∀i,Arm C S l ((Fin.append (tags v) X.tags) i).1 ((Fin.append (tags v) X.tags) i).2):
    Tendsto (markedCut (Fin.append (tags v) X.tags) arms (shape X r ψ)) l (𝓝 (appeared F v X r ψ)):=by
  rw [←chargedShape X v ψ rp covered income]
  exact product F order (Fin.append (tags v) X.tags) arms (shape X r ψ)

theorem gram {h:ℕ}(v:S.Field h)(X:External C S)
    (arms:∀i,Arm C S l ((Fin.cons (α:=fun _=>S.Tag) ⟨h,v⟩ X.tags) i).1 ((Fin.cons (α:=fun _=>S.Tag) ⟨h,v⟩ X.tags) i).2):
    Tendsto (markedCut (Fin.cons (α:=fun _=>S.Tag) ⟨h,v⟩ X.tags) arms X.test) l (𝓝 (X.charge F h v)):=by
  have read:=product F order (Fin.cons (α:=fun _=>S.Tag) ⟨h,v⟩ X.tags) arms X.test
  have same:X.charge F h v=X.test.applyTo (fun x=>S.useAt S x (Fin.cons (α:=fun _=>S.Tag) ⟨h,v⟩ X.tags)):=by
    change X.test.applyTo (X.pay h v)=_
    apply X.test.apply_eq;intro x hx;exact X.pay_eq F h v x hx
  rwa [same]

end YM.Integration.WilsonPublicForkPooledHearing
