import YM.Integration.WilsonOriginalPrimerInk

/-! The pole-cleared Wilson teacher uses a particular original root.
This is the corresponding full independently filed finite source, with
the physical origin carried through every angular slot. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPlacedPrimerInk
open Function Finset Lattice Laurent RG Wilson FormalBulk08
open FormalBulk08.Mesa FormalBulk08.Orb FormalBulk08.Reef FormalBulk08.Kemp
open FormalBulk08.Lotus Stationary WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}
def offset (o:Site n)(i:Woods G n):Woods G n:=(o+i.1,i.2)
def place (o:Site n):Matrix (Woods G n) (Woods G n) ℝ:=fun i j=>
  if offset o i=j then 1 else 0

def filed (d:ℕ)(T:Pot G)(n:Side)(o:Site n):PChart G n:=
  fun e=>fade (place o) (WilsonOriginalPrimerInk.column d T n e)

theorem shelf (d:ℕ)(T:Pot G)(n:Side)(o:Site n):shellK d (filed d T n o):=by
  intro e r hr
  funext x
  simp [filed,fade,WilsonOriginalPrimerInk.span d T n e r hr]

theorem pure (d:ℕ)(T:Pot G)(n:Side)(o:Site n)(e:ℕ):Pure (filed d T n o e):=
  fade_pure (WilsonOriginalPrimerInk.symmetric d T n e) _

private theorem basis (o:Site n) : cord (place (G:=G) o)=MvPolynomial.rename (R:=ℝ) (offset o):=by
  apply MvPolynomial.algHom_ext
  intro i
  rw [cord_var,MvPolynomial.rename_X]
  simp [place]

theorem origin (d:ℕ)(T:Pot G)(n:Side)(o:Site n):
    Blue.flash (filed d T n o)=PowerSeries.map (MvPolynomial.rename (R:=ℝ) (offset (G:=G) o)).toRingHom (Kemp.banner d T n):=by
  rw [←WilsonOriginalPrimerInk.original d T n]
  apply PowerSeries.ext
  intro e
  rw [Blue.flash,coeff_mk,coeff_map,Blue.flash,coeff_mk]
  apply Eq.trans (fade_visible (place o) (WilsonOriginalPrimerInk.column d T n e)
    ⟨d+e+1,fun r hr=>WilsonOriginalPrimerInk.span d T n e r (by omega)⟩)
  rw [basis]
  rfl

theorem tested (d:ℕ)(T:Pot G)(n:Side)(o:Site n)(e:ℕ)(A:Link G n):
    MvPolynomial.eval A (coeff e (Blue.flash (filed d T n o)))=
    MvPolynomial.eval (fun j:wire G n=>A (o+j.1,j.2)) (coeff e (Kemp.banner d T n)):=by
  rw [origin,coeff_map]
  exact MvPolynomial.eval_rename (offset o) A _

end YM.Integration.WilsonOriginalPlacedPrimerInk
end
