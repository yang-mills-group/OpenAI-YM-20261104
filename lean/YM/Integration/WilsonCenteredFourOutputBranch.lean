import YM.Integration.WilsonCenteredFourOutputDeposit
import YM.Integration.WilsonCenteredNestedPairChord

/-! The positive coordinate inside the complete two-fork ordinary chord.
Subtract the other deposited subwords before any absolute value. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourOutputBranch
open Function Set Filter MeasureTheory Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader
open OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Atom OPE.Prescription OPE.Log RG17
open WilsonCenteredNestedRawPair WilsonCenteredNestedTwoVertex WilsonCenteredNestedPairChord
open WilsonCenteredFourOutputSensor
open scoped Classical BigOperators Topology
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
  (F:Final C f S) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def tip {D:ℕ} (included:4≤D) (c:Q.channels 4) : Menu.Cut Q D := ⟨⟨4,by omega⟩,c⟩
def tags (a:Fin 2→S.Field 4) (i:Fin 2) : S.Tag:=⟨4,a i⟩

def others {D:ℕ} (included:4≤D) (c:Q.channels 4) (m:ℕ) (out:Q.channels m)
    (v:Fin 2→S.Tag) (far:S.Tag) (x y:Fin 2→E4) (o:E4) : ℂ :=
  ∑ t ∈Finset.univ.erase (tip F Q included c),
    express Q t.1 t.2 x v (y 0) * express Q m out y (placed F Q t far) o

theorem retained {D:ℕ} (included:4≤D) (c:Q.channels 4) (m:ℕ) (out:Q.channels m)
    (v:Fin 2→S.Tag) (far:S.Tag) (x y:Fin 2→E4) (o:E4) :
    held F Q D m out v far x y o - others F Q included c m out v far x y o =
      express Q 4 c x v (y 0)*express Q m out y (placed F Q (tip F Q included c) far) o:=by
  unfold held others
  have split:=Finset.sum_erase_add (s:=Finset.univ) (a:=tip F Q included c)
    (fun t:Menu.Cut Q D=>express Q t.1 t.2 x v (y 0)*express Q m out y (placed F Q t far) o) (Finset.mem_univ _)
  rw [←split]
  abel

theorem chord {D:ℕ} (included:4≤D) (c:Q.channels 4) (m:ℕ) (out:Q.channels m)
    (v:full.Leaf→S.Tag) (z:full.Plot) :
    Kernel.chord F Q z v out (caps m D) -
      others F Q included c m out (near v) (other v) (skyline (childPlace 0 z)) (skyline z) (anchor z) =
      express Q 4 c (skyline (childPlace 0 z)) (near v) (skyline z 0)*
        express Q m out (skyline z) (placed F Q (tip F Q included c) (other v)) (anchor z):=by
  rw [←WilsonCenteredNestedPairChord.chord F Q m D out z v]
  exact retained F Q included c m out .. 

def heard {D:ℕ} (included:4≤D) (c:Q.channels 4) (m:ℕ) (out:Q.channels m)
    (a:Fin 2→S.Field 4) (far:S.Tag) (r:ℝ) (ψ:Test 2) (y:Fin 2→E4) (o:E4):ℂ :=
  ∫x:Points 2, ψ x * (held F Q D m out (tags a) far (posed r x) y o -
    others F Q included c m out (tags a) far (posed r x) y o)

theorem deposited {D:ℕ} (included:4≤D) (c:Q.channels 4) (m:ℕ) (out:Q.channels m)
    (a:Fin 2→S.Field 4) (far:S.Tag) (r:ℝ) (ψ:Test 2) (y:Fin 2→E4) (o:E4) (center:y 0=0) :
    heard F Q included c m out a far r ψ y o =
      (∫x:Points 2,ψ x*Q.coef 4 c (d:=fun _:Fin 2=>4) (posed r x) a 0)*
        express Q m out y (placed F Q (tip F Q included c) far) o:=by
  unfold heard
  simp_rw [retained,center,←mul_assoc]
  rw [integral_mul_const]
  rfl

theorem original (fac:Services C f S) {K:Set (Points 2)} (compact:IsCompact K) (away:K⊆conf 2):
    ∀ᶠ r in RG17.home,∀ {D:ℕ} (included:4≤D) (c:Q.channels 4) (m:ℕ) (out:Q.channels m)
      (a:Fin 2→S.Field 4) (far:S.Tag) (ψ:Test 2),tsupport ψ⊆K → ∀ (y:Fin 2→E4) (o:E4),y 0=0 →
      heard F Q included c m out a far r ψ y o = grade F Q c (RG17.basket Q 4 (d:=fun _:Fin 2=>4) a r ψ)*
        express Q m out y (placed F Q (tip F Q included c) far) o:=by
  filter_upwards [WilsonCenteredFourOutputDeposit.original F Q fac compact away] with r all D included c m out a far ψ sub y o center
  rw [deposited F Q included c m out a far r ψ y o center,all a c ψ sub]

end YM.Integration.WilsonCenteredFourOutputBranch
