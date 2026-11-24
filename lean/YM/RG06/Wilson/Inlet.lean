import YM.RG06.Wilson.Voice
import YM.PertExtension.TopJet

/-!
# Joint `h`-jet read of the leading `g` coefficient of the Wilson stencil

Precisely the unsmeared input through its announced horizon at top, before Wick
subtractions/basis transforms. There is no interacting-table read here. Use
accepted projection through finite horizons; do not infer an all-h analytic
identity at nonzero h. Retain total derivatives within labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.WilsonCompiler
open GSeries Function Gauge Exterior Source Source.Drops PertExtension.Heat
open Lattice RG Bid Wilson Labels
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {d m : ℕ}


abbrev input (J : Jet G) (d : ℕ) (r : ℝ) := access G (Drops.access (trunk d (Source.scaleJet J r)))

def leadingPose (b : Fin m → Slot) (P : Pose G m) (l : ℕ) (J : Jet G) (d : ℕ) (r : ℝ) :=
  Top.symbolEval (d:=d) (Top.rawPart b P l) J r

lemma solo_integral (s : Slot) (k : G.ColorIndex) (J : Jet G) (d : ℕ) (r : ℝ) :
    tone (input J d r) (solo (0:Cover) s k) = (glow (trunk d (scaleJet J r)) s k : ℂ) := by rw [solo_eval]; rfl

lemma lead_integral (B : Fin m→Slot) (P : Pose G m) (l : ℕ) (J : Jet G) (d : ℕ) (r : ℝ) :
    tone (input J d r) (shiftedLead P (0:Cover) l B) = leadingPose B P l J d r := by
  unfold leadingPose Top.symbolEval Top.rawPart shiftedLead
  rw [MvPolynomial.aeval_rename]
  -- twice-polynomial map
  let z := tone (input J d r)
  let f (i : Fin m×G.ColorIndex) : Pigment (LinkVar G ℤ) := solo (0:Cover) (B i.1) i.2
  let g (i : Fin m×G.ColorIndex) := (glow (trunk d (scaleJet J r)) (B i.1) i.2 : ℂ)
  have e (P : MvPolynomial (Fin m×G.ColorIndex) ℂ) :
      z (MvPolynomial.eval₂Hom MvPolynomial.C f P)=MvPolynomial.aeval g P := by
    induction P using MvPolynomial.induction_on with
    | C a=> rw [MvPolynomial.eval₂Hom_C,MvPolynomial.aeval_C,tone_C]; rfl
    | add p q hp hq=> rw [map_add,map_add,hp,hq,map_add]
    | mul_X p i hp=> rw [map_mul,map_mul,hp,map_mul,MvPolynomial.eval₂Hom_X',MvPolynomial.aeval_X, solo_integral]
  exact e _

theorem base_integral (B : Fin m → Slot) (P : Pose G m) (l : ℕ) (hp : lows P l) (d : ℕ) (J : Jet G) (r : ℝ) :
    tone (input J d r) (PowerSeries.constantCoeff (voice l (frameFilm P B (0:Cover) (basic G ℤ)))) = leadingPose B P l J d r := by
  rw [free_leading P l hp]; exact lead_integral ..

/-- Each announced basis letter of the **actual** section stencil has the
asserted classical joint-weight jets on its leading homogeneous-in-A coefficient,
with the factor `1/a!` implicit on both sides if passing to Taylor coefficients.
The two order parameters (h-jets and slot division in g) are not interchanged on
the actual RG density. -/
theorem reads_inlet (C : Family G) (h : C.Makes) (H : Bid.pop (C.localSection d))
    (i : (C.labels.level d).Index) (J : Jet G) (k : ℕ) (hk : k≤d) :
    iteratedDeriv k (fun r : ℝ => tone (input J d r)
      (PowerSeries.constantCoeff (voice ((C.labels.level d).grades i).2
        (markTop C d (Pi.single i 1))))) 0 =
      iteratedDeriv k (fun r : ℝ => Labels.read (Source.scaleJet J r) ((C.labels.level d).basis i).val) 0 := by
  let F := C.labels.level d
  let p := (C.localSection d).evalC (Pi.single i 1)
  obtain ⟨m,B,-,P,e,l⟩ := H i
  have hg : markTop C d (Pi.single i 1)= frameFilm P B (0:Cover) (basic G ℤ) := formula_cover_eq p P B (fun U=> congrFun e U)
  let A : Push.CutoffProjectors.Lens G d := (J,⟨k,Nat.lt_succ_of_le hk⟩)
  have hp : Projects C.params (F.basis i) (lumin P ∘ mapped B) := by
    rw [← e, ← F.coords_basis]; have hv := (h.sections d).projects (F.coords (F.basis i)); rwa [LinearEquiv.symm_apply_apply] at hv
  simp_rw [hg,base_integral _ _ _ l]
  have hw:= Top.leading_correct i P B l hp A
  rw [Push.CutoffProjectors.probe_eq, ← F.coords_basis i, LinearEquiv.symm_apply_apply] at hw
  exact hw
end YM.RG06.WilsonCompiler
