import YM.Integration.ActualRunCurvaturePackets
import YM.Integration.ActualStencilProjection

/-! Every original section column has a nonzero signed averaged color coefficient in its actual finite path presentation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedOPEColumn
open Function Finset Lattice Wilson RG Source Labels PertExtension
open PhysicalNext.Repeat.Legato ActualRunCurvaturePackets ActualStencilCylinder ActualStencilProjection
open NativeCurvatureTensor Push.CutoffProjectors PertExtension.Series
open private cover_basis from YM.Integration.ActualRunCurvaturePackets
open scoped BigOperators Classical ContDiff

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d} {S : SectionData F}

theorem echo {c : F.Coeff} (vanishes : ∀U : CoverConfig G,S.evaluate c U=0) :
    realEcho S c=0 := by
  funext A
  let wide : Links ℤ G.Color := fun e=>if h : e.1∈S.stencil ∧e.1+step e.2∈S.stencil then A ⟨e,h⟩ else 0
  have restricted : Dict06.Wil.restrictLog S.stencil wide=A := by
    funext i
    exact dif_pos i.property
  have original := Dict06.Wil.echo_exact S c wide 1
  rw [one_smul,restricted,vanishes] at original
  exact congrArg Complex.re original.symm

theorem visible {H : Hol G} (sound : S.Sound H) (rank : Bid.pop S) (i : F.Index) :
    ∃U : CoverConfig G,S.evaluate (Pi.single i 1) U≠0 := by
  by_contra! empty
  have echo₀ := echo empty
  have term (J : Lens G d) (r : ℝ) (j : F.Index) :
      ((Pi.single i 1 : F.Coeff) j)*(Radial.jet (realEcho S (Pi.single j 1)) (F.grades j).2
        (Dict06.Wil.restrictLog S.stencil (RG06.Section.chordLine (d:=d) J.1 r)) : ℂ)=0 := by
    by_cases same : j=i
    · subst j
      simp [echo₀,Radial.jet]
    · simp [Pi.single_eq_of_ne same]
  have profile₀ : profile S (Pi.single i 1)=profile S 0 := by
    funext J
    unfold profile
    simp only [term,Pi.zero_apply,zero_mul]
  have paid := coordinate_restore S sound rank (Pi.single i 1)
  rw [profile₀,coordinate_restore S sound rank 0] at paid
  have impossible := congrFun paid i
  simp at impossible

theorem occupied (D : Presentation S) {H : Hol G} (sound : S.Sound H) (rank : Bid.pop S) (i : F.Index) :
    ∃ m : ↥(D.data.shape i).support,∃ j : Fin (m.val.sum fun _ k=>k)→G.ColorIndex,
      coefficient (fun k=>(word m.val k).2) j≠0 := by
  obtain ⟨U,nonzero⟩ := visible sound rank i
  by_contra! empty
  apply nonzero
  rw [cover_basis D i U]
  apply Finset.sum_eq_zero
  intro m hm
  have vanishes : ∀ j, coefficient (fun k=>(word m k).2) j=0 := empty ⟨m,hm⟩
  simp [value,vanishes]

end YM.Integration.WilsonRootedOPEColumn
