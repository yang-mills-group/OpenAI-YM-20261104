import YM.Integration.WilsonRichPrimitiveRows
import YM.Integration.ActualRunStartupInput

/-! Exact boxed field of every actual factory label, including the terminal
inverse, both physical scales, and the input's engineering factor. The
classical boxed label is computed from the true coefficient matrix. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFactoryBoxedFields
open Function Finset Lattice Wilson Labels PertExtension PertExtension.LatticePT
open Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Bare.Shop PositionX.Bare.Subcell
open RG PhysicalNext.Repeat.Legato MS MS.Koszul MS.Theater MS.Book MS.Book.Program MS.Book.Convolve
open MS.Land MS.Menus FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open FormalOPE.RG10.MultiGauge FormalOPE.RG10.InversionTop FVA2 FVAAlt2
open FVA2.Clock FVA2.Score FVA2.Based FVA2.PairCoords FVA2.Modes FVA2.Paper FVA2.Trans FVA2.ColorCode FVA2.Attend
open RegulatorIR.FVAAlt2.Lodge Extra.Histories
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (d : ℕ)
local notation "F" => R.family.labels.level d
local notation "S" => R.family.localSection d
local notation "T" => topMatrix S R.family.params (R.makes.sections d) (Block.clothes R d)

/-- Genuine inverse of the boxed coefficient map, on its whole domain. -/
def label (c : (F).Coeff) : Labels.Label G d :=
  (F).coords.symm (((T).conversion (covarianceSymbol G)) c)

theorem recoiled (c : (F).Coeff) : (T).inverse (covarianceSymbol G) ((F).coords (label R d c)) = c := by
  unfold label
  rw [LinearEquiv.apply_symm_apply]
  exact (T).conversion (covarianceSymbol G) |>.symm_apply_apply c

variable {ι J : Type} {n : Side} (b : Module.Basis ι ℝ (Wilson.Field G n)) (o : Site n) (e : ℝ)
local notation "sharp" => Boson.sharp (bell (J:=J) b) FVA2.PairCoords.φ (bell_even b)

theorem boxed (c : (F).Coeff) :
    BoxOffice.ordinary (J:=J) b o e d F S R.family.params (R.makes.sections d) (Block.clothes R d) (label R d c) =
    ((e:ℂ)^d)⁻¹ • ∑ j : (F).Index,c j • sharp (FVA2.Source.seated o ((F).grades j).2 (Plate.bare S j)) := by
  unfold BoxOffice.ordinary
  rw [LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.sum_apply]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => congrArg
    (fun u : ℂ => u • sharp (FVA2.Source.seated o ((F).grades j).2 (Plate.bare S j)))
    (congrFun (recoiled R d c) j))

variable (N per : ℕ) (v : R.family.label d)
local notation "θ₁" => R.family.path.levels.clock.threshold N
local notation "n₁" => R.family.side N per

/-- Coefficient of the genuine Laurent-normalized primitive, before its
common a_N^(-d). It retains the real terminal inverse of the marked factory. -/
def restored (g : ℝ) : (F).Coeff :=
  (F).scaled (g / θ₁) ((R.family.factory d N per).terminal.symm v)

/-- The common original physical section seen by each finite mark. -/
def bareRead (j : (F).Index) (x : Site n₁) (U : Config G n₁) : ℂ :=
  (S).places (Size.axis F j) x U

def word (g : ℝ) (x : Site n₁) (U : Config G n₁) : ℂ :=
  ∑ j : (F).Index,restored R d N per v g j * ((g:ℂ)^((F).grades j).2)⁻¹ *
    bareRead R d N per j x U

theorem field {g : ℝ} (hg : g≠0) (x : Site n₁) (U : Config G n₁) :
    R.family.O N per v x U = ((R.family.S.a N:ℂ)^d)⁻¹ * word R d N per v g x U := by
  change ((R.family.S.a N:ℂ)^d)⁻¹ * (S).places
    ((F).scaled θ₁⁻¹ ((R.family.factory d N per).terminal.symm v)) x U = _
  rw [HorizonPhysicalFields.section_expansion]
  unfold word
  apply congrArg (fun u : ℂ => ((R.family.S.a N:ℂ)^d)⁻¹ * u)
  apply Finset.sum_congr rfl
  intro j _
  unfold bareRead restored
  simp only [Frame.scaled,LinearMap.coe_mk,AddHom.coe_mk,Complex.ofReal_pow,Complex.ofReal_inv,
    Complex.ofReal_div,div_pow,inv_pow]
  field_simp [Complex.ofReal_ne_zero.mpr hg]

/-- Positive native vacuum left completely in place for each incoming
density; signed insertions are restored without guessing an output height. -/
theorem top {g : ℝ} (hg : g≠0) (deep : R.family.ref d ≤ N) (U : Config G n₁) :
    ((R.family.factory d N per).entries N ((R.family.factory d N per).terminal.symm v)).density 0 S
      (R.family.path.rep N per N) U =
      (Wilson.bare (R.family.beta N per) U : ℂ) * word R d N per v g 0 U := by
  rw [ActualRunStartupInput.inserted_density R d N per v deep U,field R d N per v hg]
  have h := pow_ne_zero d (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos N).ne')
  field_simp [h]

end YM.Integration.WilsonFactoryBoxedFields
