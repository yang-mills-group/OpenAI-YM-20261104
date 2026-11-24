import YM.FVA2.BilledField
import YM.FVAAlt2.Rocket.Export

/-! The inverse Wick matrix of the prescribed boxed field, read in exactly
the run's local frame. The genuine lower slot terms keep their own ranks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRichPrimitiveRows
open Function Finset Lattice Wilson Labels PertExtension PertExtension.LatticePT
open Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Bare.Shop PositionX.Bare.Subcell
open RG PhysicalNext.Repeat.Legato MS MS.Koszul MS.Theater MS.Book MS.Book.Program MS.Book.Convolve
open MS.Land MS.Menus FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open FormalOPE.RG10.MultiGauge FormalOPE.RG10.InversionTop FVA2 FVAAlt2
open FVA2.Clock FVA2.Score FVA2.Based FVA2.PairCoords FVA2.Modes FVA2.Paper FVA2.Trans FVA2.ColorCode FVA2.Attend
open RegulatorIR.FVAAlt2.Lodge
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)
local notation "Reg" => basisR R

def warehouse : Warehouse G where
  F := R.family.labels
  H := R.family.params
  S := R.family.localSection
  h := R.makes.sections
  acts := Block.clothes R

variable {B : MS.Local.Physical.Deck G} (v : MS.Rake.Label B)
local notation "F" => R.family.labels.level v.h
local notation "S" => R.family.localSection v.h
local notation "W" => warehouse R

/-- Original rank-by-rank Wick inverse, including its lower ranks. -/
theorem inverse :
    ((topMatrix S R.family.params (R.makes.sections _) (Block.clothes R v.h)).inverse
      (covarianceSymbol G)) ((F).coords (Shop.seat B v.item.2)) = Lobby.γ Reg v := by
  let c := (F).coords (Shop.seat B v.item.2)
  have hc : c = ∑ i, c i • (Pi.single i 1 : (F).Coeff) := by
    funext j
    symm
    simp only [Finset.sum_apply]
    simp [Pi.single_apply,mul_ite]
  change ((topMatrix S R.family.params (R.makes.sections _) (Block.clothes R v.h)).inverse
    (covarianceSymbol G)) c = _
  funext j
  rw [hc,map_sum,Finset.sum_apply]
  unfold Lobby.γ Shop.valueP
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul,Pi.smul_apply,Vertex.true_coefficients]
  rfl

theorem price (i : (F).Index) :
    (↑((W).prices B v.h v.item.1 v.item.2 i) : ℂ) = Lobby.γ Reg v i := by
  rw [Warehouse.price_cast]
  exact congrFun (inverse R v) i

theorem material {n : Side} (x : Site n) (i : (F).Index) :
    FVA2.Source.put (Plate.bare S i) x = Lobby.poster Reg v x i :=
  Plate.bare_put S i x

theorem physical {n : Side} (x : Site n) (i : (F).Index) (U : Config G n) :
    (↑(Lobby.poster Reg v x i U) : ℂ) = (S).places (Pi.single i 1) x U :=
  PertExtension.Orb.SlotEvaluation.scalar_real (R.makes.sections _)

theorem rank (i : (F).Index) (h : Lobby.γ Reg v i ≠ 0) :
    ((F).grades i).2 ≤ v.item.1 := by
  by_contra! hn
  change Shop.valueP B S (R.makes.sections _) (Block.clothes R v.h) v.item.2 i ≠ 0 at h
  rw [Shop.current_p _ _ _ _ _ _ hn.le,Shop.cancel B i v.item.2] at h
  · exact h rfl
  · exact fun he => hn.ne' (congrArg Prod.snd he)

/-- In the original declared rank, the lower ranks funded by the Wick
inverse occur with their actual positive coupling powers. -/
def incoming {n : Side} (g : ℝ) (x : Site n) (U : Config G n) : ℂ :=
  ∑ i : (F).Index,Lobby.γ Reg v i * (g:ℂ)^(v.item.1-((F).grades i).2) * Lobby.poster Reg v x i U

theorem scale {n : Side} {g : ℝ} (hg : g ≠ 0) (x : Site n) (U : Config G n) :
    ((g:ℂ)^v.item.1.val)⁻¹ * incoming R v g x U =
      ∑ i : (F).Index,(↑((W).prices B v.h v.item.1 v.item.2 i) : ℂ) *
        ((g:ℂ)^((F).grades i).2)⁻¹ * (S).places (Pi.single i 1) x U := by
  unfold incoming
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [price R v i,physical R v x i U]
  by_cases h : Lobby.γ Reg v i = 0
  · simp [h]
  have he : (g:ℂ)^v.item.1.val = (g:ℂ)^(v.item.1-((F).grades i).2) * (g:ℂ)^((F).grades i).2 := by
    rw [←pow_add,Nat.sub_add_cancel (rank R v i h)]
  rw [he,mul_inv_rev]
  field_simp [Complex.ofReal_ne_zero.mpr hg]

variable {ι J : Type} {n : Side} (b : Module.Basis ι ℝ (Wilson.Field G n))
  (x : Site n) (e : ℝ)
local notation "embed" => Boson.sharp (bell (J:=J) b) FVA2.PairCoords.φ (bell_even b)

/-- Exact engineering-normalized BoxOffice readout on the very same physical
section, without identifying distinct choices of physical deck. -/
theorem ordinary :
    BoxOffice.ordinary (J:=J) b x e v.h F S R.family.params (R.makes.sections v.h)
        (Block.clothes R v.h) (Shop.seat B v.item.2) =
      ((e:ℂ)^v.h)⁻¹ • ∑ i : (F).Index, Lobby.γ Reg v i •
        embed (FVA2.Source.seated x ((F).grades i).2 (Plate.bare S i)) := by
  unfold BoxOffice.ordinary
  rw [LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact congrArg (fun z : ℂ => z • embed (FVA2.Source.seated x ((F).grades i).2 (Plate.bare S i)))
    (congrFun (inverse R v) i)

end YM.Integration.WilsonRichPrimitiveRows

