import YM.Integration.WilsonPositionProgramNormalizedMaster
import YM.Integration.WilsonMarkedIndependentMixedIntegratedHistory
import YM.WilsonCoeffUV.Emit.RentedCapture

/-! The native separation gate tests unit-priced fields. Pull a scalar out of
each original slot after its inverse and restore the full ordinary face. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramWindingSlotScale
open Next.Foundations PhysicalNext.Repeat.Legato
open Filter Finset Lattice Wilson RG RG.Supply Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonCoeffUV.Power WilsonCoeffUV.Blue WilsonCoeffUV.Soil Source Source.Drops Labels
open scoped Topology BigOperators Classical
variable {G:Gauge}{a e:ℕ}

theorem residual (Q:Fin (a+1)→SealR G)(X:Herit Q)(w:Fin (a+1)→ℝ)(pos:∀i,0<w i)
    (cap:∀i,WilsonPositionProgramNormalizedMaster.fee X e i≤w i)(i:Fin (a+1)):
    WilsonConditionalTaylorSeparatedPurchase.fee (Q i) (onSlots Q X (fun j=>(w j)⁻¹) i) e≤2:= by
  have inside:∑j:Alma (Q i).F,∑k∈range (e+1),‖PowerSeries.coeff k (X i j)‖≤w i:=by
    apply le_trans _ (cap i)
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro j _
    exact (Fin.sum_univ_eq_sum_range (fun k=>‖PowerSeries.coeff k (X i j)‖) (e+1)).symm
  unfold WilsonConditionalTaylorSeparatedPurchase.fee onSlots
  simp only [Pi.smul_apply,map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (pos i).le)]
  simp_rw [←Finset.mul_sum]
  have small:=mul_le_mul_of_nonneg_left inside (inv_nonneg.mpr (pos i).le)
  rw [inv_mul_cancel₀ (pos i).ne'] at small
  linarith

theorem moved (L:Levels G)(O:ChartRatio G)(Q:Fin (a+1)→SealR G)(X:Herit Q)(w:Fin (a+1)→ℝ)(m n:ℕ):
    normalized L O Q (onSlots Q X w) m n=onSlots Q (normalized L O Q X m n) w:=by
  funext i j
  unfold normalized onSlots PermuteLens
  simp only [Pi.smul_apply,Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _=>smul_comm ..

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)(e:ℕ):
    let Q:=deck (G:=G) l d fit
    let L:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,∀ (b n D : ℕ), b ≤ m → m ≤ n → ∀(X:Herit Q)(w:Fin (a+1)→ℝ)(φ:Wilt Q),
    (∀i,0<w i) →
    AutumnDay L R.metals.O φ (normalized L R.metals.O Q X m n) m b n D =
      (∏i,w i) • AutumnDay L R.metals.O φ
        (normalized L R.metals.O Q (onSlots Q X (fun j=>(w j)⁻¹)) m n) m b n D:=by
  intro Q L
  filter_upwards [FundedMarkedCoverRows.realm R simple v funded (a+1) l d fit e 0 0] with m invited
  obtain ⟨V,lv,ro,_,anchor,_,_,⟨school⟩,_⟩:=invited
  intro b n D bm mn X w φ pos
  have clear(i j):i≠j → ClearDay (φ i) (φ j) (-14+14):=by
    intro _ x _ y _
    simp
  let Y:=onSlots Q X (fun j=>(w j)⁻¹)
  have restore:onSlots Q (normalized L R.metals.O Q Y m n) w=normalized L R.metals.O Q X m n:=by
    rw [←moved]
    exact congrArg (fun U=>normalized L R.metals.O Q U m n) (tariffGrow pos Q X)
  have same:=crop_factor (R:=V) (d:=D) (normalized L R.metals.O Q Y m n) φ school w bm anchor.le mn clear
  rwa [lv,ro,restore] at same

end YM.Integration.WilsonPositionProgramWindingSlotScale
end
