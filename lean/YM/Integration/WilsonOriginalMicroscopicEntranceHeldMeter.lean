import YM.Integration.WilsonMeasuredPublicEntranceFixedBill

/-! A fixed Taylor order pays every signed share at the nonconstant three-field hearing before either regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldMeter
open Function Finset Filter Lattice Wilson RG Source Labels PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Extra.Histories.Motion
open WilsonReflectedPublicGuardedColumns WilsonThermometerUnitFilingFieldRange WilsonReflectedPublicCommonSoftLaw
open WilsonMeasuredPublicEntranceCheapOrder WilsonMeasuredPublicEntrancePeerShares WilsonMeasuredPublicEntranceCropRoof
open WilsonOriginalOccupiedStencil Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V]
open WilsonMeasuredPublicEntranceFixedBill (depth order)

theorem original (d:V → ℕ)(simple:G.Simple)(t:ℕ):
    ∀ᶠ f:ℕ in atTop,∀N per:ℕ,f≤N → ∀s:(Stock.census V).Mode,
      let H:=R.family.path.levels.clock.hatBeta f
      let a:=fun i=>gross R (d i) f
      let e:=fun i=>net R (d i) f (depth d t)
      let P:=order t
      route a (fun i=>a i+e i) e s.val.toList+((shares s.val.toList).length:ℝ)*
        ((H^P)⁻¹+((H^P)⁻¹+(regulatorRun R.family N per f)^P*(Multi.shards (Stock.census V) s).card)+(H^P)⁻¹)≤(H^t)⁻¹:=by
  filter_upwards [WilsonMeasuredPublicEntranceFixedBill.original R d simple 0 t] with f pay
  intro N per live s H a e P
  have older:=pay N per live 0 le_rfl s
  have roofed:((Multi.shards (Stock.census V) s).card:ℝ) ≤ roof s 0:=by
    apply le_add_of_nonneg_right
    unfold WilsonMeasuredPublicEntranceCropRoof.area
    positivity
  have g:0≤regulatorRun R.family N per f:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  apply le_trans _ (by simpa only [Nat.mul_zero,Nat.zero_add] using older)
  gcongr

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldMeter
end
