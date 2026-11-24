import YM.Integration.WilsonThermometerWeakPairFarReading
import YM.Integration.WilsonThermometerWeakPairReader

/-! The measured child and the actual coherent finite sum on the moving reflected detector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairSameFrame
open Function Finset Filter Set Table Spec OPE OPE.Orbits OPE.Prescription Lattice RG
open Trace Trace.Pilot OPE.Nesting PhysMS PhysMS.Frame PhysicalNext.Repeat.Legato Frontier6.Tale
open EveryPhase Climb RG17 GapsContact GapsContact.Ascent GapsContact.Seams XSpace XSpace.Normalize Frontier6
open WilsonThermometerWeakMovingCorner
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
universe u
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {I:Type}[Fintype I]{d:I→ℕ}{P:Prescription F.sector.derivatives}
theorem original {simple:G.Simple}{A:EveryPhase.Almanac F}(H:Roll.{u} F simple A)
    (hp:P.Coherent)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (book:Foundation F Q)(J:ℝ→tower S)(V:Store G)(lead:Leading F J)
    (v:(i:I)→RG17.Free R.family (d i))(h e:ℕ)(w:RG17.Free R.family e){M s ε:ℝ}(mn:0≤M)(sp:0<s)(paid:0<ε):
    ∃(B:ℝ)(m:ℕ),0≤B ∧ ∀(t:ℝ→ℝ),Tendsto t trail trail→∀ᶠ r in trail,
      ∀(x:I→E4),WithinRoom r M s x 0→∀(z:E4),s≤‖z‖→∀(q:Viewers F),
        let ℓ:=upon (spectator F q) h 0 (sole (t r • z)) (sole ((far F J e (t r) w).2):Labels S (fun _:Unit=>e))
        ‖ℓ (shadowOld P h x 0 (born J r v)) - ℓ (Q.packet h x (born J r v) 0)‖≤
          B*dock (t r)^m/(t r)^((h:ℝ)+ε)*r^(h+1-ε):=by
  obtain ⟨B,bp,home⟩:=WilsonThermometerWeakPairReader.original F hp Q J lead book v h mn sp paid
  obtain ⟨C,m,cp,outer⟩:=WilsonThermometerWeakPairFarReading.original F H J V lead h e w sp paid
  refine ⟨C*B,m,mul_nonneg cp bp,fun t ht=>?_⟩
  have small:∀ᶠ u in trail,u≤1:=(ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [home,ht.eventually outer,ht.eventually self_mem_nhdsWithin,ht.eventually small] with r near far0 tp top
  intro x hx z hz q
  dsimp only
  rw [←map_sub]
  refine (far0 z hz q _).trans ?_
  have live:0≤C*dock (t r)^m/(t r)^((h:ℝ)+ε):=div_nonneg
    (mul_nonneg cp (pow_nonneg (zero_le_one.trans (dock_valid _ ⟨tp,top⟩)) _)) (Real.rpow_nonneg (le_of_lt tp) _)
  calc
    _ ≤ (C*dock (t r)^m/(t r)^((h:ℝ)+ε))*(B*r^(h+1-ε)):=mul_le_mul_of_nonneg_left (near x hx) live
    _ = _:=by ring
end YM.Integration.WilsonThermometerWeakPairSameFrame
end
