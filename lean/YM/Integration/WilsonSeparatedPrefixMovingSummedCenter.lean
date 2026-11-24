import YM.Integration.WilsonSeparatedPrefixMovingJointCell

/-! A joint test of the N-born and captured sums on the actual reported
cell. Its inputs are the original common family and the nominated far seat. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingSummedCenter
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonSeparatedPrefixMovingJointCell (toll atCenter)
open WilsonSeparatedPrefixMovingBeforeRead (scalar heard)
open WilsonIndependentMovingRosterAllFineRead (Heard)
open WilsonSeparatedPrefixMovingMiddleLaw (composite)
open WilsonSeparatedPrefixMovingPairSector (current)
variable {G:Gauge}{H:Hol G}{n e D:ℕ}{C W V:Credit}
variable (R:Realm G (e+1) C)(Q:Fin (n+1)→SealR G)(F:SealR G)
variable (φ:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)

def issued (t m i N:ℕ)(y:ℝ):Era G Lounge:=agateV
  (F.spins R.draws R.paid ψ t i N (y/paceT R.draws.S m t) Y)
  (LodeStar R.draws R.paid φ X m i N y)

def landed (t m i older N:ℕ)(y:ℝ):Era G Lounge:=
  cruises R.draws R.paid N (F.h+capP Q) i older (issued R Q F φ ψ X Y t m i N y)

def typed (t m i older N:ℕ)(y:ℝ)(p:Phrase D)(x v:ℝ)(s:Cover)(o:CellR):Era G ℝ:=
  cruises R.draws R.paid N (F.h+capP Q) i older (tuftV (toll p x v s o) (issued R Q F φ ψ X Y t m i N y))

variable (roster:HorizonP H R W V Q)(far:PassportC H R F W V)
include roster far

theorem mounted (t m i older N:ℕ)(y:ℝ)(gate:R.anchor ≤ i)(_ear:older ≤ i)(cut:i ≤ N):
    Auth F.h (F.spins R.draws R.paid ψ t i N (y/paceT R.draws.S m t) Y) ∧
      Auth (capP Q) (LodeStar R.draws R.paid φ X m i N y) ∧
      Auth (F.h+capP Q) (issued R Q F φ ψ X Y t m i N y):=by
  have fa:=passportHead far ψ Y (y/paceT R.draws.S m t) gate cut (m:=t)
  have na:=cruising R.draws R.hG R.green cut le_rfl
    (Hearth_enter roster φ X (gate.trans cut) (le_refl N) (m:=m) (y:=y))
  exact ⟨fa,na,agateHome fa na⟩

theorem received (t m i older N:ℕ)(y:ℝ)(gate:R.anchor ≤ i)(ear:older ≤ i)(cut:i ≤ N)(z:CellR):
    locale z (landed R Q F φ ψ X Y t m i older N y)=composite R Q F φ ψ X Y z y t m older N i:=by
  obtain ⟨fa,na,_⟩:=mounted R Q F φ ψ X Y roster far t m i older N y gate ear cut
  exact atCenter R fa na ear cut z

theorem unroll (t m i older N:ℕ)(y:ℝ)(gate:R.anchor ≤ i)(ear:older ≤ i)(cut:i ≤ N)
    (p:Phrase D)(x v:ℝ)(s:Cover)(o:CellR):
    typed R Q F φ ψ X Y t m i older N y p x v s o=
      tuftV (toll p x v s o) (landed R Q F φ ψ X Y t m i older N y):=by
  exact (cruiseT _ R.draws ear R.hG R.green cut
    (mounted R Q F φ ψ X Y roster far t m i older N y gate ear cut).2.2).symm

omit roster far in
theorem charge (P:Lounge)(p:Phrase D)(x v:ℝ)(s:Cover)(o:CellR):
    ‖toll p x v s o P‖≤‖P‖*‖wheelC x v s p o‖:=
  ((HourFace dayMeasure D P).le_opNorm _).trans (mul_le_mul_of_nonneg_right
    ((hour_price dayMeasure P D).trans (drape_norm dayMeasure P)) (norm_nonneg _))

theorem original (t b m older N h:ℕ)(y price:ℝ)(gate:R.anchor ≤ b)(ear:older ≤ b)(cut:b ≤ N)
    (ω:Fin 0→YForest G)(p:Phrase D)(x v:ℝ)(s:Cover)(o:CellR)
    (sale:∀z:CellR,Heard e h (paceT R.draws.S m t) price
      (fun q=>scalar R Q F φ ψ X Y z y t b m older N q ω)):
    Heard e h (paceT R.draws.S m t) (price*‖wheelC x v s p o‖) (fun q=>
      (typed R Q F φ ψ X Y t m N older N y p x v s o).2 q 0 ω-
      (typed R Q F φ ψ X Y t m b older N y p x v s o).2 q 0 ω):=by
  let T:=paceT R.draws.S m t
  apply heard _ _ _ _ _ (pace_pos ..)
  intro q hq
  let near:=landed R Q F φ ψ X Y t m b older N y
  let top:=landed R Q F φ ψ X Y t m N older N y
  let L:Lounge:=top.2 q 0 ω-near.2 q 0 ω
  have locate (z:CellR):L z=scalar R Q F φ ψ X Y z y t b m older N q ω:=by
    have e₁:=congr_arg (fun X:Era G ℝ=>X.2 q 0 ω) (received R Q F φ ψ X Y roster far t m N older N y (gate.trans cut) (ear.trans cut) le_rfl z)
    have e₂:=congr_arg (fun X:Era G ℝ=>X.2 q 0 ω) (received R Q F φ ψ X Y roster far t m b older N y gate ear cut z)
    change (top.2 q 0 ω z)-(near.2 q 0 ω z)=_
    change (top.2 q 0 ω z)=_ at e₁
    change (near.2 q 0 ω z)=_ at e₂
    rw [e₁,e₂]
    unfold WilsonSeparatedPrefixMovingBeforeRead.scalar composite LodeStar
    rw [cruises_top,ash_spans]
  have nn:0≤(T^h)⁻¹*price:=(norm_nonneg _).trans ((sale o).1 q hq)
  have gross:‖L‖≤(T^h)⁻¹*price:=(ContinuousMap.norm_le _ nn).mpr fun z=>by rw [locate];exact (sale z).1 q hq
  rw [unroll R Q F φ ψ X Y roster far t m N older N y (gate.trans cut) (ear.trans cut) le_rfl,
    unroll R Q F φ ψ X Y roster far t m b older N y gate ear cut]
  change ‖toll p x v s o (top.2 q 0 ω)-toll p x v s o (near.2 q 0 ω)‖≤_
  rw [←map_sub]
  exact (charge L p x v s o).trans ((mul_le_mul_of_nonneg_right gross (norm_nonneg _)).trans_eq (mul_assoc ..))

end YM.Integration.WilsonSeparatedPrefixMovingSummedCenter
