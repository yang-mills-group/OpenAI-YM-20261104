import YM.Integration.WilsonMaxwellThermometerSurveyThreeRoster
import YM.Integration.WilsonMaxwellThermometerPublicGalop

/-! The coefficient of the measured W-master minus the public W face is
read on one finite basis. Keep the earlier complete inverse, each public
engineering/Wick correction and the public field slope on every present arm. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonMaxwellThermometerSurveyThreeLedger
open Function Finset Lattice Wilson XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1
open PhysicalNext.Repeat.Legato
open WilsonMaxwellThermometerSurveyThreeRoster (Pin read hear paid wallet)
open WilsonOriginalThermometerPalette (levels)
open WilsonPositionProgramInversionMaterial (Axes)
open WilsonMaxwellThermometerPublicGalop (quotient)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G)(V:Store G)(t:Sample 3)(p:Tags G 6 3)

def invoice (e:ℕ)(S:Finset (Fin 3)):Pin R→₀ PowerSeries ℂ:=
  ∑f∈tally e 3,if ∀i:Fin 3,i∉S → f (some i)=0 then
    (PowerSeries.X^(e-f none):PowerSeries ℂ) • paid R W t (pulseU f (deck (V.layout W (grab t) 6)) p) S else 0

theorem printed (e:ℕ)(S:Finset (Fin 3)):
    PowerSeries.coeff e (hear R W t (invoice R W V t p e S))=quotient W (V:=V) t p e S:=by
  unfold invoice quotient
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases live:∀i:Fin 3,i∉S → f (some i)=0
  · rw [if_pos live,if_pos live,map_smul,smul_eq_mul,
        WilsonMaxwellThermometerSurveyThreeRoster.deposited,PowerSeries.coeff_X_pow_mul',
        if_pos (Nat.sub_le e (f none))]
    have h:(f none)≤e:=by
      rw [← (totaled f).1 hf]
      exact Finset.single_le_sum (f:=fun v=>f v) (fun i _=>Nat.zero_le _) (Finset.mem_univ none)
    rw [Nat.sub_sub_self h]
  · simp only [if_neg live,map_zero]

def change (e:ℕ)(S:Finset (Fin 3))(ζ:Axes R levels→PowerSeries ℂ):Pin R→₀ PowerSeries ℂ:=
  wallet R ζ-invoice R W V t p e S

theorem original (e:ℕ)(S:Finset (Fin 3))(ζ:Axes R levels→PowerSeries ℂ):
    PowerSeries.coeff e (WilsonMaxwellThermometerSurveyThreeInversion.surveyed R W t.F.p t.layout ζ)-
      quotient W (V:=V) t p e S = PowerSeries.coeff e (hear R W t (change R W V t p e S ζ)):=by
  rw [change,map_sub,map_sub,WilsonMaxwellThermometerSurveyThreeRoster.measured,printed]

theorem ground (S:Finset (Fin 3))(ζ:Axes R levels→PowerSeries ℂ):
    let Δ:=change R W V t p 0 S ζ
    PowerSeries.coeff 0 (WilsonMaxwellThermometerSurveyThreeInversion.surveyed R W t.F.p t.layout ζ)-quotient W (V:=V) t p 0 S=
      ∑u∈Δ.support,PowerSeries.coeff 0 (Δ u)*PowerSeries.coeff 0 (read R W t u):=by
  intro Δ
  rw [original]
  exact show PowerSeries.coeff 0 (hear R W t Δ)=_ from by
    simp only [hear,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,smul_eq_mul,
      PowerSeries.coeff_zero_eq_constantCoeff,map_mul]

theorem first (S:Finset (Fin 3))(ζ:Axes R levels→PowerSeries ℂ):
    let Δ:=change R W V t p 1 S ζ
    PowerSeries.coeff 1 (WilsonMaxwellThermometerSurveyThreeInversion.surveyed R W t.F.p t.layout ζ)-quotient W (V:=V) t p 1 S=
      ∑u∈Δ.support,(PowerSeries.coeff 0 (Δ u)*PowerSeries.coeff 1 (read R W t u)+
        PowerSeries.coeff 1 (Δ u)*PowerSeries.coeff 0 (read R W t u)):=by
  intro Δ
  rw [original]
  exact show PowerSeries.coeff 1 (hear R W t Δ)=_ from by
    simp only [hear,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,smul_eq_mul,
      PowerSeries.coeff_one_mul,PowerSeries.coeff_zero_eq_constantCoeff]
    apply Finset.sum_congr rfl
    intro u _
    ring

end YM.Integration.WilsonMaxwellThermometerSurveyThreeLedger
end
