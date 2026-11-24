import YM.Integration.WilsonSurveyedColorVacuumComponents
import YM.Integration.WilsonSurveyedColorVacuumDrive

/-! At fixed open rank the only implicit forcing comes from two ranks above,
including the regulated ghost and boson loop on the original two inputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorVacuumRank
open Function Set Filter MS Plane Koszul Heat Flux Arts Pilot Spin Arc Wire Rock Path Oceans
open Landau Alps Garment Garment.Wave Garment.Wick Shine Hem Mell Pearl Train Dock City
open WilsonSurveyedColorTensor WilsonSurveyedColorQuotient WilsonSurveyedColorPilot
open WilsonSurveyedColorSubtraction WilsonSurveyedColorFlow WilsonSurveyedColorRegulator
open WilsonSurveyedColorVacuumComponents WilsonSurveyedColorVacuumJoint
open scoped Classical BigOperators Topology
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)

private theorem atLength {D P : Type} (w : Legs (Note G D P)) (F H : Score G D P)
    (agree : ∀ l : Legs (Note G D P), l.length=w.length → F l=H l) :
    turn U F w = turn U H w := by
  induction w generalizing F H with
  | nil => exact agree [] rfl
  | cons i w ih =>
    change Koszul.D i (turn U F) w = Koszul.D i (turn U H) w
    rw [derivative,derivative]
    simp only [Finset.sum_apply,Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg (entry U j i.1.2 • ·)
    apply ih
    intro l e
    exact agree (MS.Color.setLeg i j :: l) (by simpa using e)

theorem mask (k : ℤ) (F : Mob G) : allDims U (spot k F) = spot k (allDims U F) := by
  funext m w
  change turn U ((spot k F) m) w = spot k (allDims U F) m w
  by_cases h : (w.length:ℤ)=k
  · rw [spotted h]
    apply atLength U w
    intro l e; exact spotted (by simpa [e] using h)
  · rw [spotsOff h]
    have hs := atLength U w ((spot k F) m) 0 (fun l e => spotsOff (by simpa [e] using h))
    simpa only [map_zero,Pi.zero_apply] using hs

abbrev Seen (k : ℤ) (X Y : Flats G) :=
  Pact ((color U).film ((rank k).film X)) ((rank k).film Y)

theorem select {X Y : Flats G} (h : Pact (ledger U X) Y) (k : ℤ) : Seen U k X Y := by
  intro i
  filter_upwards [h i] with z hz
  rw [WilsonSurveyedColorVacuumDrive.atSlot] at hz
  simp only [Action.atSlot]
  change allDims U (spot k (X i z)) = spot k (Y i z)
  exact (mask U k _).trans (congrArg (spot k) hz)

theorem bare {f g : Coat G} (h : Spotty (coat U f) g) (k : ℤ) :
    Spotty ((color U).tape ((rank k).tape f)) ((rank k).tape g) := by
  filter_upwards [h] with z hz
  change allDims U (spot k (f z)) = spot k (g z)
  exact (mask U k _).trans (congrArg (spot k) hz)

theorem loop {b : Bool} {t u r s : ℤ} {X Y : Flats G} (hx : ClockD b t r X)
    (hy : ClockD b u s Y) (k : ℤ) (higher : Seen U (k+2) X Y) :
    Seen U k (step0 G X) (step0 G Y) := by
  intro i
  cases i with
  | zero =>
    simp only [Action.atSlot]
    change Spotty ((color U).tape ((rank k).tape (blast 1 _ X 0))) ((rank k).tape (blast 1 _ Y 0))
    rw [bland (show 0<1 by decide),bland (show 0<1 by decide),map_zero,map_zero]
  | succ i =>
    simp only [Action.atSlot]
    change Spotty ((color U).tape ((rank k).tape (blast 1 _ X (i+1)))) ((rank k).tape (blast 1 _ Y (i+1)))
    rw [blade,blade]
    filter_upwards [higher i,sunny (hx i).fine.tune,sunny (hy i).fine.tune,high0] with z hz hX hY ht
    simp only [Action.atSlot] at hz
    change allDims U (spot (k+2) (X i z)) = spot (k+2) (Y i z) at hz
    change allDims U (spot k (feeD z • port z (A0 G 0) (X i z))) =
      spot k (feeD z • port z (A0 G 0) (Y i z))
    rw [map_smul,map_smul,map_smul,dollar (c_bo 0) hX ht,dollar (c_bo 0) hY ht,
        spot_o hX (c_bo 0) ht,spot_o hY (c_bo 0) ht]
    congr 1
    funext m
    exact oceanColor U (fun _ => line U _) (spotM _ hX) (spotM _ hY) (c_bo 0) ht
      (fun n => congrFun hz n)

theorem noneAbove {r k : ℤ} (h : r<k) {F : Mob G} (hF : Issue r F) : spot k F = 0 := by
  funext m l
  by_cases e : (l.length:ℤ)=k
  · exact (spotted e).trans (hF m l (by omega))
  · exact spotsOff e

end YM.Integration.WilsonSurveyedColorVacuumRank
end
