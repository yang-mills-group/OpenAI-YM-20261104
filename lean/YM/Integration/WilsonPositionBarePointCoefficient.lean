import YM.Integration.WilsonPositionOriginalEpochQuadrature

/-! Invert the finite coupling on the actual unintegrated position tensor, including both
finite field changes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionBarePointCoefficient
open Filter Set Finset Function Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.WilsonBridge.Coupling PowerSeries Lattice
open MS.Book MS.Book.Program
open WilsonPositionRawFiling WilsonPositionRawEpoch
open scoped BigOperators Classical Topology
variable {G : Gauge} {Z : WilsonPrescription G} {i B n : ℕ}
local notation "m" => Z.run.step i

private theorem gate (a : Key) (d : ℕ) (S : Guard G d) :
    a.gate S = Reg.Point.stepV a.knob S := by
  ext1 j
  rw [Key.gate,Reg.Point.stepV,coeff_mk,coeff_mk,Key.mix,rules]
  rw [show Finset.Iic j = range (j+1) from Finset.ext fun _=>by simp]
  apply sum_congr rfl
  intro k _
  rw [show cut a.knob k j = (a.Γ j k:ℂ) from (a.canonical j k).symm,Complex.coe_smul]

private theorem filed (s : Sample n) (d : ℕ) (use : Rose.Use Z.scheme Z.criterion s.F) :
    substitute (Rose.chosen Z.scheme Z.criterion s.F) (Rose.measureₓ Z.scheme Z.criterion d s) =
      Rose.cooked Z.scheme Z.store d s := by
  let a := key Z s.F
  have hz : Rooted a.knob := (coeff_zero_eq_constantCoeff_apply _).trans a.root
  ext1 k
  ext1 v
  have hv : Reg.Point.story (Rose.measureₓ Z.scheme Z.criterion d s) v =
      (Reg.Point.story (Rose.cooked Z.scheme Z.store d s) v).subst (Rose.χ Z.scheme Z.criterion s.F) := by
    apply PowerSeries.ext
    intro j
    rw [Reg.Point.story,coeff_mk]
    change (Rose.turn Z.scheme Z.criterion s.F (Rose.cooked Z.scheme Z.store d s) j) v = _
    simp only [Rose.turn,_root_.sum_apply,_root_.smul_apply]
    exact Rose.turn_coins Z.scheme Z.criterion s.F (fun j=>Rose.cooked Z.scheme Z.store d s j v) j
  have h := Reg.Point.moves (Rose.measureₓ Z.scheme Z.criterion d s) v hz
  rw [hv,subst_comp_subst_apply (Rose.χday ..) a.has] at h
  change _ = subst (subst (Rose.chosen Z.scheme Z.criterion s.F) (Rose.χ Z.scheme Z.criterion s.F)) _ at h
  rw [Rose.χverts _ _ _ use,X_subst] at h
  exact (coeff_mk ..).symm.trans ((congrArg (coeff k) h).trans (coeff_mk ..))

private theorem refile (s : Sample n) (d : ℕ) (use : Rose.Use Z.scheme Z.criterion s.F) :
    substitute (key Z s.F).knob (Speed.forms_t Z.scheme Z.criterion s d) =
      Dframe.status (deck (Z.store.layout Z.scheme s.F d) *
        (key Z s.F).gate (Scale.Measure.adjust Z.scheme Z.criterion d)) (live Z.scheme d s) := by
  let a := key Z s.F
  let S := Scale.Measure.adjust Z.scheme Z.criterion d
  have h0 : Rooted a.knob := (coeff_zero_eq_constantCoeff_apply _).trans a.root
  change substitute a.knob (Dframe.status S (Rose.measureₓ Z.scheme Z.criterion d s)) = _
  rw [← Reg.Point.resetP _ _ _ h0,← gate]
  have hf : substitute a.knob (Rose.measureₓ Z.scheme Z.criterion d s) = Rose.cooked Z.scheme Z.store d s :=
    filed (Z:=Z) s d use
  rw [hf]
  exact Reg.Point.eternal (deck (Z.store.layout Z.scheme s.F d)) (a.gate S) (live Z.scheme d s)

private theorem sampled (P : Handoff.Directory Z i B) (d : ℕ) (v : Tags G d n) (s : Sample n)
    (mesh : s.F = m) (k : ℕ) (cover : Handoff.Directory.budget G n d + k ≤ B) :
    WilsonPositionOriginalEpochQuadrature.point P d v s.layout k =
      Dframe.status (WilsonPositionRawEpoch.matrix Z i d) (live Z.scheme d s) k v := by
  obtain ⟨sm,x,c⟩ := s
  change sm = Z.run.step i at mesh
  subst sm
  rw [Dframe.seen]
  unfold WilsonPositionOriginalEpochQuadrature.point
  apply sum_congr rfl
  intro a ha
  have hk : a none ≤ k := ((totaled a).mp ha) ▸ single_le_sum (f:=fun j=>a j)
    (fun _ _ => Nat.zero_le _) (mem_univ none)
  exact (Handoff.Directory.lit_exact (i:=i) n d (pulseU a (WilsonPositionRawEpoch.matrix Z i d) v) P x (a none) (by omega)).symm

theorem read (P : Handoff.Directory Z i B) (d : ℕ) (v : Tags G d n) (s : Sample n)
    (mesh : s.F = m) (use : Rose.Use Z.scheme Z.criterion m) (k : ℕ)
    (cover : Handoff.Directory.budget G n d + k ≤ B) :
    WilsonPositionOriginalEpochQuadrature.point P d v s.layout k =
      coeff k ((Reg.Point.story (Speed.forms_t Z.scheme Z.criterion s d) v).subst
        (Rose.chosen Z.scheme Z.criterion m)) := by
  let a := key Z s.F
  have h0 : Rooted a.knob := (coeff_zero_eq_constantCoeff_apply _).trans a.root
  have hs := refile (Z:=Z) s d (show Rose.Use Z.scheme Z.criterion s.F by rwa [mesh])
  have hm : deck (Z.store.layout Z.scheme s.F d) *
      (key Z s.F).gate (Scale.Measure.adjust Z.scheme Z.criterion d) = WilsonPositionRawEpoch.matrix Z i d := by
    rw [mesh]
    rfl
  rw [hm] at hs
  change substitute a.knob (Speed.forms_t Z.scheme Z.criterion s d) = _ at hs
  have hv := Reg.Point.moves (Speed.forms_t Z.scheme Z.criterion s d) v h0
  rw [hs] at hv
  rw [← mesh]
  change _ = coeff k ((Reg.Point.story (Speed.forms_t Z.scheme Z.criterion s d) v).subst a.knob)
  rw [← hv,Reg.Point.story,coeff_mk]
  exact sampled P d v s mesh k cover

end YM.Integration.WilsonPositionBarePointCoefficient
