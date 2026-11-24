import YM.Integration.WilsonSubcriticalScalarMoments
import YM.Integration.WilsonSubcriticalRichGlyph
import YM.Integration.WilsonPositionSeparatedProfileUnitDressing
import YM.FVA2.Main

/-! All independently commissioned separated coefficients on scalar unit
inputs, with the actual finite field and coupling substitutions at every
engineering horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonScalarFiledCorrelations
open Function Filter Set Finset MS MS.Local.Physical MS.Menus MS.Land MS.Theater MS.Fleet
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open WilsonSubcriticalRichGlyph WilsonSubcriticalRichOptics
open scoped Classical BigOperators
variable {G : Gauge} (C : Family G) (simple : G.Simple)
  {O : Booked (Press.portDeck G)} (M : MS_Data G O)

include C simple in
private theorem zero_height (ν : ℝ) {n : ℕ} (x : Stage n) (v : Fin n→Sec G 0)
    {k : ℕ} (hk : k≠0) : Equator.wave ν M 0 n x k v = 0 := by
  let B:=Press.portDeck G
  obtain ⟨b,only⟩:=registered C B simple
  let y:=lifted B 0 b
  let D:=Daylight B 0
  let t : Fin n→Dframe.Toon G 0 := fun _=>y
  let j : Plaid B 0 := Dframe.panel y
  have row : Dframe.continuum ν M t k x.val=0 := by
    change MS.Dial.tour M (fun _:Fin n=>(⟨0,j⟩:MS.Rake.Label B)) ν (Arrival.Schedule.plot x.val) univ k=0
    rw [WilsonSubcriticalMSMoments.whole M (fun _:Fin n=>j) ν (Arrival.Schedule.track x.property) univ]
    simp only [WilsonSubcriticalMSMoments.constant,if_neg hk]
  let a (i : Fin n) := D.repr (v i) y
  have letters : v=fun i=>a i • Dframe.fill t i := by
    funext i
    calc
      v i = ∑ u,D.repr (v i) u • D u := (D.sum_repr _).symm
      _ = D.repr (v i) y • D y := by
        apply Finset.sum_eq_single y
        · intro u _ ne
          exact (ne (only 0 (by decide) u)).elim
        · intro h
          exact (h (mem_univ _)).elim
      _ = _ := by rw [show D y=Dframe.theory y from Dframe.theory_sig y]; rfl
  change Dframe.meteor ν M 0 x.val k v=0
  rw [letters,MultilinearMap.map_smul_univ,Dframe.ribbon,row,smul_zero]

include C simple in
theorem wave (ν : ℝ) (d : ℕ) {n : ℕ} (x : Stage n) (c : Fin n→ℂ) (k : ℕ) :
    Equator.wave ν M d n x k (fun i=>c i • leaf G d)=if k=0 then ∏i,c i else 0 := by
  by_cases hk:k=0
  · subst k
    rw [if_pos rfl,show Equator.wave ν M d n x 0=scene x.val d from Equator.before ν M n x,
      MultilinearMap.map_smul_univ]
    change (∏i,c i) • Maxwell.Wick.moment G x.val (fun _=>1)=_
    rw [Maxwell.Wick.constants,smul_eq_mul,mul_one]
  rw [if_neg hk]
  have inherited:=Equator.wave_walk ν M (Nat.zero_le d) n x k (fun i=>c i • leaf G 0)
  have unit : (up (G:=G) (Nat.zero_le d)) ∘ (fun i:Fin n=>c i • leaf G 0)=(fun i=>c i • leaf G d) := by
    funext i
    rw [comp_apply,map_smul]
    rfl
  rw [unit] at inherited
  exact inherited.symm.trans (zero_height C simple M ν x _ hk)

include C in
theorem coefficient (Z : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {P : Prescription (Press.portDeck G)} {dial : Bool} (named : Main.Match Z simple M P dial)
    (ν : ℝ) (d : ℕ) {n : ℕ} (x : Stage n) (c : Fin n→ℂ) (k : ℕ) :
    Facets.actMark (Measure.Z Z.scheme Z.criterion ν M d)
      (Facets.couple (Measure.f Z.criterion ν M) (Equator.wave ν M d)) n x k (fun i=>c i • leaf G d) =
        if k=0 then ∏i,c i else 0 := by
  rw [WilsonPositionSeparatedProfileUnitDressing.marked _ (named.frame ν d).1]
  exact WilsonPositionSeparatedProfileUnitDressing.coupled _ _ x _ _ (wave C simple M ν d x c) k

end YM.Integration.WilsonScalarFiledCorrelations
