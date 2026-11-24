import YM.Integration.FVA1Physical.Sources.Round2.AllFlagStage
import YM.Extra.MULTISOURCE_TRAJECTORIES.Initial

/-! The exact marked C18 gas, divided by its original vacuum, is the tower of
physical conditional expectations of ordinary products of fine stencils.
For the retained forecast the only additional factor is the change in its
regular exponent. This holds on each configuration with arbitrary flags. -/

namespace YM.Integration.FVA1Physical.Round2

open MeasureTheory Lattice Wilson RG LocalLTE.Sail MergeProof MergeProof.Accent
open scoped Classical BigOperators

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I]

noncomputable def conditionalPath (H : History G) (N n : ℕ)
    (f : Config G (H.S.side N n) → ℂ) (i : ℕ) (hi : i ≤ N) : Config G (H.S.side i n) → ℂ :=
  Nat.decreasingInduction (motive := fun i _ => Config G (H.S.side i n) → ℂ)
    (fun k _ h => conditionalPush H N n k h) f hi

theorem conditionalPath_gust (H : History G) (hH : H.Selected) (N n : ℕ)
    (f : Config G (H.S.side N n) → ℂ) (i : ℕ) (hi : i ≤ N) :
    conditionalPath H N n (fun v => ((H.rep N n N).eval v)⁻¹ • f v) i hi =
      fun v => ((H.rep N n i).eval v)⁻¹ • gust H N n N f i hi v := by
  induction hi using Nat.decreasingInduction with
  | self => rw [conditionalPath,Nat.decreasingInduction_self,gust_base]
  | of_succ k hk ih =>
    rw [show conditionalPath H N n (fun v => ((H.rep N n N).eval v)⁻¹ • f v) k hk.le =
      conditionalPush H N n k (conditionalPath H N n _ (k+1) hk) from Nat.decreasingInduction_succ_left ..,
      gust_step H N n N f hk]
    change conditionalPush H N n k (conditionalPath H N n _ (k+1) hk) = _
    rw [ih]
    funext v
    exact conditionalPush_normalized H hH N n k hk _ v

/-- One posterior moment for every allowed subset of source slots. -/
noncomputable def momentTable {H : History G} {N n : ℕ} (B : Marker.Census I) (Y : Batch H N n I)
    (i : ℕ) (hi : i ≤ N) (v : Config G (H.S.side i n)) : Marker.Poly B :=
  fun s => conditionalPath H N n (fun u => ∏ j ∈ s.val, Y.wavelengths j u) i hi v

theorem physical_moment_table {H : History G} (hH : H.Selected) {N n : ℕ}
    (B : Marker.Census I) (Y : Batch H N n I) (i : ℕ) (hi : i ≤ N)
    (v : Config G (H.S.side i n)) :
    (((H.rep N n i).eval v : ℂ)⁻¹) • gust H N n N (Y.raw B) i hi v = momentTable B Y i hi v := by
  ext s
  let u : B.Mode → ℂ := fun j => if j = s then 1 else 0
  have datum (z : Marker.Poly B) : modeTest u z = z.part s := by
    classical
    simp [u,modeTest,ite_mul]
  have he := gust_modeTest_eq H N n (Y.raw B) (PhysicalNext.Repeat.Legato.Bandage.Harmonics.physicalSeed_integrable H hH B Y) u i hi
  simp_rw [datum] at he
  have top : (fun t => ((H.rep N n N).eval t)⁻¹ • (Y.raw B t).part s) =
      fun t => ∏ j ∈ s.val, Y.wavelengths j t := by
    funext t
    have hp := SectorNext.Vacuum.strictly H hH N n N le_rfl t
    change ((H.rep N n N).eval t)⁻¹ • (Accent.birth B (H.rep N n N) Y.wavelengths t).part s = _
    rw [Accent.birth,Marker.Poly.part_smul,Accent.Mach,Extra.Trajectories.pass_fire,
      Complex.real_smul,Complex.ofReal_inv,← mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hp.ne'),one_mul]
  have hs := congrFun (conditionalPath_gust H hH N n (fun t => (Y.raw B t).part s) i hi) v
  rw [top] at hs
  rw [Marker.Poly.part_smul,congrFun he v]
  rw [Complex.real_smul, Complex.ofReal_inv] at hs
  dsimp only [momentTable, Marker.Poly.part]
  exact hs.symm

end YM.Integration.FVA1Physical.Round2

namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics

open MeasureTheory Lattice RG Wilson RG.Supply Input Org Source Extra.Histories LocalLTE LocalLTE.Sail
open MergeProof MergeProof.Accent YM.Integration.FVA1Physical YM.Integration.FVA1Physical.Round2
open scoped BigOperators

variable {G : Gauge} {X : Metals G} {R : Rolls X.p} {A : Alloy X R} {P : Bolt A}
variable {N n i : ℕ} {I : Type} [DecidableEq I] [Fintype I]

theorem conditional_retainedForecast (B : Marker.Census I) (Y : Batch (Issue.trail P) N n I)
    (π : ∀ j : ℕ, j ≤ N → Y.steering j)
    (F : ∀ (j : I) (s : ℕ), ((Labels.frames G).level (Y.demand j)).Coeff →
      Coefficient ((Labels.frames G).level (Y.demand j)) ((Issue.trail P).S.side s n))
    (hi : i < N) (O : Appendix B ((Issue.trail P).rep N n i))
    (V : ∀ d, Music ((Labels.frames G).level d) (Issue.trail P) N n) {p K : ℕ}
    (h : ∀ v, FinePrint V B Y π F hi O p K v)
    (hp : Appendix.Prepared B ((Issue.trail P).rep N n i) O (Y.origin i) (Y.requested V i)
      (fun j => (Y.named V (π i hi.le) j).forced) (gust (Issue.trail P) N n N (Y.raw B) i hi.le))
    (v : Config G ((Issue.trail P).S.side i n)) :
    let Q := (Issue.trail P).rep N n i
    ((Q.eval v:ℂ)⁻¹) • gasForecast B Y π F hi O V v =
      momentTable B Y i hi.le v * Marker.Poly.pass
        (Sail.forecast B O (spectralValue Y π F hi) v - Sail.receipt B O (Y.requested V i) v) := by
  let H := Issue.trail P
  have he := Sail.Round2.retainedForecast_eq B (H.rep N n i) O (Y.origin i) (Y.requested V i)
    (spectralValue Y π F hi) _ _ hp v (h v).vote.1 (h v).vote.2
  change _ • Sail.Round2.retainedForecast B (H.rep N n i) O _ _ v = _
  rw [he, ← smul_mul_assoc, physical_moment_table P.choice]

end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
