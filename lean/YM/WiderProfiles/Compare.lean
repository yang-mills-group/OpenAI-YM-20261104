import YM.WiderProfiles.Result
import YM.WiderProfiles.Forest
import YM.FVA2.Main
/-!
# Instantiate §F on the independent Wilson prescription of the OPE argument.
Use its actual Match as in proof §B (e.g. as furnished by `Main.solution`).

At the `RecropCash` step of that argument, the independent coefficient used is `G^P`.
In `RoundMeter` and later OPE rows it is `G^X`. Here apply to both, on the growing
exterior (`T = exp t`), compact sets K,S in `x,y`, **not** in `x,T y`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.WiderProfiles
open Function Filter Set Metric Real
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Rake MS.Land
open Arrival Dframe O Scale.Facets
open O.Enh
open O.Score (squeeze)
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open scoped Topology ContDiff BigOperators Classical

variable {G : Gauge} {d n m : ℕ} (N : WilsonPrescription G) (h : G.Simple)
    (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (A : Prescription (Press.portDeck G)) (H : Main.Match N h T A true)
local notation "Y" => N.scheme
local notation "κ" => N.criterion
local notation "V" => (Scale.Measure.outlook Y κ)
local notation "ν" => Teller.logNu 1
abbrev cost (p : XSpace.Mesh) := p.spacing^(mildG/2)
include H

theorem matched (d n k a : ℕ) (c D : ℝ) (hc : 0 < c) (hD : 1 ≤ D) (v : Tags G d n) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ p in Front, ∀ s : Sample n, grab s=p → ∀ hy : Admits a c D s,
      ‖Rose.measureₓ Y κ d s k v - Scale.Measure.start Y κ d n ⟨familiar s, hy.conf hc⟩ k v‖ ≤
        C * cost p := by
  have hI := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  exact widerProfiles ν Y κ A T h hI.Taylor hI.still hI.base d n k a c D hc hD v

lemma adjusted (a k : ℕ) (c D : ℝ) (hc : 0 < c) (hD : 1 ≤ D) (v : Tags G d n) :
    Costing (fun i : Domain n a c D => Speed.forms_t Y κ i.val d k v)
      (fun i => V d n ⟨familiar i.val, i.property.conf hc⟩ k v) := by
  have hI := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  unfold Scale.Measure.outlook Speed.forms_t actMark; simp_rw [Dframe.seen]
  exact Bond.sum (fun i => le_max_right ..) _ _ _ (fun j _=>
    start_bond ν Y κ A T h hI.Taylor hI.still hI.base a hc hD (j none)
      (pulseU j (Scale.Measure.adjust Y κ d) v))

/-- Apply to the coefficient in the growing exterior setup, `G^P` and the
post-adjustment `G^X` (as a point kernel in the formal prediction). In
particular applies to the output-centre setup taking `n=1`, `K={0}`. -/
theorem compare_forest (K : Set (Points n)) (S : Set (Points m))
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m)
    (E : ℝ) (hE : 0 < E) (a k : ℕ) (v : Tags G d (n+m)) : ∃ t0 C : ℝ, 0 < C ∧
    ∀ᶠ p in Front, ∀ t ≥ t0, exp t ≤ E*(1+Schedule.theta p)^a →
      ∀ x ∈ K, ∀ y ∈ S, ∀ s : Sample (n+m), grab s=p → Schedule.Sized s →
        familiar s=forest x (squeeze (-t) y) →
        ∃ hc : familiar s ∈ conf (n+m),
        ‖Rose.measureₓ Y κ d s k v -
            Scale.Measure.start Y κ d (n+m) ⟨familiar s, hc⟩ k v‖ ≤ C * cost p ∧
        ‖Speed.forms_t Y κ s d k v - V d (n+m) ⟨familiar s,hc⟩ k v‖ ≤ C * cost p := by
  obtain ⟨c,D,hc,hD,r⟩ := forest_admits hK hx hS hy E hE
  obtain ⟨t0,h0⟩ := r.exists
  obtain ⟨C,hC,hf⟩ := matched N h T A H d (n+m) k a c D hc hD v
  obtain ⟨B,hB,hX⟩ := absorb (adjusted N h T A H a k c D hc hD v).delta
  rw [along, eventually_comap] at hX
  refine ⟨t0,C+B,add_pos hC hB, ?_⟩
  filter_upwards [hf,hX] with p hp hP t ht he x hx y hy s hs hv hr
  subst p
  obtain hq := h0 t ht a x hx y hy s hv he hr
  have hw : 0 ≤ cost s.F := Real.rpow_nonneg s.F.positive.le _
  exact ⟨hq.conf hc, (hp s rfl hq).trans (mul_le_mul_of_nonneg_right (by linarith) hw),
    (hP ⟨s,hq⟩ rfl).trans (mul_le_mul_of_nonneg_right (by linarith) hw)⟩

open O.Score PowerSeries
omit H
/-- Finite-regulator surrogate for a coefficient row, still in the
independent formal prescription. `forms_t` is `status adjust (measureₓ…)`.
`far` coefficient *definition* and its calculation/characterization still use
continuum correlations after independent regulator removal. -/
def at_mesh (s : Sample n) (v : Scan G n) :=
  Reg.Point.story (Speed.forms_t Y κ s (totalG v)) (tape v (guardT v))

include H
lemma at_mesh_bond (a k : ℕ) (c D : ℝ) (hc : 0 < c) (hD : 1 ≤ D) (v : Scan G n) :
    Costing (fun i : Domain n a c D => coeff k (at_mesh N i.val v))
      (fun i => coeff k (install V n (familiar i.val) v)) := by
  have he (i : Domain n a c D) : familiar i.val ∈ conf n := i.property.conf hc
  simp_rw [at_mesh,install,dif_pos (he _),Reg.Point.story,coeff_mk]; exact adjusted N h T A H a k c D hc hD _
end YM.FVA2.WiderProfiles
