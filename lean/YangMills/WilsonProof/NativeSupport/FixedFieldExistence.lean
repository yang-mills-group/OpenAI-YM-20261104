import YangMills.ScalingLimits
import YangMills.WilsonProof.NativeSupport.WilsonExistence

import YangMills.FieldMeasurements
import YangMills.StressTensor
import YangMills.WilsonProof.NativeSupport.YangMills.CorrelationHierarchy

/-! Scaling tests and fixed-field identifications in a continuum hierarchy. -/

set_option autoImplicit false

noncomputable section

namespace YangMills.FixedFields

open Filter Set Function

open scoped Topology BigOperators

variable {g : GaugeGroup} {C : WilsonFamily g} (B : Maxwell.Reference g) (T : Hierarchy C)






theorem Laws.fixedCorrelations {X : T.MaxwellScaling B} (h : Laws B T X) (tables : Reconstruction.TableLaws T)
    (n : ℕ) (d : Fin n → ℕ) (a : (i : Fin n) → T.Field (d i)) (v : (i : Fin n) → B.sector (d i))
    (ha : ∀ i, Aligned B T X (d i) (engineering B T X (d i) (a i)) (v i))
    {K : Set (Points n)} (hK : IsCompact K) (hc : K ⊆ separated n) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ s : Option T.Character,
      ‖X.r k ^ (∑ i, d i) • T.correlation s (fun i => ⟨d i,a i⟩) (X.r k • x) -
        B.moment x (fun i => (v i).val)‖ ≤ ε := by
  filter_upwards [h.limit n d (fun k i => engineering B T X (d i) (a i) k) v ha K hK hc ε he] with k hk x hx s
  have sep : X.r k • x ∈ separated n := by
    intro i j e
    apply hc hx
    exact smul_right_injective _ (X.positive k).ne' e
  obtain ⟨M,hM⟩ := tables.multilinear s n _ sep
  have step := hk x hx s
  rw [hM] at step ⊢
  change ‖M (fun i => T.toLabel (d i) (((X.r k ^ d i : ℝ) : ℂ) • a i)) - _‖ ≤ ε at step
  simp only [map_smul,MultilinearMap.map_smul_univ] at step
  simp only [← Complex.ofReal_prod,Finset.prod_pow_eq_pow_sum,Complex.coe_smul] at step
  exact step

theorem Laws.selected {X : T.MaxwellScaling B} (h : Laws B T X) :
    Reconstruction.SelectedMaxwellJets B T X := by
  intro n j q marked ab K hK hc ε he
  exact (h.allJets n j q marked ab K hK hc ε he).mono (fun _ hk x hx => hk x hx (some T.selected))

def ExistsAt (run : _root_.YangMills.Wilson.Construction g) : Prop :=
  _root_.YangMills.Wilson.ExistsAt B run ∧ ∀ (p : ℕ → ℕ) (hp : StrictMono p), let T := (run.refine p hp).hierarchy
    ∃ X : T.MaxwellScaling B, Reconstruction.SelectedMaxwellJets B T X ∧ Laws B T X

def Score : Prop := ∃ pub : _root_.YangMills.Wilson.Publication, ∀ (g : GaugeGroup) (hg : g.IsSimple),
  ExistsAt (pub.coordinates g hg) (pub.runs g hg)

theorem implies_v22 (h : Score) : _root_.YangMills.Wilson.ExistenceScore := by
  obtain ⟨pub, all⟩ := h
  exact ⟨pub, fun g hg => (all g hg).1⟩

end YangMills.FixedFields
