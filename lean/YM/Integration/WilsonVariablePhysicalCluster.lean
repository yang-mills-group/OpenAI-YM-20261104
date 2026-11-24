import YM.Integration.SharedIntrinsicWilsonGrid

/-! Compactness for the whole regulator output when the physical fields are chosen at the reporting scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVariablePhysicalCluster
open Function Filter MeasureTheory Extraction Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards OPE.Log
open Frontier6.Road PhysMS Trace.Pilot Trace.Physical.GermGraph RG16.Literal MultilinearCellCapture
open FilteredIntrinsicGramReadout FilteredWilsonProduct FundedIntrinsicReadout IntrinsicPhysicalCell
open IntrinsicProductCompactness ContinuumIntrinsicWilsonProduct SharedIntrinsicWilsonGrid
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order} {D : ℕ}
variable {I : Type} [Fintype I] {d : I → ℕ}

private theorem cont {m : I → ℕ} (j : ℕ) (x : I → Cover) (v : (i : I) → C.label (m i)) (w : ℕ × ℕ) :
    Continuous (leaves C j m x v w.1 w.2) := by
  rw [show leaves C j m x v w.1 w.2 = fun U => ∏ i, C.O w.1 w.2 (v i) (location C.S j w.1 w.2 (x i)) U
    from funext fun U => Finset.prod_apply ..]
  exact continuous_finsetProd _ fun i _ => C.continuousO ..

private theorem profile (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : ℝ → (i : I) → (Climb.Bel C.book).Field (d i))
    {b m j : ℝ → ℕ} {h a c : ℝ} (hb : Height C.S trail LogV b h) (hm : Height C.S trail LogV m a)
    (hj : Height C.S trail LogV j c) (hh : 0<h) (ha : h<a) (hc : a<c) (D : ℕ) :
    ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (b t) (m t) (j t) x →
      ∃ A : ℝ, ∀ᶠ w in f.fuse, ‖value (D:=D) F.room.cutoff (b t) w (field F R J (v t) t (j t) x w)‖ ≤ A := by
  have each := eventually_all.mpr (fun g : Grades d => grade F facility anchor hb hm hj hh ha hc
      (fun t i => component F R J (v t) g t i) D)
  filter_upwards [each] with t stocked
  intro x hx
  choose A priced using fun g : Grades d => stocked g x hx
  refine ⟨∑ g, A g,?_⟩
  filter_upwards [eventually_all.mpr priced] with w paid
  obtain ⟨ho,live,_,_⟩ := paid (fun _ => 0)
  let Y (g : Grades d) := leaves C (j t) (levels g) x (component F R J (v t) g t) w.1 w.2
  have booked (g : Grades d) : Booked C w.1 w.2 D (Y g) (b t) live := by
    obtain ⟨_,_,book,_⟩ := paid g; exact book
  have add := IntrinsicProductLinearity.booked_sum C w.1 w.2 D (b t) F.room.cutoff ho live
    (fun _ : Grades d => (1:ℂ)) Y (fun g => cont ..) booked
  simp only [one_smul] at add
  have eq : value (D:=D) F.room.cutoff (b t) w (field F R J (v t) t (j t) x w) =
      ∑ g, value (D:=D) F.room.cutoff (b t) w (Y g) := by
    simp_rw [value_eq F.room.cutoff ho live]
    unfold label
    rw [field_expansion,add.2,map_sum]
  rw [eq]
  apply (norm_sum_le ..).trans
  exact Finset.sum_le_sum fun g _ => by obtain ⟨_,_,_,h⟩ := paid g; exact h

/-- Every later plotting scale admits every input, including one chosen at that scale. -/
theorem all_inputs (F : Spec.Final C f S) (fac : Facilities C f S) (anchor : I)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ → PhysMS.tower S)
    (P : Plan C D (Fintype.card I) (∑ i,d i)) :
    ∀ᶠ t in trail, ∀ v : (i : I) → (Climb.Bel C.book).Field (d i), ∀ x : I → Cover,
      Plot C (P.b t) (P.middle t) (P.j t) x →
      ∃ z : C.label D, Cluster F Q J v t (P.b t) (P.j t) x z := by
  classical
  let good (t : ℝ) (v : (i : I) → (Climb.Bel C.book).Field (d i)) : Prop :=
    ∀ x : I → Cover, Plot C (P.b t) (P.middle t) (P.j t) x →
      ∃ z : C.label D, Cluster F Q J v t (P.b t) (P.j t) x z
  let test (t : ℝ) := if debt : ∃ v, ¬good t v then Classical.choose debt else 0
  have paid : ∀ᶠ t in trail, good t (test t) := by
    filter_upwards [profile F fac anchor Q J test P.coarse P.mid P.fine P.pos P.before (P.low.trans P.high) D] with t safe
    intro x plot
    obtain ⟨B,bill⟩ := safe x plot
    obtain ⟨l,sub,live,z,conv⟩ := Next.UVStress.finite_extract _ B bill
    exact ⟨z,l,live,sub,conv⟩
  filter_upwards [paid] with t payment
  intro v
  change good t v
  by_contra debt
  have existsDebt : ∃ v, ¬good t v := ⟨v,debt⟩
  exact Classical.choose_spec existsDebt (by simpa only [test,dif_pos existsDebt] using payment)

end YM.Integration.WilsonVariablePhysicalCluster
