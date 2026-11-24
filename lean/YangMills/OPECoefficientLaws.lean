import YangMills.CorrelationHierarchy

/-! Intrinsic laws for the coefficients appearing in the physical OPE sums. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.Hierarchy
open Function Filter
open scoped BigOperators Classical Topology
variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)

/-- The one-field OPE at its own center reads the coordinates of that field. -/
def singletonCoordinate (a : T.Tag) (w : ℕ) (channel : T.Channel w) : ℂ :=
  T.coefficient (fun _ : Unit => a) w channel (fun _ => 0) 0

/-- Channels have dual coordinates on the physical fields. Inserting the unit
in any shrinking, eventually distinct configuration preserves the coefficients,
including when a pair approaches much faster than the diameter. -/
structure CoefficientLaws : Prop where
  multilinear {I : Type} [Fintype I] (d : I → ℕ) (w : ℕ) (c : T.Channel w)
      (x : I → Spacetime) (o : Spacetime) :
    ∃ form : MultilinearMap ℂ (fun i => T.Field (d i)) ℂ,
      ∀ v, T.coefficient (fun i => ⟨d i, v i⟩) w c x o = form v
  sameInputs {I J : Type} [Fintype I] [Fintype J] (slots : J ≃ I)
      (a : I → T.Tag) (b : J → T.Tag) (x : I → Spacetime) (o shift : Spacetime)
      (same : ∀ j, T.toLabel (b j).1 (b j).2 = T.toLabel (a (slots j)).1 (a (slots j)).2)
      (w : ℕ) (c : T.Channel w) :
    T.coefficient b w c (fun j => x (slots j) + shift) (o + shift) = T.coefficient a w c x o
  dual (w : ℕ) (i j : T.Channel w) :
    T.singletonCoordinate ⟨w, T.channelField w i⟩ w j = if i = j then 1 else 0
  otherDegree (d w : ℕ) (different : w ≠ d) (i : T.Channel d) (j : T.Channel w) :
    T.singletonCoordinate ⟨d, T.channelField d i⟩ w j = 0
  complete (h : ℕ) (v : T.Field h) :
    (∑ d : Fin (h + 1), ∑ c : T.Channel d.val,
      T.singletonCoordinate ⟨h, v⟩ d.val c • T.toLabel d.val (T.channelField d.val c)) = T.toLabel h v
  deleteUnit {I A : Type} [Fintype I] (f : Filter A) (a : I → T.Tag)
      (x : A → (Unit ⊕ I) → Spacetime) (o : A → Spacetime)
      (shrinks : Tendsto (fun t i => x t i - o t) f (𝓝 0))
      (distinct : ∀ᶠ t in f, Injective (x t)) (w : ℕ) (c : T.Channel w) :
    ∀ᶠ t in f, T.coefficient (Sum.elim (fun _ => ⟨4, T.unitAtFour⟩) a) w c (x t) (o t) =
      T.coefficient a w c (x t ∘ Sum.inr) (o t)

/-- A zero channel field would have coordinate zero by multilinearity and coordinate one
by duality. This excludes zero-channel padding even if every spectator ignores it. -/
theorem CoefficientLaws.channelField_ne_zero {T : Hierarchy C} (laws : T.CoefficientLaws)
    (w : ℕ) (c : T.Channel w) : T.channelField w c ≠ 0 := by
  intro zero
  obtain ⟨L, hL⟩ := laws.multilinear (fun _ : Unit => w) w c (fun _ => 0) 0
  have dual := laws.dual w c c
  unfold singletonCoordinate at dual
  rw [if_pos rfl, zero, hL, L.map_coord_zero () rfl] at dual
  exact zero_ne_one dual

/-- Two unit insertions leave any field at its fusion center unchanged. The
three positions may approach at independent rates. The equality is exact on
the eventual configurations and at the finite cutoff equal to the field grade. -/
theorem CoefficientLaws.twoUnits {T : Hierarchy C} (laws : T.CoefficientLaws)
    {A : Type} (f : Filter A) (h : ℕ) (v : T.Field h)
    (x : A → (Unit ⊕ (Unit ⊕ Unit)) → Spacetime)
    (o : A → Spacetime) (atCenter : ∀ t, x t (.inr (.inr ())) = o t)
    (shrinks : Tendsto (fun t i => x t i - o t) f (𝓝 0))
    (distinct : ∀ᶠ t in f, Injective (x t)) :
    let unit : T.Tag := ⟨4, T.unitAtFour⟩
    let inputs := Sum.elim (fun _ : Unit => unit)
      (Sum.elim (fun _ : Unit => unit) (fun _ : Unit => (⟨h, v⟩ : T.Tag)))
    ∀ᶠ t in f, (∑ d : Fin (h+1), ∑ c : T.Channel d.val,
      T.coefficient inputs d.val c (x t) (o t) • T.toLabel d.val (T.channelField d.val c)) = T.toLabel h v := by
  intro unit inputs
  let single := fun _ : Unit => (⟨h, v⟩ : T.Tag)
  let pair := Sum.elim (fun _ : Unit => unit) single
  let y := fun t => x t ∘ Sum.inr
  have shrinks' : Tendsto (fun t i => y t i - o t) f (𝓝 0) :=
    tendsto_pi_nhds.mpr fun i => (tendsto_pi_nhds.mp shrinks) (Sum.inr i)
  have distinct' : ∀ᶠ t in f, Injective (y t) := distinct.mono fun _ h => h.comp Sum.inr_injective
  have each (d : Fin (h+1)) (c : T.Channel d.val) :
      ∀ᶠ t in f, T.coefficient inputs d.val c (x t) (o t) = T.singletonCoordinate ⟨h, v⟩ d.val c := by
    filter_upwards [laws.deleteUnit f pair x o shrinks distinct d.val c,
      laws.deleteUnit f single y o shrinks' distinct' d.val c] with t h1 h2
    refine h1.trans (h2.trans ?_)
    have translate := laws.sameInputs (Equiv.refl Unit) single single (fun _ => 0) 0 (o t)
      (fun _ => rfl) d.val c
    have position : y t ∘ Sum.inr = fun _ : Unit => o t := funext fun ⟨⟩ => atCenter t
    simpa only [position, zero_add, singletonCoordinate, single] using translate
  filter_upwards [eventually_all.mpr fun d => eventually_all.mpr (each d)] with t ht
  simpa only [ht] using laws.complete h v

end YangMills.Hierarchy
