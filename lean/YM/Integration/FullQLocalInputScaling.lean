import YM.Integration.FullQLocalOutputScaling
import YM.Integration.LocalComparisonBarePreparationAt

/-! Fixed independent-slot normalization of an already represented bare input.
The original carrier, complete gas and every declared row are retained.
Only test arguments are pulled back. No admission or clock estimate is added. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FullQLocal.InputScaling
open Function Finset Lattice Wilson RG Marker LocalComparison
open Comparison.RG02 RG3.Held RG3.Script.Picnic
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
    {D : V → ComparisonDensity.Address.Orbit} {R : Census V}
    {P : Rep G n} {o : V → Site n}

private theorem tests_update (c : V → ℂ) (x : TestSpace D) (v : V)
    (a : (D v).Mood) :
    VariableScaling.tests c (Function.update x v a) =
      Function.update (VariableScaling.tests c x) v (c v • a) := by
  funext i
  by_cases hi : i = v
  · subst i
    simp [VariableScaling.tests]
  · simp [VariableScaling.tests, Function.update_of_ne hi]

private theorem letter_pullback (c : V → ℂ) {s : Finset V}
    {f : TestSpace D → ℂ}
    (h : Letter ℂ (fun v => (D v).Mood) s f) :
    Letter ℂ (fun v => (D v).Mood) s
      (fun x => f (VariableScaling.tests c x)) where
  stay x y hxy := h.stay _ _ (fun i hi =>
    congrArg (fun a : (D i).Mood => c i • a) (hxy i hi))
  join x i hi a b := by
    simp only [tests_update, smul_add]
    exact h.join (VariableScaling.tests c x) i hi (c i • a) (c i • b)
  scale x i hi r a := by
    simp only [tests_update]
    rw [smul_comm (c i) r a]
    exact h.scale (VariableScaling.tests c x) i hi r (c i • a)

/-- Every declared regular, forced, unit and caption row keeps its original
mode and its exact independent-slot multilinearity after the pullback. -/
theorem multilinear (c : V → ℂ) (T : Taste (TestSpace D) o P R)
    (h : Multilinear D T) :
    Multilinear D (pullback (VariableScaling.tests c) T) where
  regular i U := letter_pullback c (h.regular i U)
  forced i j U := letter_pullback c (h.forced i j U)
  unit v := letter_pullback c (h.unit v)
  captions i := letter_pullback c (h.captions i)

/-- All original support and origin data are unchanged, including zero rows. -/
theorem retains (c : V → ℂ) (T : Taste (TestSpace D) o P R)
    (address : V → Support n) (h : Retains T address) :
    Retains (pullback (VariableScaling.tests c) T) address where
  origins := h.origins
  regular := h.regular
  forced := h.forced
  captions := h.captions

/-- The zero test tuple remains zero under every fixed scalar pullback. -/
theorem active_zero (c : V → ℂ) (T : Taste (TestSpace D) o P R)
    (h : (T.leaf (fun _ => 0 : TestSpace D)).Active) :
    ((pullback (VariableScaling.tests c) T).leaf (fun _ => 0 : TestSpace D)).Active := by
  have hz : VariableScaling.tests c (fun _ => 0 : TestSpace D) = (fun _ => 0 : TestSpace D) := by
    funext v
    simp [VariableScaling.tests]
  change (T.leaf (VariableScaling.tests c (fun _ => 0 : TestSpace D))).Active
  simpa only [hz] using h

variable [Fintype V]

/-- The full density, including the original gas and every marked channel,
is evaluated at precisely the pulled-back test tuple. -/
theorem density (c : V → ℂ) (T : Taste (TestSpace D) o P R)
    (x : TestSpace D) (U : Config G n) :
    ((pullback (VariableScaling.tests c) T).leaf x).density U =
      (T.leaf (VariableScaling.tests c x)).density U := rfl

/-- The original all-coupling InputColors receipt pulls back with the packet.
Its common vacuum and power remain those of the original colors. -/
theorem input_colors (c : V → ℂ)
    (colors : TestSpace D → Bulk.Colors R G n)
    (packets : MarkedPackets D G n R)
    (h : InputColors colors packets) :
    InputColors (fun x => colors (VariableScaling.tests c x))
      (VariableScaling.packets c packets) where
  well x := h.well (VariableScaling.tests c x)
  vacuum x y := h.vacuum (VariableScaling.tests c x) (VariableScaling.tests c y)
  power x y := h.power (VariableScaling.tests c x) (VariableScaling.tests c y)
  marks x g hg U := by
    rw [VariableScaling.read]
    exact h.marks (VariableScaling.tests c x) g hg U

/-- An original full bare factorization yields the scaled input preparation
at any requested norm. Only the auxiliary remainder has zero marked rows.
The same original gas is retained; no rough-row norm upgrade is inferred. -/
def prepared_bare (c : V → ℂ) {C : Family G}
    (N period level : ℕ) (q : BudgetPoint)
    (Q : Global.StepCarrier C N period level)
    (roots : V → Site (C.side level period))
    (T : Taste (TestSpace D) roots Q.rep R)
    (colors : TestSpace D → Bulk.Colors R G (C.side level period))
    (packets : MarkedPackets D G (C.side level period) R)
    (w : V → ℝ) (kernelEnvelope : R.Mode → ℝ)
    (hLayout : (T.leaf (fun _ => 0 : TestSpace D)).Active)
    (hColors : InputColors colors packets)
    (hw : ∀ v, 0 < w v) (hEnvelope : ∀ s, 0 < kernelEnvelope s)
    (hQuiet : kernelEnvelope R.quiet = 1)
    (hGas : ∀ U : Config G (C.side level period),
      Summable (fun s : Finset ℕ => ‖Q.rep.activities.gasOccurrence Q.rep.p s U‖))
    (hFactor : ∀ (x : TestSpace D) (U : Config G (C.side level period)),
      (T.leaf x).density U = (Q.rep.eval U : ℂ) •
        Poly.pass (packets.read x (Pert.Asymptotics.regulatorRun C N period level) U)) :
    Global.PreparedWithRemainderAt N period level q Q roots
      (pullback (VariableScaling.tests c) T)
      (fun x => colors (VariableScaling.tests c x))
      (VariableScaling.packets c packets) w kernelEnvelope 0 0 :=
  Global.PreparedWithRemainderAt.of_bare_factorization N period level q Q roots
    (pullback (VariableScaling.tests c) T)
    (fun x => colors (VariableScaling.tests c x))
    (VariableScaling.packets c packets) w kernelEnvelope (fun _ => 0)
    (active_zero c T hLayout) (input_colors c colors packets hColors)
    hw hEnvelope hQuiet hGas (fun x U => by
      rw [density, VariableScaling.read]
      exact hFactor (VariableScaling.tests c x) U)

end YM.Integration.FullQLocal.InputScaling
end
