import YM.Push.PRICE_COMPILER.Post

/-!
# Price book for all-order propagation

Clients may impose additional pre-block floors on the profiles (including neighbor costs),
post-block ceilings on theta, post-theta per-stage entrance/volume tests, and stretch prices.
Only tests of this dependency form; in using the constructor one must prove the `eventual...`
properties, not assume an arbitrary new comparison estimate can be priced this way.
In particular the price book is fixed in common, *before* issuing even one shot;
no dependence on future choices of history, ultraviolet cutoff N or period index p here.
No other role for Delays (V) is assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG04B
open Function Filter RG Lattice RG.Supply
open scoped Topology Matrix.Norms.Frobenius BigOperators

abbrev Pre (α : Type) := KernelChoices → (ℕ → Stage) → α
abbrev Ratios (α : Type) := Pre ((ℕ → Side) → α)
abbrev Post (α : Type) := Ratios ((ℕ → ℝ) → α)

/-- Stage-wise additional requests. `x` for `hat` is the hatted **inverse**
coupling `hatBeta` at the *coarse* level in the step with the given input stage
`j`. Test not just eventual at fixed cutoff -- it's uniform across the history,
including startup. `factor` L(j) is blocking m+1 to m when j=J(m+1). Later
entrances can ask additional conditions on physical scale. -/
structure Request where
  preLength : Pre (ℕ → ℕ)
  margin : Ratios (ℕ → ℝ)
  margin_pos k s L i : 0 < margin k s L i
  hat : Post (ℕ → ℝ → Prop)
  eventualHat k s L θ j : ∀ᶠ x in atTop, hat k s L θ j x
  scale : Post (ℝ → ℕ → ℝ → Prop)
  eventualScale k s L θ b j : ∀ᶠ x in atTop, scale k s L θ b j x
  shells : Post (ℕ → ℕ)
  growth : Post (ℕ → ℕ)
  depth : Post (ℝ → ℕ → ℝ)
  window : Post (ℝ → ℕ → ℝ → ℕ)
  sublin k s L θ b j : Tendsto (fun x : ℝ => (window k s L θ b j x : ℝ) / x) atTop (𝓝 0)
  minPer : Post (ℝ → ℕ)

def Request.none : Request := {
  preLength := fun _ _ _ => 0
  margin := fun _ _ _ _ => 1
  margin_pos := fun _ _ _ _ => zero_lt_one
  hat := fun _ _ _ _ _ _ => True
  scale := fun _ _ _ _ _ _ _ => True
  eventualHat := fun _ _ _ _ _ => Eventually.of_forall (fun _ => True.intro)
  eventualScale := fun _ _ _ _ _ _ => Eventually.of_forall (fun _ => True.intro)
  shells := fun _ _ _ _ _ => 0
  growth := fun _ _ _ _ _ => 0
  depth := fun _ _ _ _ _ _ => 0
  window := fun _ _ _ _ _ _ _ => 0
  sublin := fun _ _ _ _ _ _ => by simp
  minPer := fun _ _ _ _ _ => 0 }

def Request.combine (Q R : Request) : Request := {
  preLength := fun k s i => max (Q.preLength k s i) (R.preLength k s i)
  margin := fun k s L i => min (Q.margin k s L i) (R.margin k s L i)
  margin_pos := fun k s L i => lt_min (Q.margin_pos ..) (R.margin_pos ..)
  hat := fun k s L θ j x => Q.hat k s L θ j x ∧ R.hat k s L θ j x
  eventualHat := fun k s L θ j => (Q.eventualHat ..).and (R.eventualHat ..)
  scale := fun k s L θ b j x => Q.scale k s L θ b j x ∧ R.scale k s L θ b j x
  eventualScale := fun k s L θ b j => (Q.eventualScale ..).and (R.eventualScale ..)
  shells := fun k s L θ j => max (Q.shells k s L θ j) (R.shells k s L θ j)
  growth := fun k s L θ j => max (Q.growth k s L θ j) (R.growth k s L θ j)
  depth := fun k s L θ b j => max (Q.depth k s L θ b j) (R.depth k s L θ b j)
  window := fun k s L θ b j x => Q.window k s L θ b j x + R.window k s L θ b j x
  sublin := fun k s L θ b j => by
    simpa only [Nat.cast_add, add_div, add_zero] using
      (Q.sublin k s L θ b j).add (R.sublin k s L θ b j)
  minPer := fun k s L θ b => max (Q.minPer k s L θ b) (R.minPer k s L θ b) }

private theorem rollsThree {G : Gauge} (hG : G.Simple) (Q : Request) (p : Sheet G) :
    ∃ L : Rolls p, (∀ i, Q.preLength p.kernel p.profile i ≤ (L.L i).val) ∧
      (∀ j, ∃ n : ℕ, (L.L j).val = 3^n) := by
  choose M H using fun i => Rolls.eventually_large p hG i
  let B i := (Finset.range (i+1)).sup fun n => max (M n) (Q.preLength p.kernel p.profile n)
  let L (i : ℕ) : Side := ⟨3 ^ (B i+1), by positivity⟩
  have h (i) : max (M i) (Q.preLength p.kernel p.profile i) ≤ (L i).val :=
    (show _ ≤ B i from Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self _))).trans
      ((Nat.le_succ _).trans (Nat.lt_pow_self (by decide : 1 < 3)).le)
  let hL : Rolls p := ⟨L, fun j => H j _ ((le_max_left ..).trans (h j))
    ((show Odd (3:ℕ) from ⟨1,rfl⟩).pow), fun i j hij => pow_le_pow_right₀
      (by decide : 1 ≤ (3 : ℕ)) (Nat.add_le_add_right (Finset.sup_mono (Finset.range_mono (by omega))) 1)⟩
  exact ⟨hL, fun i => (le_max_right ..).trans (h i), fun i => ⟨_, rfl⟩⟩

lemma Request.factors {G : Gauge} (h : G.Simple) (Q : Request) (p : Sheet G) :
    ∃ L : Rolls p, (∀ i, Q.preLength p.kernel p.profile i ≤ (L.L i).val) ∧
      (∀ j, ∃ n : ℕ, (L.L j).val = 3^n) := rollsThree h Q p

variable {G : Gauge} (Q : Request) (a : Levels G)

set_option quotPrecheck false
local notation "S" => a.clock.stage
local notation "θ" => a.clock.theta
local notation "K" => a.clock.kernel
local notation "L" => a.clock.factor
local notation "b" => a.clock.bar
local notation "J" => a.clock.J

/-- The actual Levels have been bought to meet every clause. -/
structure Booked : Prop where
  pre i : Q.preLength K S i ≤ (L i).val
  three j : ∃ n : ℕ, (L j).val = 3^n
  shield i : θ i ≤ Q.margin K S L i
  hats m : Q.hat K S L θ (J (m+1)) (a.clock.hatBeta m)
  later m : J 0 < J (m+1) → Q.scale K S L θ b (J (m+1)) (a.S.scale m)
  periods p : Q.minPer K S L θ b ≤ (a.S.period p).val
  volumes m p : let j := J (m+1)
                Q.shells K S L θ j * (1+a.clock.coverSize m+a.clock.coverSize (m+1)) ^
                    Q.growth K S L θ j ≤ (a.S.side m p).val
  plateau j : J 0 ≤ j → ∃ k : ℕ,
    let w := Q.window K S L θ b j (a.S.scale k)
    Q.depth K S L θ b j ≤ a.S.scale k ∧ w ≤ k ∧
    ∀ m : ℕ, k - w ≤ m → m ≤ k + w → J m=j

variable {Q a}
/-- Extract multiple simultaneous orders of prices. -/
lemma Booked.components {R : Request} (h : Booked (Q.combine R) a) :
    Booked Q a ∧ Booked R a := by
  constructor
  · refine ⟨fun i => (le_max_left ..).trans (h.pre i), h.three,
      fun i => (h.shield i).trans (min_le_left ..), fun i => (h.hats i).1,
      fun i hi => (h.later i hi).1, fun i => (le_max_left ..).trans (h.periods i),
      fun i p => ?_, fun j hj => ?_⟩
    · intro s
      let n := 1+a.clock.coverSize i+a.clock.coverSize (i+1)
      apply le_trans _ (h.volumes i p)
      exact Nat.mul_le_mul (le_max_left ..) (pow_le_pow_right₀ (show 1 ≤ n from by unfold n; omega) (le_max_left ..))
    obtain ⟨k,hH,hU,hX⟩:=h.plateau j hj
    have hi : Q.window K S L θ b j (a.S.scale k) ≤ (Q.combine R).window K S L θ b j (a.S.scale k) := Nat.le_add_right ..
    exact ⟨k,(le_max_left ..).trans hH,hi.trans hU,fun m hl hm=> hX _ (by omega) (by omega)⟩
  refine ⟨fun i => (le_max_right ..).trans (h.pre i), h.three,
    fun i => (h.shield i).trans (min_le_right ..), fun i => (h.hats i).2,
    fun i hi => (h.later i hi).2, fun i => (le_max_right ..).trans (h.periods i),
    fun i p => ?_, fun j hj => ?_⟩
  · intro s
    let n := 1+a.clock.coverSize i+a.clock.coverSize (i+1)
    apply le_trans _ (h.volumes i p)
    exact Nat.mul_le_mul (le_max_right ..) (pow_le_pow_right₀ (show 1 ≤ n from by unfold n; omega) (le_max_right ..))
  obtain ⟨k,hH,hU,hX⟩:=h.plateau j hj
  have hi : R.window K S L θ b j (a.S.scale k) ≤ (Q.combine R).window K S L θ b j (a.S.scale k) := Nat.le_add_left ..
  exact ⟨k,(le_max_right ..).trans hH,hi.trans hU,fun m hl hm=> hX _ (by omega) (by omega)⟩

end YM.RG04B
