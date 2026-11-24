import YM.WilsonMS.Stencil.WNames

/-!
# Tuning ledger for the Wick-compensated input

Keep even the canonical generator term in this proof. In using the High
infrastructure of the repo, need the `Caps` & eligibility argument of
`Menus` but for the Wick-compensated columns. The proof here parallels the
supplied calculations, not inferring estimates with the `W` parts omitted.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BMenu
open MS.Logarithm
open XSpace Function Filter Set Finset MeasureTheory
open MS MS.Local MS.Local.Physical MS.Plane MS.High MS.Book MS.Book.Convolve MS.Book.Program
open MS.Menus MS.Land MS.Koszul MS.Cylinder MS.Cylinder.Lab MS.Native MS.Native.Paint
  MS.Native.Wilsonian
open MS.Native.Studio MS.Lifting MS.Native.Sew MS.Native.Draft MS.Color MS.Swirl MS.Swirl.Near
open Lattice Corrected MS.Landau Detect Flux
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {d r : ℕ}

/-- Uniform hypotheses for a column recipe on through-horizon fields. A
single recipe at all orders, including the right grant on rank/dimensions. Weights
checked after the charged (Laurent) insertion convention. No hypothesis about
MS solutions here. Instantiated for both stencil systems. -/
structure BasisMenu (G : Gauge) where
  pre : {d : ℕ} → Team → Glyph (Ensure.deck G) d → ℝ → T (Dot G Cover)
  pre_ticks {j : ℕ} p (u : Glyph (Ensure.deck G) j) x (k : ℕ) : Tuned (pre p u x k) 0
  pre_flag {j : ℕ} p (u : Glyph (Ensure.deck G) j) x (k : ℕ) : Colorless (pre p u x k)
  pre_ready {j : ℕ} p (u : Glyph (Ensure.deck G) j) k : Ready (fun x => pre p u x k)
  pre_leg {j : ℕ} p (u : Glyph (Ensure.deck G) j) k (x : ℝ) : Limit (pre p u x k).val ((k : ℤ)+u.grade)
  pre_w {j : ℕ} p (u : Glyph (Ensure.deck G) j) x : G.Simple →
    Weightless (Spectrum G) (style G p x) (pre p u x)
  start {j : ℕ} p (u : Glyph (Ensure.deck G) j) x : Fits (pre p u x 0) u.read u.grade u.size false
  changeScale {j : ℕ} p (u : Glyph (Ensure.deck G) j) (x : ℝ) : pre p u x= car (Y p x) (pre (Stripped p) u x)

/-- The implicit BasisMenu of the primary construction. -/
instance : Coe (Initialize G) (BasisMenu G) where
  coe W := {
    pre := fun p u x => preambleW W p u x
    pre_ticks := pre_ticks W
    pre_ready := pre_ready W
    pre_leg := pre_leg W
    pre_w := pre_w W
    pre_flag := pre_flag W
    start := start W
    changeScale := changeScale W }

variable (W : BasisMenu G) (p : Team)
local notation "B" => Ensure.deck G
variable (u : Glyph (Ensure.deck G) d) (P : Acts (Ensure.deck G) d)
local notation "Γ" => Spectrum G

/-- for each output physical field at its horizon d, use the bare set *through*
this horizon; allowing mixing along Deck. The same table of glyphs and
canonical-primitive tickets as the MS proof. -/
def rentW (x : ℝ) (i : ℕ) :=
  ∑ g : Glyph B d, ∑ j ∈ Finset.antidiagonal i, oil P g j.1 x • W.pre p g x j.2

def scoreW (x : ℝ) : T (Dot G Cover) :=
  rentW W p P x + Menus.motto p P x

lemma circleRent : Circle G (rentW W p P) false 0
    where
  stance0 _ _ h := Bool.noConfusion h
  actual i
    x := Tune.sum _ fun g _ => Tune.sum _ fun j _ => (W.pre_ticks p g x j.2).cash _ (by simp [oil])
  settled i x := Colorless.csum _ fun i _ => Colorless.csum _ fun j _ => (W.pre_flag p i x j.2).smul _
  tag
    i :=
    value_sum _ fun g _ =>
      value_sum _ (fun j _ => pc_ready (c := oil P g j.1) ⟨_, Ready.got _, rfl⟩ (W.pre_ready p g j.2))
  room
    i :=
    ⟨i + d, fun x => by
      unfold rentW
      simp_rw [sum_stack]
      exact
        Limit.sum _
          (fun g _ =>
            Limit.sum _
              (fun j hj =>
                ((W.pre_leg p g j.2 x).smul _).up
                  (by
                    obtain he := Finset.mem_antidiagonal.mp hj
                    have hv := Glyph.memory g
                    omega)))⟩

lemma circleScore : Circle G (scoreW W p P) false 0
    where
  stance0 _ _ h := Bool.noConfusion h
  actual i x := ((circleRent W p P).actual i x).add (Menus.pretty p P x i)
  settled i x := ((circleRent W p P).settled i x).add (Menus.colorRoot p P x i)
  tag i := ((circleRent W p P).tag i).add (Menus.flows p P i)
  room
    i := by
    obtain ⟨k, hk⟩ := (circleRent W p P).room i
    refine ⟨k + i + fringe P i, fun x => ?_⟩
    exact Limit.add ((hk x).up (by omega)) ((Menus.stuff p P x i).up (by omega))

lemma stages (x : ℝ) :
    rentW W p P x =
      ∑ i : Glyph B d,
        pairW (LinearMap.lsmul ℂ (Dot G Cover)) (fun j => oil P i j x) (W.pre p i x) :=
  funext fun n => by
    rw [Finset.sum_apply]
    rfl

lemma mechanical (x : ℝ) : rentW W p P x = car (Y p x) (rentW W (Stripped p) P x) := by
  rw [stages, stages, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [W.changeScale p i, MS.Swirl.Near.oil_roll]

lemma untouched (h : G.Simple) (x : ℝ) : Weightless (Spectrum G) (style G p x) (rentW W p P x) := by
  let V := Dot G Cover
  let S := style G p x
  let D := actB (Spectrum G) + pairW (Spectrum G).touch S
  let J := pairW (LinearMap.lsmul ℂ V)
  have he c f : actB (Spectrum G) (J c f) = J c (actB (Spectrum G) f) := by
    funext n
    unfold actB J
    simp only [paired, promised, LinearMap.lsmul_apply, map_sum, map_smul]
  rw [stages]
  change D _ = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  let c := fun j => oil P i j x
  let f := W.pre p i x
  rw [show D (J c f) = J c (D f) from ?_, show D f = 0 from W.pre_w p i x h, map_zero]
  dsimp only [D, LinearMap.add_apply]
  rw [map_add,
    show pairW (Spectrum G).touch S (J c f) = J c (pairW (Spectrum G).touch S f) from Menus.olio ..,
    he]

lemma properShift (h : G.Simple) (x : ℝ) : Weightless (Spectrum G) (style G p x) (scoreW W p P x) := by
  let D := actB (Spectrum G) + blocks (Spectrum G) (style G p x)
  change D _ = 0
  rw [scoreW, map_add, show D (rentW W p P x) = 0 from untouched W p P h x]
  rw [show D (Menus.motto p P x) = 0 from
      steady_squares (style G p x) _ (main_law G p x h) (fun i => ((core_circle G p).actual i x).symm)
        (fun i => Tune.parity ((core_circle G p).actual i x) ghostParity)
        (fun i => ((P i).proof.actual x).symm),
    zero_add]

lemma retained (k : ℕ) (A : Acts B d) (H : ∀ i, i ≤ k → P i = A i) (x : ℝ) :
    scoreW W p P x k = scoreW W p A x k := by
  simp_rw [scoreW, Pi.add_apply, sky, rentW, H k k.le_refl]
  apply congr_arg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    unfold oil
    rw [H j.1
        (by
          obtain h := mem_antidiagonal.mp hj
          omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [H j.2
      (by
        obtain h := mem_antidiagonal.mp hj
        omega)]

variable {v : ℤ} {n : ℕ}

def light (Q : Price B d) (x : ℝ) : Dot G Cover :=
  ∑ g : Glyph B d, (↑((Q g).eval x) : ℂ) • W.pre p g x 0

lemma repair (Q : Price B d) (X : Menus.Power G) (n : ℕ) (x : ℝ) :
    scoreW W p P x n - scoreW W p (Menus.patch P Q X n) x n =
      light W p Q x + Menus.advance (X.input x) := by
  let S := Menus.patch P Q X n
  have hs (i : Glyph B d) :
    (∑ j ∈ antidiagonal n, (oil P i j.1 x - oil S i j.1 x) • W.pre p i x j.2) =
      (↑((Q i).eval x) : ℂ) • W.pre p i x 0 := by
    rw [Finset.sum_eq_single (n, 0)]
    · simp [oil, S, Menus.patch]
    · intro j hj hne
      obtain ht := mem_antidiagonal.mp hj
      have h : j.1 ≠ n := by
        intro hp
        exact
          (hne
              (Prod.ext hp
                (by
                  dsimp
                  omega))).elim
      simp_rw [oil, show S j.1 = P j.1 from patch_bef P Q X h, sub_self, zero_smul]
    simp
  rw [scoreW, scoreW, Pi.add_apply, Pi.add_apply, add_sub_add_comm, light]
  congr 1
  · unfold rentW
    simp_rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [← hs c]
    exact
      Finset.sum_congr rfl
        (fun k _ => (sub_smul (oil P c k.1 x) (oil S c k.1 x) (W.pre p c x k.2)).symm)
  have hc : (P n).proof.input x - (S n).proof.input x = X.input x := by
    simp [S, Menus.patch, Power.sub]
  rw [sky, sky, add_sub_add_comm, ← map_sub, hc, Menus.advance]
  congr 1
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (0, n)]
  · dsimp only
    rw [← map_sub, hc, style, whoZero]
  · intro j hj hne
    obtain h := mem_antidiagonal.mp hj
    have h' : j.2 ≠ n := fun g =>
      hne
        (Prod.ext
          (by
            dsimp
            omega)
          g)
    rw [patch_bef _ _ _ h', sub_self]
  simp

lemma shines {Q : Price B d} (h : Glyph.Homes Q v r) (x : ℝ) :
    Limit (light W p Q x).val r ∧ Fits (light W p Q x) (Glyph.valAt Q x) r v false := by
  refine ⟨?_, Fits.sum _ (fun i _ => ?_)⟩
  swap
  · by_cases he : Q i = 0
    · simp only [he, Polynomial.eval_zero, Complex.ofReal_zero]
      rw [zero_smul, zero_smul]
      exact Fits.zero _
    rw [← h.size i he, ← h.grade i he]
    exact (W.start p i x).smul _
  unfold light
  rw [sum_stack]
  refine Limit.sum _ fun c _ => ?_
  by_cases he : Q c = 0
  rw [he, Polynomial.eval_zero, Complex.ofReal_zero, zero_smul]
  exact fun _ _ => rfl
  rw [← h.grade c he]
  exact Limit.smul _ ((by simpa using W.pre_leg p c 0 x) : Limit (W.pre p c x 0).val c.grade)

structure Ability (P A : Acts B d) (n r : ℕ) (v : ℤ) (H : ℝ → Law G) : Prop where
  past (i : ℕ) : i < n → P i = A i
  size (x : ℝ) : Limit ((scoreW W p P x n) - (scoreW W p A x n)).val r
  jet (x : ℝ) : Fits ((scoreW W p P x n) - (scoreW W p A x n)) (H x) r v false

lemma room {F H : ℝ → Law G} (h : 0 ≤ v) (ht : v ≤ d) (hp : Ready F) (hq : Ready H)
    (hc : ∀ i, F i ∈ (B).carries v r) (hd : ∀ i, H i ∈ Lease G (v - 1) r (-1)) :
    ∃ (Q : Price B d) (X : Menus.Power G),
      Glyph.Homes Q v r ∧
        X.allowance = r ∧ Ability W p P (Menus.patch P Q X n) n r v (fun i => F i + natQ (H i)) := by
  obtain ⟨Q, hQ, hF⟩ := Glyph.offered h ht hc hp
  obtain ⟨X, hx, hX⟩ := pens hq hd
  have he (x : ℝ) :
    Limit (Menus.advance (X.input x)).val r ∧
      Fits (Menus.advance (X.input x)) (natQ (H x)) r v false :=
    estimateL x (hx ▸ X.ranks x) (hX x)
  refine ⟨Q, X, hQ, hx, ⟨fun i h => (patch_bef P Q X h.ne).symm, fun x => ?_, fun x => ?_⟩⟩ <;>
    rw [repair]
  exact (shines W p hQ x).1.add (he x).1
  rw [← hF x]
  exact (shines W p hQ x).2.add (he x).2

end YM.WilsonMS.BMenu
