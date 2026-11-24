import YM.WilsonMS.Columns.LeaderChoice
import YM.WilsonMS.Calibration.TacticsW
/-!
# Bare columns: valence-parity correspondence

Strengthen Fits with same-grade parity of all slot towers, including *shifted
Haar*, free Wick admission, and local canonical paths. (Local block here for
one input mark; products are compared coefficientwise.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.LoopRank
open Function Filter Finset Set MeasureTheory Real
open scoped Topology ContDiff BigOperators
section spolia
open XSpace Lattice RG Source Labels Maxwell Maxwell.Free Wilson Next.Rank.Normal
open MvPolynomial Finsupp Corrected
open scoped Classical Pointwise
variable {G : Gauge} {H : Source.Hol G} {d r k : ℕ} (A : Survey G H d)
variable {I : Type} {p q : poly I} {b : I →₀ ℕ}

abbrev green (r : ℕ) : Submodule ℂ (poly I) :=
  restrictSupport ℂ (setOf (fun x => Allows r (weight (fun _ => 1) x)))

lemma bush (p : poly I) : p ∈ green k ↔ ∀ i ∈ p.support, Allows k (weight (fun _ => 1) i) :=
  mem_restrictSupport_iff ..

lemma expand_x (h : p ∈ green k) (i : I) : X (R := ℂ) i * p ∈ green (k + 1) := by
  apply (bush _).mpr
  intro j hj
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hj)
  rw [support_X] at hx
  rw [map_add, Finset.mem_singleton.mp hx, Finsupp.weight_single, one_smul, add_comm 1]
  exact ((bush _).mp h y hy).sum (Allows.equal 1)

lemma cut_rank (L : I → ℂ) (p : poly I) (h : p ∈ green k) : slit L p ∈ green (k + 1) := by
  have hx : (slit L) p = ∑ i ∈ p.support, (slit L) (monomial i (MvPolynomial.coeff i p)) := by
    rw [← map_sum, ← as_sum p]
  rw [hx]
  apply Submodule.sum_mem
  intro i hi
  rw [slit, MvPolynomial.mkDerivation_monomial, Finsupp.sum]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro j hj
  rw [smul_eq_mul, mul_comm, MvPolynomial.C_mul']
  apply Submodule.smul_mem
  apply (bush _).mpr
  intro j' hh
  rw [Finset.mem_singleton.mp (support_monomial_subset hh)]
  obtain hz := ((bush p |>.mp h) i hi).sum (Allows.equal 1)
  have hv : single j 1 ≤ i := single_le_iff.mpr (by exact Nat.pos_of_ne_zero (mem_support_iff.mp hj))
  rw [← tsub_add_cancel_of_le hv] at hz
  rw [map_add, weight_single, one_smul] at hz
  exact Allows.down hz

lemma functorial (Q : Next.Rank.Normal.Symmetric I)
    (h : IsWeightedHomogeneous (fun _ => (1 : ℕ)) p k) : milk Q p ∈ green k := by
  have he (x : I →₀ ℕ) (z : ℂ) : milk Q (monomial x z) ∈ green (weight (fun _ => 1) x) := by
    apply Extra.FD.per_factor x
    · change milk Q (C z) ∈ _
      rw [fine]
      exact (bush _).mpr fun i ht => (mem_singleton.mp (support_monomial_subset ht)) ▸ Allows.equal _
    intro w i hh
    rw [monomial_add_single, pow_one, mul_comm (monomial w z), feeds, map_add, weight_single,
      one_smul]
    exact Submodule.add_mem _ (expand_x hh i) (cut_rank (Q.cov i) _ hh)
  rw [p.as_sum, map_sum]
  exact Submodule.sum_mem _ fun i hi => (h (MvPolynomial.mem_support_iff.mp hi)) ▸ (he i _)

lemma parity_count (p : Label G d) (h : p ∈ Labels.Grade (d, r)) :
    (A.insertW (-1) p).val - p.val ∈ green r := by
  have hx : IsWeightedHomogeneous (fun _ => (1 : ℕ)) p.val r := by
    intro i hi
    obtain hv := (pure_grade _ _) |>.mp h hi
    rw [weight_slot] at hv
    rw [rank_le]
    exact congr_arg Prod.snd hv
  exact
    Submodule.sub_mem _ (functorial _ hx)
      ((bush p.val).mpr fun i hi => by
        rw [hx (MvPolynomial.mem_support_iff.mp hi)]
        exact Allows.equal r)

lemma par_seal (p : Label G d) (hp : p ∈ Labels.Grade (d, r)) (i k : ℕ) (hv : ¬Allows r k) :
    exactPart A p i k = 0 := by
  let v := A.insertW (-1) p - p
  apply Subtype.ext
  change Labels.piece (i, k) v.val = 0
  apply MvPolynomial.ext
  intro j
  unfold Labels.piece
  rw [coeff_weightedHomogeneousComponent, MvPolynomial.coeff_zero]
  split
  swap
  · rfl
  rename_i hj
  rw [weight_slot] at hj
  by_contra hz
  obtain he := (bush _ |>.mp (parity_count A p hp)) j (MvPolynomial.mem_support_iff.mpr hz)
  rw [rank_le] at he
  obtain hM := congr_arg Prod.snd hj
  simp only at hM
  rw [hM] at he
  exact hv he
end spolia
section gear
open MS
open Plane Koszul Heat Flux Landau Lattice Tone Momentum Frame Wire Color Detect Native
  Native.Wilsonian Paint Book Convolve City Logarithm Program Signal
open Cylinder Lab Taylor Draft Orientation Local.Physical High Knobs Wind Menus Lifting BMenu
variable {G : Gauge} {i j k r d : ℕ} {v : ℤ}
local notation "B" => Ensure.deck G

lemma piecesP (W : XSpace.Initialize G) (J : Glyph B d) (u : ℕ) :
    pays (u + J.grade) ((vertices W J) u).val := by
  have h (a i : ℕ) (f : Dot G Cover) : pays (a + i) (Book.levels i f a).val :=
    LoopRank.full
      (by
        rw [Nat.cast_add]
        exact rankMod f.val _)
  unfold vertices
  rw [Pi.add_apply]
  apply sum (h u _ _)
  rw [Finset.sum_apply, sum_stack]
  refine sums _ fun i _ => ?_
  by_cases hp : Allows J.grade i.2.val
  · exact higher ((Allows.equal u).sum hp) (h u _ _)
  rw [atom, further, par_seal _ _ (dataHere _) _ _ hp]
  change pays _ (Book.levels i.2.val (Webs.symbol _ 0) u).val
  rw [show (0 : Labels.Pol G) = MvPolynomial.C 0 from (map_zero _).symm, Webs.symbol_C]
  have he : piece (A := LightMode G Cover) (0 : ℂ) = 0 := by
    apply Subtype.ext
    funext l
    cases l <;> rfl
  rw [he]
  intro l _
  change Book.mask _ (0 : Raw _ ℂ) l = 0
  rw [map_zero]
  rfl

lemma rank_φ {P : Team} (he : Valid P) (W : XSpace.Initialize G) (x : ℝ) (J : Glyph B d) (n : ℕ) :
    pays (n + J.grade) (preambleW W P J x n).val :=
  wob_grade x he (piecesP W J) n

variable {F H : Dot G Cover}

private abbrev near1 (F : Dot G Cover) (r : ℕ) : Prop :=
  ∀ w, ¬Allows r (List.length w + 1) → F.val w = 0

private lemma dyed1 (z : Bool) (h : near1 F k) : near1 (twisted DotFlip z F) k := by
  intro l hp
  rw [twistp, at_sign, h l hp, mul_zero]

private lemma visitor (h : near1 F k) (p : Cover) : near1 (Lab.Shift p F) k := by
  intro l hp
  nth_rw 1 [← enough (F := (Lab.Shift p F).val) (h := (l.length : ℤ)) l rfl]
  change Book.mask _ (shade _ F) l = 0
  rw [← mod_ink, show Book.model l.length F = 0 from ?_, map_zero]
  rfl
  apply Subtype.ext
  ext u
  by_cases he : (u.length : ℤ) = l.length
  exact (enough (F := F.val) u he).trans (h u (by rwa [show u.length = l.length from by omega]))
  exact strange u he

private lemma cards (he : near1 F i) (ht : near1 H j) (hx : i + j = k + 2) :
    pays k (couple DotFlip F H).val := by
  rw [coupled]
  intro w hv
  rw [scattered, scatter_congr _ w _ (fun _ _ => (0 : ℂ)) ?_]
  exact map_zero (allocate ..)
  intro u v ht'
  obtain hy := split_length ht'
  by_cases hh : Allows i (u.length + 1)
  swap
  · rw [he u hh, zero_mul]
  have hz : ¬Allows j (v.length + 1) := fun h' =>
    hv
      (by
        apply Allows.linear (c := 2)
        convert hh.sum h' using 1 <;> omega)
  rw [ht v hz, mul_zero]

private lemma starter (h : pays k F.val) (i : Branch G Axis) (x : Cover) : near1 (force i x F) k := by
  obtain ⟨p, hp⟩ := obliges F
  rw [force_at F hp]
  intro u hv
  rw [sum_stack, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  exact visitor (k := k) (F := enter (i, j) F) (fun l he => h ((i, j) :: l) he) (x - j) u hv

lemma Lap_φ (hf : pays i F.val) : pays i ((Spectrum G).Lap F).val := by
  rw [Bonded.lap_at, sum_stack]
  refine sums _ (fun y _ => scales ?_ _)
  obtain ⟨s, hs⟩ := obliges F
  rw [heart_by _ _ F hs, sum_stack]
  exact sums _ fun j _ => fun l hp => hf _ (fun h => hp h.down)

lemma touch_φ (hf : pays i F.val) (hh : pays j H.val) (ht : i + j = k + 2) :
    pays k ((Spectrum G).touch F H).val := by
  obtain ⟨s, hs⟩ := obliges H
  rw [Bonded.touching, sum_stack]
  refine sums _ (fun v _ => scales ?_ _)
  rw [root_at F H _ _ hs, sum_stack]
  refine sums _ fun i' _ => ?_
  rw [spot_eq]
  exact
    sum (cards (dyed1 _ (starter hf _ _)) (fun l hl => hh _ hl) ht)
      (cards
        (starter
          (show pays i (sign DotFlip _ F.val) from fun l hp => by rw [at_sign, hf l hp, mul_zero]) _
          _)
        (fun l hl => hh _ hl) ht)

structure Controlled (r : ℕ) (X : Tact B d) : Prop where
  support (g : Glyph B d) : X.register g ≠ 0 → Allows r g.grade
  auxiliary (x : ℝ) : pays r (X.proof.input x).val

structure RankBudget (W : BasisMenu G) : Prop where
  rank_φ {p : Team} (h : Valid p) (x : ℝ) {d : ℕ} (J : Glyph B d) (n : ℕ):
    pays (n + J.grade) (W.pre p J x n).val

lemma primaryRank (W : XSpace.Initialize G) : RankBudget (↑W : BasisMenu G):= ⟨by
  intro p h x d J n; exact rank_φ h W x J n⟩

lemma score_b (W : BasisMenu G) (hR : RankBudget W) {p : Team} (he : Valid p) (F : Acts B d) (r : ℕ)
    (hp : ∀ i, Controlled (i + r) (F i)) (x : ℝ) (n : ℕ) : pays (n + r) (scoreW W p F x n).val := by
  rw [scoreW, Pi.add_apply]
  apply sum
  · unfold rentW
    rw [sum_stack]
    refine sums _ fun j _ => ?_
    rw [sum_stack]
    refine sums _ fun i hi => ?_
    by_cases H : (F i.1).register j ≠ 0
    swap
    · rw [oil, not_not.mp H, Polynomial.eval_zero, Complex.ofReal_zero, zero_smul]
      exact fun _ _ => rfl
    exact
      higher (i := i.2 + j.grade)
        (by
          convert (Allows.equal i.2).sum (hp i.1 |>.support j H) using 1
          obtain ht := mem_antidiagonal.mp hi
          omega)
        (scales (hR.rank_φ he x j i.2) _)
  rw [sky]
  refine sum (Lap_φ ((hp n).auxiliary x)) ?_
  rw [sum_stack]
  exact
    sums _ fun i hi =>
      touch_φ (style_valid x he i.1) ((hp _).auxiliary x)
        (by
          obtain he := mem_antidiagonal.mp hi
          omega)
end gear
end YM.WilsonMS.LoopRank
