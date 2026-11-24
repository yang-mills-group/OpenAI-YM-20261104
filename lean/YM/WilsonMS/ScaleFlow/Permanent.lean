import YM.WilsonMS.Scales.DifferentialScale
import Mathlib.Analysis.Polynomial.Basic
/-!
# μ-invariance of the exact action re-expression

Within the pure-pole MS variable: reads at log μ-t use shifted coupling at the
top, still is EXACT scale transformation, not just up to cutoff corrections!
Derive from regulator convergence of the position re-expressions and
log-polynomiality. In particular probes are comparing the *bare* coupling
change origins literally, order by order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.RunBare
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Logarithm
open PowerSeries (coeff mk X C constantCoeff invOfUnit)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates FrameX Ice TraceMC GFlow
  Datum
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k n m j : ℕ}
local notation "BΨ" => Ensure.deck G
local notation "𝕄" => XSpace.Mesh
section reset
variable {P : ℝ → Cn}

lemma sense_len {I : Type} {f : I → ℝ} {l : Filter I} [l.NeBot] {Q : ℝ → ℝ} {j : ℝ} (h : Ready Q)
    (ht : Tendsto f l atBot) (hx : Tendsto (Q ∘ f) l (𝓝 j)) : Q = fun _ => j := by
  obtain ⟨p, rfl⟩ := h.scalar
  by_cases he : 0 < p.degree
  · obtain ht' := (Polynomial.abs_tendsto_atBot _ he).comp ht
    have hz : ∀ᶠ i in l, |p.eval (f i)| < |j| + 1 :=
      (continuous_abs.continuousAt.tendsto.comp hx).eventually (gt_mem_nhds (lt_add_one _))
    obtain ⟨i, hi, hv⟩ := (hz.and (ht'.eventually (eventually_gt_atTop (|j| + 1)))).exists
    exact False.elim (by exact (not_lt.mpr hi.le) hv)
  rw [Polynomial.eq_C_of_degree_le_zero (le_of_not_gt he)] at hx ⊢
  funext i
  rw [Polynomial.eval_C]
  exact
    tendsto_nhds_unique (f := fun _ => _) tendsto_const_nhds
      (show Tendsto (fun _ => _) l _ from hx.congr fun i => (Polynomial.eval_C ..))

lemma stead {I : Type} {f : I → ℝ} {l : Filter I} [l.NeBot] {Q : ℝ → ℂ} {j : ℂ} (h : Ready Q)
    (ht : Tendsto f l atBot) (hx : Tendsto (Q ∘ f) l (𝓝 j)) : Q = fun _ => j := by
  funext i
  apply Complex.ext
  exact
    congr_fun
      (sense_len (h.linear Complex.reLm) ht (Complex.continuous_re.continuousAt.tendsto.comp hx)) i
  exact
    congr_fun
      (sense_len (h.linear Complex.imLm) ht (Complex.continuous_im.continuousAt.tendsto.comp hx)) i

lemma cran {P : Team} (t : ℝ) : Aware (shift P t) :=
  ⟨Program.share .., Program.ann .., copy_clean _ _⟩

lemma θ_tick (P : Team) : speed (shift P) := by
  intro n
  obtain ⟨V, hV, he⟩ := shiftR P n
  rw [he]
  exact hV.linear Complex.ofRealLI.toLinearMap

lemma polynomial_inv (h : speed P) (hp : ∀ i, Aware (P i)) : speed (fun i => Ice.Counter (P i)) := by
  intro n
  let Γ (i : ℝ) := Ice.Counter (P i)
  have hγ (i : ℝ) : Aware (Γ i) := (hp i).counter
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases lt_or_ge 0 n with ht | ht
    swap
    · rw [Nat.eq_zero_of_le_zero ht]
      simp_rw [show ∀ i : ℝ, coeff 0 (Ice.Counter (P i)) = 0 from fun i => (hγ i).root]
      exact Ready.const _
    have hz (i : ℝ) :
      coeff n (Γ i) =
        coeff n PowerSeries.X - ∑ j ∈ (Finset.Iic n).erase 1, cut (Γ i) j n * coeff j (P i) := by
      rw [show _ = _ from
          Counter_next (hp i).root
            (by
              rw [(hp i).paid]
              norm_num)
            (Nat.ne_of_gt ht),
        (hp i).paid, div_one]
    have hh (i j : ℕ) (hj : j < n) : Ready (fun v => cut (Γ v) i j) := by
      induction i generalizing j with
      | zero =>
        simp_rw [cut, pow_zero]
        exact Ready.const _
      | succ i hg =>
        unfold cut
        simp_rw [pow_succ, PowerSeries.coeff_mul]
        exact
          accounts _
            (fun v hv =>
              (hg _ (by
                      obtain h := Finset.mem_antidiagonal.mp hv
                      omega)).pair
                (Algebra.lmul ℝ ℂ).toLinearMap
                (ih _
                  (by
                    obtain hh := Finset.mem_antidiagonal.mp hv
                    omega)))
    change Ready (fun i => coeff n (Γ i))
    simp_rw [hz]
    refine
      Ready.sub (Ready.const _)
        (accounts _ (fun u hu => Ready.pair (Algebra.lmul ℝ ℂ).toLinearMap ?_ (h u)))
    obtain ⟨he, hM⟩ := Finset.mem_erase.mp hu
    cases u with
    | zero =>
      simp_rw [cut, pow_zero]
      exact Ready.const _
    | succ k =>
      unfold cut
      simp_rw [pow_succ, PowerSeries.coeff_mul]
      refine accounts _ fun a ha => ?_
      obtain H := Finset.mem_antidiagonal.mp ha
      by_cases h1 : a.1 = n
      rw [show a.2 = 0 from (by omega)]
      simp_rw [show ∀ i : ℝ, coeff 0 (Γ i) = 0 from fun i => (hγ i).root, mul_zero]
      exact Ready.const _
      by_cases h2 : a.2 = n
      rw [show a.1 = 0 from (by omega)]
      simp_rw [show ∀ i : ℝ, coeff 0 ((Γ i) ^ k) = 0 from fun i => blocked (hγ i |>.root) (by omega),
        zero_mul]
      exact Ready.const _
      exact (hh k a.1 (by omega)).pair (Algebra.lmul ℝ ℂ).toLinearMap (ih _ (by omega))
variable {F Q : 𝕄 → Cn} {T V : Cn}

lemma spin (h : Tracks F T) (hv : Tracks Q V) (ht : ∀ i, Rooted (Q i)) (hx : Rooted V) :
    Tracks (fun i => (F i).subst (Q i)) (T.subst V) := by
  intro n
  simp_rw [usePool hx, usePool (ht _)]
  exact Fast.p_sum _ (fun i _ => Fast.mul (Coast hv i n) (h i))
end reset
section μ
variable {K : Store G} (V : Rose.Pick K) {W : Initialize G} {A : Prescription (Ensure.deck G)}
  {B : Booked (Ensure.deck G)} {F : MS_Data G B} (g : G.Simple) (hA : Installed W F A)
  (hc : Commuting A) (x t : ℝ)
local notation "σ" => A.team
include V g hA hc
set_option quotPrecheck false

lemma way : muFlow V F t = (Counter (χMS 0 V F)).subst (χMS (-t) V F) := by
  let p := χMS 0 V F
  let v := ψW V F
  let r := χMS (-t) V F
  unfold muFlow transit
  rw [Ice.assoc (ψ_aware V g hA hc).root (awareχ V g hA hc 0).root, (awareχ V g hA hc 0).unravel,
    eraser]

lemma baked : Program.shift A.team (x - t) = (Program.shift A.team x).subst (muFlow V F t) := by
  rw [way V g hA hc]
  let q (u : ℝ) := pι A u
  let L (i) := Vine V W A 0 i
  let U (i) := Vine V W A (-t) i
  let F' (i : ℝ) := PowerSeries.subst (Program.shift σ (i - t)) (Counter (Program.shift σ i))
  let a := χMS 0 V F
  let R := χMS (-t) V F
  let S := PowerSeries.subst R (Counter a)
  have hs : speed F' := by
    unfold F'
    refine speed.reexpress (polynomial_inv (θ_tick σ) (fun i => cran i)) ?_ (fun i => share A.team _)
    intro n
    exact
      coord_apply (r := (fun i : ℝ => i - t))
        (by
          have hx : Ready (fun x : ℝ => x) := (by simpa using Ready.got Polynomial.X)
          exact hx.sub (Ready.const _))
        (θ_tick σ n)
  have hx : ∀ᶠ i in Front, ((Counter (L i)).subst (U i)) = F' (-height i) := by
    filter_upwards [Rose.usable W V g] with i hi
    let c := Rose.chosen W V i
    let D := q (-t) i
    let H := q 0 i
    have hH : Aware H := cran _
    have hU : Rooted (U i) := FrameX.vine_roots V W A (-t) i
    have hv : L i = c.subst H := rfl
    have he : coeff 1 (L i) ≠ 0 := by
      rw [hv, tangential _ hH.root hH.paid]
      exact hi
    have hL : Rooted (L i) := FrameX.vine_roots V W A 0 i
    have hT : F' (-height i) = (Counter H).subst D := by
      unfold F' H D q pι
      rw [show -height i - t = -t - height i from (by abel), zero_sub]
    rw [hT]
    apply
      separate hL he (show Rooted _ from (root_sub _ _ hU).trans (born _))
        (show Rooted _ from (root_sub _ _ (cran (P := σ) (-t - height i)).root).trans (born _))
    rw [← Ice.assoc (born _) hU, counter_l hL he, PowerSeries.subst_X (Worried hU), hv,
      Ice.assoc hH.root (by exact (hH.counter.extend (cran (P := σ) _)).root), ←
      Ice.assoc hH.counter.root ((show Aware D from cran _).root), hH.undo,
      PowerSeries.subst_X (Worried (show Aware D from cran _).root)]
    rfl
  have ht : F' x = S := by
    apply PowerSeries.ext
    intro i
    apply congr_fun (?_ : (fun c => coeff i (F' c)) = (fun _ => coeff i S)) x
    refine stead (hs i) (tendsto_neg_atBot_iff.mpr (attained frontier)) ?_
    refine
      (spin (back_marks V W A F 0 g hA hc) (tracked (-t) V W A F g hA hc) (vine_roots V W A _)
              (awareχ V g hA hc _).root i |>.limit).congr'
        (hx.mono fun j hj => congr_arg (coeff i) hj)
  have hp : Aware (shift σ (x - t)) := cran _
  change _ = (shift σ x).subst S
  rw [← ht]
  unfold F'
  rw [← Ice.assoc (born _) hp.root, (cran (P := σ) x).undo, PowerSeries.subst_X (Worried hp.root)]
end μ
end YM.WilsonMS.RunBare
