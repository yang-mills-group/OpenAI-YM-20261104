import YM.WilsonMS.Scales.LogRails
/-!
# Log-polynomial dependence, actual MS construction, all positions in compact

Along arrows of the parameter log(μ), `Ready`: coefficient at each
finite perturbative order is a polynomial in this parameter. For separated
amplitudes, use the supplied *existence* to the infrared; no uniformity in μ
needed there, since a uniform log-degree budget can be transported to
infinity by evaluating at finitely many scales.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.TraceMC
open Function Set Filter MeasureTheory Real Finset Metric
open MS MS.Plane MS.Latch MS.Latch.Job MS.Koszul MS.Landau MS.Landau.Detect MS.Land
open MS.Rake MS.Orbit MS.Vane MS.Heat MS.Tone MS.City MS.Book MS.Dock MS.Emit MS.Outlook
open MS.Local.Physical MS.Osc MS.Osc.Snap MS.Tide MS.Dial MS.Logarithm Wire Belt Geo Flux
open scoped Topology Classical
variable {G : Gauge} {I W : Type} {A : Deck G} {M : Booked A} {n m k : ℕ}
open MS.Train
variable {F H : Glade G (Rates I)} {L : MS_Data G M} {Y : W → Label A} {ψ : Position W I}
variable [LinearOrder W] {U : Rake.Dance G (Rates I) W} {S R : Finset W}

abbrev plain (I : Type) : Geo (Rates I) :=
  ⟨0, fun p => p.1, fun _ => le_rfl⟩

abbrev awayC (P : Position W I) : Position W (Rates I) := fun w x => P w x.2

omit [LinearOrder W] in
lemma copy_mesh (h : Mesh (frameF I 0) ψ) : Mesh (plain I) (awayC ψ) := by
  intro i j hi
  obtain ⟨⟨C, hC, hV⟩, A, hA, h⟩ := h i j hi
  exact ⟨⟨C, hC, fun p => hV p.2⟩, ⟨A, hA, fun p => h p.2⟩⟩

omit [LinearOrder W] in
lemma plain_all (h : Mesh (frameF I 0) ψ) (μ : ℝ) : Mesh (frameF I μ) ψ := fun i j hi => by
  obtain ⟨⟨C, hC, hV⟩, A, hA, h⟩ := h i j hi
  exact ⟨⟨C, hC, hV⟩, ⟨A, hA, h⟩⟩

variable (ht : Mesh (frameF I 0) ψ) (h : DOrd M (plain I) L Y (awayC ψ) U)
include h

omit [LinearOrder W] h in
private lemma log_item (v : Label A) (n : ℕ) : Ready (along (rowM (plain I) L v n)) := by
  let L' : (ℝ → Law G) →ₗ[ℝ] (I → ℝ → Law G) := LinearMap.pi fun _ => LinearMap.id
  exact (show Ready _ from Outlook.plant (Host.host (Dock.gang (L.markOK v.h v.item n)))) |>.linear L'

omit [LinearOrder W] h in
private lemma log_bulk (n : ℕ) : Ready (along (approach (plain I) L n)) := by
  let L' : (ℝ → Law G) →ₗ[ℝ] (I → ℝ → Law G) := LinearMap.pi fun _ => LinearMap.id
  exact (show Ready _ from Outlook.plant (Host.host (Dock.gang (L.bulkOK n)))) |>.linear L'

def stillK (μ : ℝ) (U : Rake.Dance G (Rates I) W) :=
  copy (fun i => (μ, i)) U

lemma log_copy (μ : ℝ) : DOrd M (frameF I μ) L Y ψ (stillK μ U) :=
  valid_copy _ h (fun i => (μ, i)) (fun _ => rfl)
set_option quotPrecheck false
local notation "μ0" => (fun _ : Rates I => planeF)
local notation "Z0" => Geo.constantP G (Rates I) (PlanetD G)

omit ht h in
lemma sumsP {X : Type} (A : Finset X) (F : X → Glade G (Rates I)) (H : ∀ i ∈ A, Ready (along (F i))) :
    Ready (along (∑ i ∈ A, F i)) := by
  obtain h := Ready.sums A H
  suffices he : along (∑ i ∈ A, F i) = ∑ i ∈ A, along (F i) from he.symm ▸ h
  funext i p j
  simp [along, Finset.sum_apply]
include ht

lemma S_poly (hp : ∀ i ∈ picks S, ∀ n, Ready (along (U i n)) ∧ Ready (along (U (S \ i) n)))
    (hx : ∀ i < n, Ready (along (U S i))) :
    Ready (along (Src (awayC ψ) μ0 Z0 Z0 (approach (plain I) L) U S n)) := by
  refine
    Ready.add (f := along _)
      (sumsP (Domain.paths n 0) (fun i => expJ Z0 _ _) fun i hi =>
        tree_g (log_bulk (L := L) _) (hx i ((Finset.mem_Ico.mp hi).2)))
      (sumsP (picks S) _ fun i hi => sumsP (antidiagonal n) _ fun j hj => ?_)
  obtain ⟨hr, h1, h2, h3⟩ := n_small hi
  have hs := h1.mono hr.le
  let x := (rootX ψ i - rootX ψ S)
  have he : rootX (awayC ψ) i - rootX (awayC ψ) S = x ∘ Prod.snd := by
    unfold x rootX
    simp only [dif_pos h1, dif_pos hs]
    rfl
  rw [he]
  apply polyp_in (hp i hi j.1 |>.1) (hp i hi j.2 |>.2)
  rintro ⟨s, p⟩ t
  exact Climb.allSat (plain_all ht s) (log_copy h s) h1 h2 _ _ p t _

lemma grew (s : Finset W) (n : ℕ) : Ready (along (U s n)) := by
  obtain hv := builder L (copy_mesh ht) Y
  induction s using Finset.strongInductionOn generalizing n with
  | _ s ih =>
    obtain hp | hs := s.eq_empty_or_nonempty
    · rw [hp, h.1]
      exact Ready.zero
    by_cases hu : 2 ≤ s.card
    swap
    · obtain ⟨w, he⟩ :=
        Finset.card_eq_one.mp
          (show s.card = 1 from
            (by
              obtain he := Finset.card_pos.mpr hs
              omega))
      rw [he, h.2.1]
      exact log_item (Y w) n
    induction n using Nat.strong_induction_on with
    | h n hN =>
      obtain hh := h.2.2 s hu n
      let Q := U s n
      let F := Src (awayC ψ) μ0 Z0 Z0 (approach (plain I) L) U s n
      obtain ⟨k, hk⟩ : collect Q := hh.1
      have hB : Ready (along F) :=
        S_poly ht h (fun i hi t => ⟨ih i (n_small hi |>.1) _, ih _ (n_small hi |>.2.2.2) _⟩) hN
      have he (j : ℕ) : allLn (fun w => k < j + w.length) Q := by
        induction j with
        | zero =>
          unfold allLn
          have he (μ : ℝ) (p : I × ℝ × { l : Tℓ G // k < 0 + l.length }) :
            Q (μ, p.1) p.2.1 p.2.2.val = 0 :=
            hk _ _ _
              (by
                obtain ht := p.2.2.property
                omega)
          simp_rw [he]
          exact Ready.const _
        | succ j ih =>
          have hC : allLn (fun w => k < j + 1 + w.length) (sailP μ0 Z0 Q) :=
            cost_Θ (fun ⟨x, p⟩ t => Climb.allCycle (plain_all ht x) (log_copy h x) hs _ p t) ih
              (fun i j w hw =>
                (by
                  simp only [List.length_cons]
                  omega))
          rw [show Q = _ from hh.2.2]
          exact TraceMC.integral (all_add hC (above hB)) hh.2.1
      exact complete (he (k + 1)) (fun l => by omega)

lemma shore (i : Finset W) (hi : i.Nonempty) (n : ℕ) (x : Rates I) : Allow (U i n) x :=
  (reports _ (copy_mesh ht) h hi n).1 x

lemma read_book (s : ℝ) (p : I) (X : Finset W) (n : ℕ) :
    Vane.blade (U X n) (s, p) = Dial.book L Y s (pointI ψ p) X n :=
  Point_t L Y s (plain_all ht s) (log_copy h s) ..

lemma highP (s : Finset W) (n : ℕ) : Ready (fun v => fun p : I => Dial.book L Y v (pointI ψ p) s n) := by
  let f (v : ℝ) (p : I) := Vane.blade (U s n) (v, p)
  simp_rw [← read_book ht h]
  obtain hs | ht' := s.eq_empty_or_nonempty
  · subst s
    rw [h.1]
    simp_rw [Pi.zero_apply, (Fleet.allow_zero (G := G) _).2]
    exact Ready.const _
  obtain ⟨R, H⟩ := grew ht h s n
  have hv : f = evaluate R f := by
    funext a x
    obtain hz := shore ht h s ht' n (a, x)
    apply tendsto_nhds_unique hz
    have hK (t : ℝ) :
      U s n (a, x) t [] = ∑ i ∈ Finset.range R, (plate R i).eval a • U s n ((i : ℝ), x) t [] := by
      have H := congr_fun (congr_fun (congr_fun (interpret H a) x) t) []
      simp only [along, evaluate, Finset.sum_apply, Pi.smul_apply] at H
      exact H
    simp_rw [hK]
    rw [evaluate, Finset.sum_apply]
    exact tendsto_finsetSum _ fun i _ => (shore ht h s ht' n ((i : ℝ), x)).const_smul _
  change Ready f
  exact hv.symm ▸ eval_ready R f
omit ht h
open Puff Actors Puff.Mom Puff.SplitP

lemma pricedM {f g : ℝ → I → Finset W → Convolve.T ℂ}
    (hf : ∀ i n, Ready (fun v => fun p => f v p i n))
    (hg : ∀ i n, Ready (fun v => fun p => g v p i n)) (s : Finset W) (n : ℕ) :
    Ready (fun v => fun p => (Trunk.stack (marked W)).core (f v p) (g v p) s n) := by
  let T i n := fun (x : ℝ) (p : I) => f x p i n
  let Q i n := fun (x : ℝ) (p : I) => g x p i n
  change Ready (fun v => fun p => (∑ d ∈ subs s, Trunk.core (f v p d.1) (g v p d.2)) n)
  simp_rw [Finset.sum_apply]
  let K := Algebra.lmul ℝ (I → ℂ)
  have hx :
    ∀ A : Finset (W), ∀ i : Finset W, ∀ n m : ℕ, Ready (fun v => fun p => T A n v p * Q i m v p) :=
    fun i j n m => Ready.pair K.toLinearMap (hf i n) (hg j m)
  convert
    Ready.sums (subs s)
      (fun d hd => Ready.sums (Finset.antidiagonal n) (fun v _ => hx d.1 d.2 v.1 v.2)) using
    1
  funext i p
  simp only [Finset.sum_apply]
  rfl

lemma letSun {f : ℝ → I → Finset W → Convolve.T ℂ} (hv : ∀ i n, Ready (fun v => fun p => f v p i n))
    (s : Finset W) (n : ℕ) : Ready (fun t => fun i => bouquet (f t i) s n) := by
  have he (r : ℕ) : ∀ i j, Ready (fun v => fun p => (Trunk.stack (marked W)).power (f v p) r i j) := by
    induction r with
    | zero =>
      intro i j
      unfold Actors.power
      exact Ready.const _
    | succ r ih => exact pricedM hv ih
  let A := fun t i => bouquet (f t i) s n
  unfold bouquet Cheer Actors.cheers
  simp_rw [Finset.sum_apply]
  convert
    Ready.sums _
      (fun i _ =>
        (he i s n).linear ((LinearMap.mulLeft (I → ℂ) (fun _ => phase i)).restrictScalars ℝ)) using
    1
  funext v p
  simp only [Finset.sum_apply]
  rfl
include ht

lemma letLog (F : MS_Data G M) (y : W → Rake.Label A) (s : Finset W) (n : ℕ) :
    Ready (fun v => fun i => Dial.tour F y v (pointI ψ i) s n) := by
  obtain ⟨U, he⟩ := Vane.formal (builder F (copy_mesh ht) y)
  exact letSun (f := fun v i => Dial.book F y v (pointI ψ i)) (highP ht he) s n
end YM.WilsonMS.TraceMC
