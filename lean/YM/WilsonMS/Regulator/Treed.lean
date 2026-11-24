import YM.WilsonMS.Regulator.PublicRead
import YM.WilsonMS.Regulator.Pillars
import YM.XSpace.Carpet
/-!
# Point coefficients in the aligned columns and their regulator bounds

Packets with all amending column changes suitable for MS result in the *same*
moments as the `photo` sampling convention, with translated geometry. And
separated stencil-position costs inherit the MS rate on that geometry. This
version estimates PT coefficients with the marks already reparametrized and
basis-shifted.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.VisitH
open Function Set Filter MeasureTheory Real Finset
open MS MS.Latch MS.Latch.Job MS.Tone MS.Landau MS.Landau.Detect MS.Plane MS.Land MS.Koszul MS.Book
  MS.Book.Convolve MS.Menus
open MS.Theater MS.Tide MS.Dial MS.High MS.Rake MS.Orbit MS.Fleet MS.Vista MS.Vane
open MS.Local.Physical Lattice XSpace XSpace.Expense Schedule BMenu Fiscal
open XSpace.Cirrus Rake.Geo MS.Osc.Snap
open PowerSeries (coeff)
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {n d : ℕ} {W I : Type} [LinearOrder W]
section flags
variable {B : Deck G} {M : Booked B} (F : MS_Data G M) {x : Position W I} (p : W → Label B)
variable {U : Rake.Dance G I W} {P : Geo I} {μ : ℝ}

lemma offset (h : DOrd M P F p x U) (v : I → QP) : DOrd M P F p (fun w => x w + v) U := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro s hs k
  let y (w : W) := x w + v
  have he : s.Nonempty := Finset.card_pos.mp (by omega)
  let D := constantP G I (PlanetD G)
  have hp (p : Finset W) (hv : p.Nonempty) : rootX y p = rootX x p + v := by
    simp only [rootX, dif_pos hv, y]
  rw [show multi _ y _ _ _ _ _ _ _ = multi (fun _ => planeF) x D D (approach P F) (U s) U k s from ?_]
  · exact h.2.2 s hs k
  unfold multi
  exact
    congr_arg₂ (· + ·) rfl
      (Finset.sum_congr rfl fun i hi => by
        rw [hp i (n_small hi |>.2.1), hp s he, add_sub_add_right_eq_sub])

lemma relocated (a : W → QP) (ha : Injective a) (v : QP) :
    Dial.book F p μ (fun w => a w + v) = Dial.book F p μ a := by
  have he := pin F p μ ha
  have ht : Injective (fun w => a w + v) := fun _ _ h => ha (add_right_cancel h)
  have hp := perfect (pin F p μ ht) (offset F p he (fun _ => v))
  unfold Dial.book
  rw [hp]

lemma toured (a : W → QP) (ha : Injective a) (v : QP) :
    Dial.tour F p μ (fun w => a w + v) = Dial.tour F p μ a := by
  unfold Dial.tour
  rw [relocated F p a ha]
end flags
local notation "𝕄" => XSpace.Mesh
local notation "B" => Ensure.deck G
section canonical
variable (V : XSpace.Initialize G) (μ : ℝ) (A : Prescription (Ensure.deck G))
  (f : Fin n → Glyph (Ensure.deck G) d)

def paidAt (S : Finset (Fin n)) (p : 𝕄) (x : Fin n → Cover) : PowerSeries ℂ :=
  (∏ i ∈ S, Fiscal.postage (height p) (f i).size) •
    BMenu.fullRead V (μ - height p) p.p (V.tree _) 0 A x (profileK f) S

lemma paid_height (x : Fin n → Cover) (p : 𝕄) (a : Cover) (j : ℕ) :
    coeff j (paidAt V μ A f Finset.univ p x) =
      (∏ i, postage (height p) (f i).size) *
        coeff j
          (fullRead V (μ - height p) p.p (V.tree _) a A (fun i => x i - a) (profileK f)
            Finset.univ) := by
  unfold paidAt
  rw [map_smul, smul_eq_mul]
  unfold fullRead
  simp_rw [zero_add, show ∀ i, a + (x i - a) = x i from fun _ => by abel]

def amended (p : 𝕄) (d : ℕ) :=
  Normalize.realm (bets A (μ - height p) (height p) d)
    (Book.Program.substitute (MS.Book.Program.shift A.team (μ - height p)) (Normalize.batch V p d))

def note (p : Sample n) (j : ℕ) :=
  coeff j (paidAt V μ A f Finset.univ p.F p.layout)

lemma revised (p : 𝕄) (f' : Test n) (j : ℕ) :
    amended V μ A p d j n f' (glow ∘ f) = Deposit p (fun x => note V μ A f x j) f' := by
  unfold amended
  rw [pulses (a := 0) A V _ _ _ f (small_p _) _]
  unfold Deposit write
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold note
  dsimp only
  rw [paid_height V μ A f _ p 0]
  unfold XSpace.Mesh.back
  dsimp only [Function.comp_apply]
  ring
section bounds
variable (K : Set (Points n)) {M : Booked (Ensure.deck G)} (F : MS_Data G M)

lemma safe_t : Removed.safe (trial K μ) := fun i => by
  rw [upright]
  exact i.mesh.p.large

lemma at_orn (x : Study K) (j : ℕ) (s : Finset (Fin n)) :
    let T := trial K μ;
    let p := profileK f
    fare (Label.h ∘ p) T.profile (PeakT.ordZ (tagD V T (safe_t μ K) A p)) s j x =
      coeff j (paidAt V μ A f s x.mesh x.pos) := by
  intro R P
  unfold PeakT.ordZ fare
  simp only [Pi.mul_apply]
  rw [logs_out]
  have hU : islandV R (safe_t μ K) x = x.mesh.p := ?he
  swap
  · let S := fun v : Period => v.side
    have h : Injective S := by
      rintro ⟨a, p, u⟩ ⟨b, q, r⟩ hh
      dsimp only [S] at hh
      cases hh
      rfl
    exact h (upright K μ x)
  unfold uncut
  rw [hU]
  unfold paidAt fullRead
  have hp (s : Finset (Fin n)) :
    higher R.profile (Vane.charge (Label.h ∘ P) s) x =
      ∏ i ∈ s, Fiscal.postage (height x.mesh) (f i).size := by
    induction s using Finset.induction with
    | empty => simp [higher, Vane.charge, Port.τ]
    | insert i s hi ih =>
      rw [Vane.charge, Finset.sum_insert hi, higher, Nat.cast_add, ← Port.T_add,
        Finset.prod_insert hi]
      rw [← ih]
      rfl
  rw [map_smul, smul_eq_mul, hp]
  have hv (i) : R.head x + R.off i x = x.pos i := by
    unfold R trial
    dsimp only
    abel
  simp_rw [hv, zero_add]
  rfl

lemma visit_Final (hK : K ⊆ conf n) (i : Study K) :
    Dial.tour F (profileK f) μ (testP (trial K μ) i) =
      Dial.tour F (profileK f) μ (VisitH.actual (i.mesh.rel i.pos i.center)) := by
  rw [funext (act_test K μ i)]
  exact
    toured _ _ _
      (Theater.out.injective.comp
        (show Injective _ from (hK i.bright : i.mesh.rel i.pos i.center ∈ conf n)))
      _

def answers (μ : ℝ) (j : ℕ) (p : Points n) : ℂ :=
  Dial.tour F (profileK f) μ (VisitH.actual p) Finset.univ j
variable (hG : G.Simple) (hu : Installed V F A)
include hG hu

/-- Snapshot uniform mesh-period/separation estimate on the *canonical* aligned
columns in terms of the common Z denominator. Shifted coupling and D(P)
included; no position restamping yet. -/
lemma picture (hs : IsCompact K) (hT : K ⊆ conf n) (j : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ p in Front,
          ∀ v : Fin n → Cover,
            ∀ w ∈ p.Box,
              p.rel v w ∈ K →
                ‖note V μ A f ⟨p, v, w⟩ j - answers f F μ j (p.rel v w)‖ ≤
                  C * exp (-mildG * height p) := by
  let Y := trial K μ
  let L := Filter.comap (Study.mesh (K := K)) Front
  have he : Stretched L Study.mesh :=
    frontier.wider (show Tendsto Study.mesh L Front from tendsto_comap)
  obtain ⟨A', _, _, hX⟩ := adjusted V Y (safe_t μ K) A (profileK f) F μ hG hu L (growing K hs hT μ he)
  obtain ⟨C, hC, h⟩ := hX Finset.univ j |>.2.2
  change ∀ᶠ x in Filter.comap _ Front, _ at h
  rw [eventually_comap] at h
  refine ⟨C, hC.le, ?_⟩
  filter_upwards [frontier.smaller, toll frontier, h] with p hp ih hi v w hw hW
  let x : Study K := ⟨p, ih, hp, v, w, hw, hW⟩
  have ht := hi x rfl
  rw [Pi.sub_apply, show fare _ _ _ _ _ x = _ from at_orn V μ A f K x j Finset.univ,
    show Y = _ from rfl, visit_Final _ _ _ _ hT x] at ht
  exact ht
end bounds
end canonical
end YM.WilsonMS.VisitH
