import YM.WilsonMS.XSpace.LeadingFrame
/-!
# Stability of the near branch using its finite linearization

In the MS frame, use the finite real equations of the established position
scheme. Later get power estimates at every order for the normalized correlator
in the measuring coupling. The leading solve here is already in that frame's
free branch. Don't assume higher bare changes bounded!
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.VisitH
open Function Set Filter MeasureTheory Real Finset
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus
open Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open Fiscal BMenu Reservoir
open PowerSeries (constantCoeff coeff mk)
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d n j : ℕ}
local notation "BΨ" => Ensure.deck G
local notation "𝕄" => XSpace.Mesh

abbrev TrailT (f : 𝕄 → Change G d) (p : Change G d) :=
  Fast (fun i => guide G d (f i)) (guide G d p)

private def wheelT (G : Gauge) (d : ℕ) :
    Change G d →ₗ[ℝ] (Glyph (Ensure.deck G) d → Glyph (Ensure.deck G) d → ℂ) :=
  { toFun F p q := (Daylight (Ensure.deck G) d).coord q (F.val (glow p))
    map_add' _ _ := funext fun _ => funext fun _ => map_add _ _ _
    map_smul' a
      x :=
      funext fun p =>
        funext fun q =>
          map_smul (((Daylight (Ensure.deck G) d).coord q).restrictScalars ℝ) a (x.val (glow p)) }

private lemma wheels (G : Gauge) (d : ℕ) : Injective (wheelT G d) := by
  intro f g h
  apply Subtype.ext
  refine (Daylight (Ensure.deck G) d).ext fun i => ?_
  apply (Daylight (Ensure.deck G) d).equivFun.injective
  ext1 j
  rw [Fiscal.shines]
  exact congr_fun (congr_fun h i) j

lemma Skips {f : 𝕄 → Change G d} {v : Change G d} : Fell (fun i => (f i).val) v.val ↔ TrailT f v := by
  let L := guide G d
  let A := Daylight BΨ d
  let T := wheelT G d
  constructor
  · intro h
    let P := L.toLinearMap.comp T.leftInverse
    have hx (f : Change G d) : L f = P (wheelT G d f) := by
      unfold P
      rw [LinearMap.comp_apply,
        LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (wheels ..))]
      rfl
    change Fast (fun i => L _) (L _)
    simp_rw [hx]
    have hp : Fast (fun i => T (f i)) (T v) :=
      fast_pi (fun i => fast_pi (fun j => Follows.run (h (glow i)) j))
    exact hp.map (LinearMap.toContinuousLinearMap P)
  intro h p
  apply Reservoir.tracks
  intro c
  let P : Change G d →ₗ[ℝ] ℂ :=
    { toFun F := A.coord c (F.val p), map_add' _ _ := map_add _ _ _,
      map_smul' a F := map_smul ((A.coord c).restrictScalars ℝ) a (F.val p) }
  have he (x : Change G d) : P x = (P.comp L.symm.toLinearMap) (L x) := by simp
  change Fast (fun i => P _) (P _)
  simp_rw [he]
  exact h.map (LinearMap.toContinuousLinearMap (P.comp L.symm.toLinearMap))

lemma along {f : 𝕄 → FieldEnd G d} {F} (p : 𝕄 → Sec G d) (x : Sec G d) (hp : Fell f F)
    (h : Follows p x) : Follows (fun i => f i (p i)) (F x) := by
  let B := Daylight BΨ d
  have hs (p : Sec G d) (F : FieldEnd G d) : F p = ∑ i : Glyph BΨ d, B.coord i p • F (glow i) := by
    conv_lhs => rw [← B.sum_repr p]
    rw [map_sum]
    exact
      Finset.sum_congr rfl fun i _ =>
        (map_smul F _ _).trans (congr_arg (fun i : Sec G d => B.coord _ p • F i) (Fiscal.shines i))
  rw [hs x]
  conv_lhs => intro i; rw [hs (p i)]
  exact finals _ fun i _ => chances (Follows.run h i) (hp (glow i))

lemma Fell.stood {f : 𝕄 → Change G d} {p : Change G d} :
    TrailT f p ↔ Fell (fun i => stand (f i)) (stand p) := by
  rw [← Skips]
  constructor
  · intro h x
    exact crow (curfew x) (h x)
  intro h x
  apply tracks
  intro c
  let A := Daylight BΨ d
  have he := (Follows.run (h x) c).sub (Fast.const (A.coord c x))
  have ht (f : Change G d) : A.coord c (Normalize.stand f x) - A.coord c x = A.coord c (f.val x) := by
    rw [Normalize.stood, map_add]
    abel
  unfold A at *
  rw [ht] at he
  apply he.change
  filter_upwards with i
  exact ht (f i)

lemma Fell.joins {f g : 𝕄 → FieldEnd G d} {F H} (h : Fell f F) (ht : Fell g H) :
    Fell (fun i => f i * g i) (F * H) := fun p => along (fun i => g i p) (H p) h (ht p)

lemma Fell.guard {f : 𝕄 → Pick G d} {v : Pick G d} (h : TrailT (fun i => f i n) (v n)) :
    Fell (fun i => coeff n (deck (f i))) (coeff n (deck v)) := by
  by_cases hx : n = 0
  · subst n
    simp_rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, const_deck]
    exact (Fell.stood (G := G)).mp h
  simp_rw [pos_decked _ hx]
  exact Skips.mpr h

lemma Grip {F : 𝕄 → Prediction G d} {P} (hF : NShape F P) (v : 𝕄 → Fin n → Sec G d)
    (p : Fin n → Sec G d) (h : ∀ j, Follows (fun i => v i j) (p j)) (K : Set (Points n))
    (hp : IsCompact K) (hh : K ⊆ conf n) : HoldT K (fun i t => F i n t (v i)) (fun t => P n t p) := by
  let A := Daylight BΨ d
  have hq (L : Prediction G d) (t : Test n) (x : Fin n → Sec G d) :
    L n t x = ∑ i : Fin n → Glyph BΨ d, (∏ j, A.coord (i j) (x j)) * L n t (glow ∘ i) := fromHeight ..
  simp_rw [hq (F _) _ (v _), hq P _ p]
  refine
    HoldT.sum _
      (fun i _ => HoldT.both (Fast.p_prod _ (fun j _ => Follows.run (h j) (i j))) (hF n _ _ hp hh))

abbrev Pilot (F : 𝕄 → Reports G d) (P : Reports G d) (j : ℕ) :=
  ∀ i ≤ j, NShape (fun p => F p i) (P i)

lemma Ringlet {F : 𝕄 → Reports G d} {P : Reports G d} (S : 𝕄 → Pick G d) (T : Pick G d)
    (h : Pilot F P j) (hv : ∀ i ≤ j, TrailT (fun p => S p i) (T i)) :
    NShape (fun p => realm (deck (S p)) (F p) j) (realm (deck T) P j) := by
  intro n p K hK hp
  simp_rw [Normalize.really]
  apply HoldT.sum
  intro k hk
  have he (x) : k x ≤ j :=
    (totaled k |>.mp hk) ▸
      Finset.single_le_sum (f := fun x => k x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
  exact
    Grip (h _ (he none)) (fun i => pulseU k _ p) _
      (fun i => (Fell.guard (n := k (some i)) (f := S) (hv _ (he _))) _) K hK hp
section execute
open Fray
variable {X : Screen G d} (E : X.Prepared) (D : Fray X) {F : 𝕄 → Reports G d} {P : Reports G d}

lemma Cut_fast (h : NShape (fun x => F x 0) (reference G d)) :
    Fast (fun i => D.purse (F i 0)) (D.purse (reference G d)) :=
  fast_pi fun _ => fast_pi fun _ => h.eval _ _

lemma baseGood (hp : P 0 = reference G d) : D.Executed E P := by
  let L (_ : ℝ) := P
  have h : Via (u := pure (0 : ℝ)) D (fun i => L i 0) := by
    simp_rw [L, hp]
    unfold Via
    exact tendsto_const_nhds
  exact D.happy E (P := L) h
variable (hu : NShape (fun x => F x 0) (reference G d)) (ht : P 0 = reference G d)
include hu

lemma shift_first : TrailT (fun i => D.Lays E (F i) 0) (0 : Change G d) := by
  unfold TrailT
  simp_rw [leads, guid]
  rw [map_zero, ← show D.route E _ = 0 from D.ground0 E]
  exact
    Fast.mode (Cut_fast D hu)
      (by
        apply (D.train E).differentiableAt
        simp)
include ht

lemma route_higher (j : ℕ) (hK : Pilot F P j) : TrailT (fun i => D.Lays E (F i) j) (D.Lays E P j) := by
  let T i := D.Lays E (F i)
  let V := D.Lays E P
  induction j using Nat.strong_induction_on with
  | h j hv =>
    by_cases hx : j = 0
    · subst j
      rw [leads D E P, ht, D.pass_free]
      exact shift_first E D hu
    let B i := Screen.blind (T i) j
    let U := Screen.blind V j
    have he (p : ℕ) (hh : p ≤ j) : Pilot F P p := fun i hi => hK _ (hi.trans hh)
    have hR : NShape (fun i => realm (deck (B i)) (F i) j) (realm (deck U) P j) := by
      refine Ringlet B U hK ?_
      intro i hi
      obtain h | rfl := lt_or_eq_of_le hi
      · unfold U B
        simp_rw [Screen.blind_low _ _ _ h]
        exact hv i h (he i h.le)
      unfold U B
      simp_rw [Screen.blind_at]
      exact Fast.const _
    let f (i) := D.purse (F i 0)
    let p := D.purse (reference G d)
    let g := guide G d
    let q i := D.delta (f i, g (T i 0))
    let L := D.delta (p, g 0)
    have htL : L = 1 := by
      unfold L p
      rw [map_zero]
      exact unpin D E
    obtain hq : Fast q L := by
      apply Fast.mode ((Cut_fast D hu).prod_mk (shift_first E D hu))
      unfold Fray.delta
      refine DifferentiableAt.clm_comp ?_ (differentiableAt_const _)
      exact
        (((D.fair).fderiv_right (by trivial : (1 : WithTop ℕ∞) + 1 ≤ ω)).differentiable (by simp)) _
    have hL : L.IsInvertible := by
      rw [htL]
      exact ⟨ContinuousLinearEquiv.refl .., rfl⟩
    let y i := -X.D (realm (deck (B i)) (F i) j)
    let u := -X.D (realm (deck U) P j)
    have hp : TrailT y u := by
      let Y (K : Prediction G d) := fun k => watch (D.scope k) K
      let f i := Y (realm (deck (B i)) (F i) j)
      have ht' : Fast f (Y (realm (deck U) P j)) := fast_pi fun p => hR.eval _ _
      unfold TrailT u y
      simp_rw [map_neg, ← D.equal]
      exact (ht'.map D.stamps).neg
    change Fast (fun i => g (T i j)) (g (V j))
    have htV : V 0 = 0 := by
      unfold V
      rw [leads D E, ht, D.pass_free]
    have hV : g (V j) = L.inverse (g u) := by
      rw [← hL.inverse_apply_self (g (V j))]
      refine congr_arg L.inverse ?_
      have ht' := baseGood E D ht
      unfold L p
      rw [← ht, ← htV]
      change D.delta _ _ = _
      rw [D.order]
      apply congr_arg (guide G d)
      rw [align, LinearEquiv.symm_apply_apply]
      exact X.bare_price _ _ hx ht'.2.1
    have hx' := hL.contDiffAt_map_inverse (n := 1)
    have H : Fast (fun i => (q i).inverse (g (y i))) (L.inverse (g u)) :=
      Fast.mode ((hq.mode (hx'.differentiableAt (by simp))).prod_mk hp)
        (differentiableAt_fst.clm_apply differentiableAt_snd)
    rw [hV]
    refine H.change ?_
    let B₀ := Cut_fast D hu
    have hξ : Via (u := Front) D (fun i => F i 0) := B₀.limit
    have hevent := Tendsto.prodMk_nhds B₀.limit (shift_first E D hu |>.limit)
    rw [map_zero] at hevent
    filter_upwards [D.happy E hξ, hevent.eventually (D.unhit E)] with i hi hi'
    have he : (q i).IsInvertible := hi'
    rw [← he.inverse_apply_self (g (T i j))]
    congr 1
    unfold q f
    rw [D.order, align, LinearEquiv.symm_apply_apply]
    exact congr_arg g (Eq.symm (X.bare_price _ _ hx hi.2.1))

lemma fit_rate (j : ℕ) (hK : Pilot F P j) : NShape (fun i => D.fit E (F i) j) (D.fit E P j) :=
  Ringlet _ _ hK fun i hi => route_higher E D hu ht i (fun k hk => hK k (hk.trans hi))
end execute
end YM.WilsonMS.VisitH
