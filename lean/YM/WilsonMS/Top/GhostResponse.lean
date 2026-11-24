import YM.WilsonMS.Top.HalfAction

/-! # Root vs full ghost sources computed on the same gauge patch

Pull `ropes` on any stencil lift parameter columns. Then specialize when
those parameters are based *as used in the ghost algebra*. (Mean-zero will need
an extra cancellation.)
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Quo
open Function Filter Set Finset Matrix Complex Lattice XSpace
open MS MS.Orbit MS.Bare MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.Native Root Position Darboux
open Focus
open scoped Topology ContDiff Matrix.Norms.Frobenius

variable {P : Period} (T : P.Tree) (G : Gauge)
local notation "Nm'" => LinksI G P
local notation "Qm'" => GhostI T G
local notation "n" => P.side
local notation "J'" => liftJ P G
local notation "M'" => Root.Mode T G
local notation "U'" => SiteField G P.side
local notation "Q'" => GaugeField G P.side
local notation "T₀" => MS.Native.Chart.City G P.Sites
local notation "T₁" => LogSpace G P
local notation "A0" => Native.glow G (Site P.side)
local notation "R0" => coordinates T G
local notation "Rd" => Chart.drive P.side
local notation "VI" => colorTerm G (Site P.side)
local notation "Ro" => Chart.loco (G := G) (Chart.drive P.side)
local notation "PM'" => Native.Paper G (Site P.side)
local notation "Δ" => panel G (Site P.side)
local notation "Rv" => R0
local notation "χ" => expander P G
local notation "Vu" => localVector T G
local notation "Ac" => liftN T G

def parameter (S : Matrix Q' Qm' ℂ) (j : Qm') : Lot G (Site P.side) :=
  ∑ i : Q', (S i j).re • Native.priv (siteEquiv G P.side i)

def travel (v : Lot G P.Sites) (x : T₁) : T₀ :=
  Chart.roam Rd (χ x) v

def source_response (p : Lot G P.Sites) (j : SiteField G P.side) : Raw M' ℂ :=
  ink (R0).e0 ((A0).seed (linkEquiv G n j) ∘ travel G p)

section movement
variable (S : Matrix (GaugeField G P.side) (GhostI T G) ℂ)

lemma pull_K (i : U') :
    specialize (location T G S) (atLetter (ak G n i)) = ∑ j : Nm', J' i j • atLetter (k j) := by
  classical
  rw [specialize_letter, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type (α₁ := Nm')]
  simp_rw [show ∀ x, location T G S (ak G n i) x = _ from fun x => locationF T G S (k i) x]
  simp [legs, k]

lemma pull_C (i : Q') :
    specialize (location T G S) (atLetter (cc G n i)) = ∑ j : Qm', S i j • atLetter (c j) := by
  rw [specialize_letter, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type (α₁ := Nm')]
  simp_rw [show ∀ x, location T G S (cc G n i) x = _ from fun x => locationF T G S (c i) x]
  simp [legs, c]

lemma pull_B (i : Q') : specialize (location T G S) (atLetter (cb G n i)) = 0 := by
  rw [specialize_letter]
  apply Finset.sum_eq_zero
  intro k _
  rw [show location T G S (cb G n i) k = 0 from locationF T G S (b i) _ |>.trans rfl, zero_smul]

lemma responds (hs : RealEntries S) (j : Qm') (i : U') :
    source_response T G (parameter T G S j) i =
      ∑ k : Q',
        S k j •
          specialize (location T G S)
            (ink (A0).e0 ((A0).seed (linkEquiv G n i) ∘ Ro (siteEquiv G n k))) := by
  let F (k : Q') := ((A0).seed (linkEquiv G n i) ∘ Ro (siteEquiv G n k))
  let V (k : Q') := F k ∘ χ
  have h (j) : germ (F j) := (A0).seed _ |>.contDiff.contDiffAt.comp 0 (Chart.ride ..)
  have ht (j : Q') : germ (V j) :=
    ContDiffAt.comp (f := ⇑χ) 0
      (by
        rw [map_zero]
        exact h j)
      (χ).contDiff.contDiffAt
  have he :
    (A0).seed (linkEquiv G n i) ∘ travel G (parameter T G S j) = ∑ k : Q', ((S k j).re) • V k := by
    funext x
    unfold travel parameter
    simp_rw [Function.comp_apply, map_sum, Finset.sum_apply, map_smul]
    rfl
  unfold source_response
  rw [he, ink_sum _ _ (fun a _ => show germ ((S a j).re • V a) from (ht a).const_smul (S a j).re)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [restrict_germ T G hs (F k) (h k), ink_smul _ (ht k), hs]

lemma bill (hs : RealEntries S) (i : U') :
    specialize (location T G S) (stone (A0) Ro (linkEquiv G n i)) =
      ∑ j : Qm', product (dg T G) (atLetter (c j)) (source_response T G (parameter T G S j) i) := by
  let L := specialize (location T G S)
  have he (F H : Raw (FixedMode G P.side) ℂ) :
    L (product σbranch F H) = product (dg T G) (L F) (L H) :=
    (specialize_tether (location_tie T G S)).craft F H
  unfold stone
  rw [← Equiv.sum_comp (siteEquiv G P.side), map_sum]
  change (∑ i' : Q', L (product σbranch ((Δ).spark (siteEquiv G n i')) _)) = _
  simp_rw [he, show ∀ k, L ((Δ).spark (siteEquiv G n k)) = _ from fun k => pull_C T G S k, map_sum,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply, responds T G S hs, map_sum, map_smul]
  exact Finset.sum_comm

abbrev wing (P : Period) (G : Gauge) :=
  (Native.Paper G (Site P.side)).hung
    (launch (Native.glow G (Site P.side)) (colorTerm G (Site P.side))
      (Chart.loco (Chart.drive P.side)))

def history (p : Lot G P.Sites) (u : Nm') :=
  ∑ i : U', J' i u • source_response T G p i

def connected (v : Qm' → Lot G (Site P.side)) :=
  ∑ u : Nm',
    product (dg T G) (atLetter (k u))
      (∑ j : Qm', product (dg T G) (atLetter (c j)) (history T G (v j) u))

lemma bill_total (hs : RealEntries S) :
    specialize (location T G S) (wing P G) = connected T G (parameter T G S) := by
  let V := specialize (location T G S)
  let W (i) := launch (A0) VI Ro i
  have he (f g : Raw (FixedMode G n) ℂ) : V (product σbranch f g) = product (dg T G) (V f) (V g) :=
    (specialize_tether (location_tie T G S)).craft ..
  let T0 (j : Native.ToneS G × Site n) :=
    (PM').fee j (R := ℂ) • product (dg T G) (V (atLetter ((PM').dual j))) (V (W j))
  suffices H : (∑ i, T0 i) = connected T G (parameter T G S)
    by
    unfold wing Bonded.hung
    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) H
    rw [map_smul]
    exact congr_arg ((PM').fee i (R := ℂ) • ·) (he _ _)
  let Vp (u : Nm') (j : Qm') (i : U') :=
    product (dg T G) (atLetter (k u))
      (product (dg T G) (atLetter (c j)) (source_response T G (parameter T G S j) i))
  rw [(Δ).split_i, ← Equiv.sum_comp (linkEquiv G n), ←
    Equiv.sum_comp (siteEquiv G n) (fun i => (T0 ((Δ).KId i))),
    show (∑ i : Q', T0 ((Δ).KId (siteEquiv G n i))) = 0 from Finset.sum_eq_zero (fun x _ => ?_)]
  swap
  · unfold T0
    rw [show V (atLetter ((PM').dual ((Δ).KId (siteEquiv G n x)))) = 0 from pull_B T G S x, map_zero,
      LinearMap.zero_apply, smul_zero]
  rw [add_zero]
  have hx i : T0 ((Δ).AId (linkEquiv G n i)) = ∑ u : Nm', ∑ j : Qm', J' i u • Vp u j i := by
    unfold T0
    rw [show (PM').fee _ = (1 : ℂ) from rfl, one_smul]
    rw [show V (atLetter ((PM').dual ((Δ).AId (linkEquiv G n i)))) = _ from pull_K T G S i,
      show V (W ((Δ).AId (linkEquiv G n i))) = _ from bill T G S hs i]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Finset.sum_comm
  simp_rw [hx, connected, history, map_sum, map_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
end movement

lemma propagateR (j : Qm') : parameter T G Ac j = based T G (Native.priv j) ∘ P.vertex := by
  let g := based T G (Native.priv j) ∘ P.vertex
  change _ = g
  rw [← Native.frame g, ← Equiv.sum_comp (siteEquiv G n)]
  unfold parameter
  apply Finset.sum_congr rfl
  intro i _
  rw [projector_k]
  rfl

lemma vBased (p : Qm') : travel G (parameter T G Ac p) =ᶠ[𝓝 0] χ ∘ Vu p := by
  have h (x : P.Sites) : parameter T G Ac p x = based T G (Native.priv p) (P.vertex x) :=
    congr_fun (propagateR T G p) x
  have hu (e : P.Link) :
    Chart.route (Chart.drive n) e.val (parameter T G Ac p) = endsMap T G e (Native.priv p) :=
    Prod.ext (h _) (h _)
  have he (e : P.Link) :
    Chart.route Rd (P.reflect e.val) (parameter T G Ac p) = (endsMap T G e (Native.priv p)).swap := by
    rw [← hu, Chart.routed, Chart.routed]
    unfold Chart.endRail Chart.drive
    rw [P.reflect_axis, P.reflect_dest, P.reflect_base]
    simp only [h, P.vertex_neg]
    rfl
  filter_upwards [eventually_all.mpr
      (fun x : P.Link =>
        (continuous_apply (A := fun _ : P.Link => G.Color) x |>.tendsto (0 : T₁)).eventually
          (MS.Bare.Maurer.volt_back (endsMap T G x (Native.priv p))))] with
    a ha
  funext e
  change Maurer.volts _ _ = P.extend (localVector T G p a) e
  by_cases hp : P.Chosen e
  · let x : P.Link := ⟨e, hp⟩
    rw [P.extend_at _ x, show χ a e = a x from P.extend_at _ x]
    rw [hu x]
    rfl
  let x : P.Link := ⟨P.reflect e, (P.choice_reflect _).mpr hp⟩
  have hX : e = P.reflect x.val := (P.reflect_invol e).symm
  let g0 := parameter T G Ac p
  change Maurer.volts (Chart.route Rd e g0) (χ a e) = P.extend _ e
  rw [hX, he x, show χ a _ = -(a x) from (P.extend_reflect a _).trans (by rw [P.extend_at]), ha x,
    P.extend_reflect, P.extend_at]
  rfl

lemma componentL (v : T₁) (j : Nm') :
    ∑ i : U', (J' i j).re * ((A0).seed (linkEquiv G n i) (χ v) : ℝ) = 2 * ((R0).seed j v : ℝ) := by
  let f : T₁ →ₗ[ℝ] ℝ := ∑ i : U', (J' i j).re • (((A0).seed (linkEquiv G n i)) ∘L χ).toLinearMap
  change (∑ i : U', _) = _
  rw [show (∑ i : U', _) = f v from
      (by
        unfold f
        simp only [LinearMap.sum_apply, LinearMap.smul_apply]
        rfl)]
  let L : T₁ →ₗ[ℝ] ℝ := (2 : ℝ) • ((R0).seed j).toLinearMap
  change f v = L v
  rw [← Native.frame v, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul, map_smul]
  have hp (i : U') : (A0).seed (linkEquiv G n i) (χ (priv k)) = (J' i k).re := by
    rw [expands_basis]
    rfl
  have hv (q : Nm') : (R0).seed q (priv k) = (1 : Matrix Nm' Nm' ℝ) q k := by
    unfold coordinates
    rw [projector_k]
    rcases q with ⟨a, b⟩
    rcases k with ⟨x, k⟩
    by_cases he : a = x <;> by_cases hx : b = k <;> simp [Native.priv, he, hx, Matrix.one_apply]
  apply congr_arg
  unfold L f
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, hp, hv, smul_eq_mul]
  apply ofReal_injective
  rw [Complex.ofReal_sum]
  simp_rw [Complex.ofReal_mul, real_lift G _ _]
  rw [show (∑ i : U', J' i j * J' i k) = (J'ᵀ * J') j k
      by
      rw [Matrix.mul_apply]
      rfl,
    lifted_norm]
  simp [one_apply]
  split <;> simp

lemma rooted_history (p : Lot G P.Sites) (v : T₁ → T₁) (h : germ v) (hx : travel G p =ᶠ[𝓝 0] χ ∘ v)
    (j : Nm') : history T G p j = (2 : ℂ) • ink (R0).e0 ((R0).seed j ∘ v) := by
  let g (i : U') := (A0).seed (linkEquiv G n i) ∘ (χ ∘ v)
  let Y (i : U') := (A0).seed (linkEquiv G n i) ∘ travel G p
  have hp (i) : germ (g i) :=
    ContDiffAt.comp (g := (A0).seed (linkEquiv G n i)) (f := χ ∘ v) 0
      ((A0).seed _ |>.contDiff.contDiffAt) ((χ).contDiff.contDiffAt.comp 0 h)
  unfold history
  change (∑ i : U', _) = _
  rw [show ((2 : ℂ) • ink (R0).e0 ((R0).seed j ∘ v)) = ink (R0).e0 ((2 : ℝ) • ((R0).seed j ∘ v)) from
      ?_]
  swap
  · rw [ink_smul _ ((R0).seed j |>.contDiff.contDiffAt.comp 0 h), Complex.ofReal_ofNat]
  rw [show (2 : ℝ) • ((R0).seed j ∘ v) = ∑ i : U', (J' i j).re • g i from
      funext
        (fun x => by
          rw [Finset.sum_apply]
          exact (componentL T G (v x) j).symm),
    ink_sum _ _ (fun i _ => (show germ ((J' i j).re • (g i)) from (hp i).const_smul (J' i j).re))]
  exact
    Finset.sum_congr rfl fun i _ => by
      rw [ink_smul _ (hp i), real_lift]
      unfold source_response
      rw [inkit _ (hx.fun_comp _)]

private lemma specialK (i : Nm') : specialize (discard T G) (atLetter (k i)) = atLetter (k i) := by
  rw [specialize_letter]
  simp [discard, k, legs, Fintype.sum_sum_type, Root.Mode, Darboux.Letters, Matrix.one_apply]

private lemma specialC (i : Qm') :
    specialize (discard T G) ((chartFocus T G).spark i) = atLetter (c i) := by
  change specialize (discard T G) (atLetter (c i)) = _
  rw [specialize_letter]
  simp [discard, c, legs, Fintype.sum_sum_type, Root.Mode, Darboux.Letters, Matrix.one_apply]

private lemma specialB (i : Qm') : specialize (discard T G) (atLetter (b i)) = 0 := by
  rw [specialize_letter]
  simp [discard, legs, Root.Mode, Darboux.Letters]

lemma compare_based :
    specialize (location T G Ac) (wing P G) =
      (2 : ℂ) •
        specialize (discard T G)
          ((pairs T G).hung
            (launch (coordinates T G) (Native.colorTerm G T.Nonroot) (localVector T G))) := by
  let Q := specialize (discard T G)
  let X := launch (coordinates T G) (Native.colorTerm G T.Nonroot) Vu
  let q := dg T G
  have hm (V U : Raw M' ℂ) : Q (product q V U) = product q (Q V) (Q U) :=
    (specialize_tether (discard_wire T G)).craft ..
  let F i := (pairs T G).fee i (R := ℂ) • product q (atLetter ((pairs T G).dual i)) (X i)
  have ht j : Q (F (Sum.inr j)) = 0 := by
    unfold F
    rw [map_smul, hm, show Q (atLetter ((pairs T G).dual (Sum.inr j))) = 0 from specialB T G j,
      map_zero, LinearMap.zero_apply, smul_zero]
  rw [bill_total T G _ (real_based T G)]
  change connected T G _ = _ • Q (∑ i, F i)
  rw [map_sum, Fintype.sum_sum_type]
  simp_rw [ht, Finset.sum_const_zero, add_zero]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold F
  rw [show (pairs T G).fee (.inl i) = (1 : ℂ) from rfl, one_smul, hm,
    show Q (atLetter ((pairs T G).dual (Sum.inl i))) = atLetter (k i) from specialK T G i]
  rw [← map_smul (product _ _)]
  apply congr_arg
  rw [show X (Sum.inl i) = stone (R0) Vu i from launch_stone .., stone, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [rooted_history T G _ (Vu j) ((site_lie ..).smooth j) (vBased T G j) i, map_smul, hm,
    show Q ((chartFocus T G).spark j) = _ from specialC T G j,
    show Q _ = _ from discardReads T G ((R0).seed i ∘ Vu j) ((site_lie T G).vectorSeed _ i j)]
end YM.WilsonMS.Quo
