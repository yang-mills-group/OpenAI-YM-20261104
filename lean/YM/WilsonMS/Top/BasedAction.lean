import YM.WilsonMS.Top.Based
import YM.WilsonMS.Top.ClosedSeries

/-!
# All orders on the finite inversion regulator

`uncoupled` is the quotient orbit action (half) *together* with the BV
exponent for the based equivariant gauge transformations. Haar is tracked
separately even when gauge fixing. Prove the master and insertion conditions
in the actual symbol conventions with these choices; the unrestricted QME
on the cover wouldn't suffice.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Root
open XSpace Period Lattice Function Filter Set Finset
open MS MS.Koszul MS.Bare MS.Bare.Focus MS.Cylinder MS.Cylinder.Taylor MS.Native MS.Book
  MS.Book.Convolve
open Darboux
open scoped Topology Matrix.Norms.Frobenius ContDiff

variable {P : Period} (T : P.Tree) (G : Gauge)

def liftedA (P : Period) (G : Gauge) : LogSpace G P →ₗ[ℝ] MS.Native.Chart.City G P.Sites
    where
  toFun := Period.extend P
  map_add' x y := by
    funext e
    unfold Period.extend
    split_ifs <;> simp [*, add_comm]
  map_smul' x y := by
    funext e
    unfold Period.extend
    split_ifs <;> simp [*]

lemma exponentiate (x : LogSpace G P) :
    Native.Chart.nation (liftedA P G x) = P.restore (raised G x) := by
  funext e
  change G.lieExp (P.extend x e) = _
  unfold Period.extend Period.restore raised
  split_ifs
  rfl
  rw [Next.SectorChange.exp_negative]
  rfl

def energyE (P : Period) (G : Gauge) (x : LogSpace G P) :=
  -P.energy (raised G x)

lemma cover_exp (x : LogSpace G P) :
    energyE P G x = Native.Chart.rent (Native.Chart.drive P.side) (liftedA P G x) / 2 := by
  rw [Native.Chart.original_W, exponentiate, neg_div]
  rfl

lemma energy_germ (P : Period) (G : Gauge) : germ (energyE P G) := by
  let V := (liftedA P G).toContinuousLinearMap
  let k := Native.Chart.drive P.side
  rw [show energyE P G = (fun x => (Native.Chart.rent k ∘ V) x / (2 : ℝ)) from funext (cover_exp G)]
  exact
    (ContDiffAt.comp (g := Native.Chart.rent k) (f := ⇑V) 0
          (by
            rw [map_zero]
            exact Native.Chart.rent_s _)
          V.contDiff.contDiffAt).div_const
      _

lemma energy_zero (P : Period) (G : Gauge) : energyE P G 0 = 0 := by
  rw [cover_exp, map_zero]
  simp [Native.Chart.rent, Native.Chart.gone, Native.Chart.atCart]

lemma energy_st (P : Period) (G : Gauge) : fderiv ℝ (energyE P G) 0 = 0 := by
  have H : IsLocalMax (energyE P G) 0 :=
    Filter.Eventually.of_forall fun u => by
      change energyE P G u ≤ energyE P G 0
      rw [energy_zero]
      exact neg_nonpos.mpr (div_nonneg (Wilson.energy_nonneg _) zero_le_two)
  exact H.fderiv_eq_zero

lemma energyGauge : Inert (localVector T G) (energyE P G) :=
  inert_of_invariant T G (fun x => -P.energy x) (fun x _ u => by rw [Period.energy_invariant])
    (energy_germ P G)

def stamped (O : P.Array G → ℝ) :=
  ink (coordinates T G).e0 (O ∘ raised G)

def uncoupled : Raw (Root.Mode T G) ℂ :=
  Sourced (energyE P G) (Native.colorTerm G T.Nonroot) (localVector T G) (coordinates T G)

def haarLog : Raw (Root.Mode T G) ℂ :=
  ink (coordinates T G).e0 (orbitLog G)

def exponent : MS.Book.Convolve.T (Raw (Root.Mode T G) ℂ) :=
  rankLevel 2 (uncoupled T G) + rankLevel 0 (haarLog T G)

def free :=
  mask 2 (uncoupled T G)

def interaction : MS.Book.Convolve.T (Raw (Root.Mode T G) ℂ) := fun i : ℕ =>
  if i = 0 then 0 else exponent T G i

lemma log_head : haarLog T G [] = 0 := by
  simp [haarLog, orbitLog, MS.Bare.Maurer.lac, LocalH.spin_zero]

lemma exp_head : exponent T G 0 = free T G := by
  have hv : mask 0 (haarLog T G) = 0 := by
    ext l
    cases l with
    | nil =>
      rw [enough [] (by simp), log_head]
      rfl
    | cons i l =>
      exact
        strange _
          (by
            simp
            omega)
  change (mask _ _ + mask (↑(0 : ℕ) + (0 : ℤ)) _ : Raw (Root.Mode T G) ℂ) = _
  norm_num [hv, free]

lemma assemble : Puff.Mom.useN.refineV (free T G) + interaction T G = exponent T G := by
  ext1 i
  by_cases h : i = 0
  · subst i
    rw [Pi.add_apply, Puff.SplitP.refineV, if_pos (show 0 = Puff.Mom.useN.origin from rfl),
      interaction, if_pos rfl, add_zero, exp_head]
  rw [Pi.add_apply, Puff.SplitP.refineV, if_neg (show i ≠ Puff.Mom.useN.origin from h), interaction,
    if_neg h, zero_add]

lemma happy : interaction T G 0 = 0 :=
  if_pos rfl

lemma uncoupled_symm : Symm (dg T G) (uncoupled T G) :=
  (ink_s _ (coordinates T G |>.never) (energy_germ P G)).add
    (Bonded.Lifted.acted_s (lifting _ _ _ (site_lie T G |>.smooth)))

lemma uncoupled_pure : Pure (dg T G) false (uncoupled T G) :=
  (ink_p _ (coordinates T G |>.never) _).add
    (Bonded.Lifted.acted_e (lifting _ _ _ (site_lie T G |>.smooth)))

lemma log_symm : Symm (dg T G) (haarLog T G) :=
  ink_s _ (coordinates T G |>.never) (orbit_germ G)

lemma log_pure : Pure (dg T G) false (haarLog T G) :=
  ink_p _ (coordinates T G |>.never) _

lemma launchFrom (i) :
    From (launch (coordinates T G) (Native.colorTerm G T.Nonroot) (localVector T G) i) 1 := by
  let Y := coordinates T G
  let F := chartFocus T G
  have hl (j) : From (F.spark j) 1 := fun l h => by
    cases l with
    | nil => rfl
    | cons =>
      simp at h
      omega
  rcases i with i | i
  · change From (stone Y (localVector T G) i) 1
    exact
      From.sum _
        (fun j _ =>
          (hl j).pair (hx := 0)
            (show From _ 0 from
              (by
                intro l h
                omega)))
  change From (F.shadow (Native.colorTerm G T.Nonroot) i) 1
  have hx : From (F.shadow (Native.colorTerm G T.Nonroot) i) 2 :=
    From.sum _ (fun j _ => From.sum _ (fun k _ => From.smul _ ((hl j).pair (hl k))))
  intro l h
  exact hx l (by omega)

lemma actionFrom : From (uncoupled T G) 2 := by
  apply From.add
  · intro l h
    cases l with
    | nil => simp [energy_zero]
    | cons i l =>
      cases l with
      | nil =>
        change (↑(fderiv ℝ (energyE P G) 0 _) : ℂ) = 0
        rw [energy_st]
        simp
      | cons =>
        simp at h
        omega
  refine From.sum _ ?_
  intro i _
  refine From.smul _ (From.pair (h := 1) ?_ (launchFrom T G i))
  intro l h
  cases l
  rfl
  simp at h
  omega

lemma class_master : link (pairs T G).BV true (dg T G) (uncoupled T G) (uncoupled T G) = 0 :=
  (site_lie T G).classicalGauge _ (energy_germ P G) (energyGauge T G)

/-- The QME of the actual quotient/based action with the Haar terms. E.g.
later applied in `field_comparison` to see a given coefficient is a closed
symbol in the free *based* complex. -/
lemma tok : MS.Book.tokM (pairs T G) (exponent T G) = 0 := by
  let B := pairs T G
  let p := dg T G
  let L := uncoupled T G
  let R := haarLog T G
  let f := rankLevel 2 L
  let g := rankLevel 0 R
  let V := tokenL B.BV true p
  have he := actionFrom T G
  have hv : From R 0 := by
    intro l h
    omega
  have hs : B.BV R = 0 := lap_g (coordinates T G) (orbitLog G)
  have hl : link B.BV true p L L = 0 := class_master T G
  have hr : link B.BV true p R R = 0 := link_g ..
  have hh : link B.BV true p R L = link B.BV true p L R :=
    link_commute _ (log_pure T G) (uncoupled_pure T G)
  funext k
  change B.BV ((f + g) k) + (1 / 2 : ℂ) • pairW V (f + g) (f + g) k = 0
  simp_rw [Pi.add_apply, map_add, LinearMap.add_apply, Pi.add_apply]
  rw [show pairW V f f k = rankLevel (2 + 2 - 2) (link B.BV true p L L) k from link_level _ k he he,
    show pairW V f g k = rankLevel (2 + 0 - 2) (link B.BV true p L R) k from link_level _ k he hv,
    show pairW V g f k = rankLevel (0 + 2 - 2) (link B.BV true p R L) k from link_level _ k hv he, hh,
    show pairW V g g k = rankLevel (0 + 0 - 2) (link B.BV true p R R) k from link_level _ k hv hv,
    show B.BV (f k) = rankLevel (2 - 2) (B.BV L) k from lap_level B k,
    show B.BV (g k) = rankLevel (0 - 2) (B.BV R) k from lap_level B k, hl, hr, hs]
  have hy : B.BV L + link B.BV true p L R = 0 :=
    (site_lie T G).quantum_pay _ (orbit_germ G) (density_identity T G)
  unfold rankLevel
  simp only [map_zero, add_zero, zero_add]
  norm_num
  have hb := congr_arg (mask (k : ℤ)) hy
  simp only [map_add, map_zero] at hb
  linear_combination (norm := module) hb

private lemma free_cl : link (pairs T G).BV true (dg T G) (free T G) (free T G) = 0 := by
  have hv := link_level (pairs T G) 0 (actionFrom T G) (actionFrom T G)
  rw [class_master] at hv
  simpa [rankLevel, free] using hv

private lemma masked_parity {A : Type} {p : Sector A} {F : Raw A ℂ} (hp : Pure p false F) (n : ℤ) :
    Pure p false (mask n F) := by
  intro l h
  by_cases he : (l.length : ℤ) = n
  exact (enough l he).trans (hp l h)
  exact strange _ he

lemma quadratic : Quadratic (pairs T G) (free T G)
    where
  rank := rankMod _ _
  even := masked_parity (uncoupled_pure T G) _
  symm := mask_symmetric _ (uncoupled_symm T G)
  master := free_cl T G
  lap := by
    let B := pairs T G
    let X := exponent T G
    have he := congr_fun (tok T G) 0
    change B.BV (X 0) + (1 / 2 : ℂ) • pairW (tokenL B.BV true (dg T G)) X X 0 = 0 at he
    dsimp only [B, X] at he
    rw [paired, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, exp_head] at he
    change _ + (1 / 2 : ℂ) • link B.BV true (dg T G) (free T G) (free T G) = 0 at he
    rw [show link B.BV true (dg T G) (free T G) (free T G) = 0 from free_cl T G] at he
    simpa using he

lemma field_closed (O : P.Array G → ℝ) (hg : germ (O ∘ raised G))
    (hh : ∀ k : P.Vertex → G.El, k T.root = 1 → ∀ U, O (P.act k U) = O U) (d : ℕ)
    (h : From (stamped T G O) d) :
    modulo (pairs T G) (exponent T G) (rankLevel d (stamped T G O)) = 0 := by
  let B := pairs T G
  let p := dg T G
  let V := stamped T G O
  let U := rankLevel (↑d) V
  let L := uncoupled T G
  let R := haarLog T G
  let f := rankLevel 2 L
  let g := rankLevel 0 R
  let Φ := tokenL B.BV true p
  have he := actionFrom T G
  have hv : From R 0 := by
    intro l h
    omega
  have hx : link B.BV true p L V = 0 := by
    have hG := inert_of_invariant T G O hh hg
    rw [show link B.BV true p L V = _ from
        (site_lie T G).onto (f := energyE P G) (coordinates T G) hg]
    apply Finset.sum_eq_zero
    intro i _
    rw [inkit _ (hG i), ink_zero, map_zero]
  have hR : link B.BV true p R V = 0 := link_g ..
  have hV : B.BV V = 0 := lap_g ..
  ext1 n
  change B.BV (U n) + pairW Φ (f + g) U n = 0
  simp_rw [map_add, LinearMap.add_apply, Pi.add_apply]
  rw [show pairW Φ f U n = rankLevel (2 + d - 2) (link B.BV true p L V) n from link_level _ n he h,
    show pairW Φ g U n = rankLevel (0 + d - 2) (link B.BV true p R V) n from link_level _ n hv h,
    show B.BV (U n) = rankLevel (↑d - 2) (B.BV V) n from lap_level B n, hV, hx, hR]
  simp [rankLevel]

end YM.WilsonMS.Root
