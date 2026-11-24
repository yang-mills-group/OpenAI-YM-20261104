import YM.WilsonMS.Top.FFT

/-!
# Block reading of the supplied position and momentum Symbols

The full periodic tangent space (for inspecting the action & propagator,
not claiming it's a valid all-orders flat-saddle LPT regulator).
Use both the tangent and cotangent labels of the `Swirl` finite mode alphabet.
Keep the local kinetic and orbit-gradient from the actual Wilson definitions,
including both anchor positions on a link.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Position
open Function Finset Filter Set Matrix Complex Lattice
open MS MS.Orbit MS.Orbit.Cog MS.Koszul MS.Plane MS.Bare MS.Native
open MS.Cylinder.Lab MS.Book MS.Cylinder MS.Landau MS.Latch MS.City MS.Swirl MS.Swirl.Near MS.Tone
open scoped Topology

variable (G : Gauge) (n : Side)

abbrev Ax :=
  Axis × G.ColorIndex

abbrev SiteField :=
  Ax G × Site n

abbrev GaugeField :=
  G.ColorIndex × Site n

def atomA (i : Ax G) : BH G :=
  (Landau.gauge i.1, i.2)

def atomK (i : Ax G) : BH G :=
  (Landau.anti i.1, i.2)

def atomC (i : G.ColorIndex) : BH G :=
  (Landau.ghost, i)

def atomB (i : G.ColorIndex) : BH G :=
  (Landau.gaugeC, i)

abbrev aa : SiteField G n → FixedMode G n :=
  Prod.map (atomA G) id

abbrev ak : SiteField G n → FixedMode G n :=
  Prod.map (atomK G) id

abbrev cc : GaugeField G n → FixedMode G n :=
  Prod.map (atomC G) id

abbrev cb : GaugeField G n → FixedMode G n :=
  Prod.map (atomB G) id

lemma AInj : Injective (atomA G) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ h
  simpa [atomA, Landau.gauge] using h

lemma KInj : Injective (atomK G) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ h
  simpa [atomK, anti] using h

lemma CInj : Injective (atomC G) := fun _ _ h => congr_arg Prod.snd h

lemma BInj : Injective (atomB G) := fun _ _ h => congr_arg Prod.snd h

def linkEquiv : SiteField G n ≃ Mind G (Site n)
    where
  toFun x := ((x.2, x.1.1), x.1.2)
  invFun x := ((x.1.2, x.2), x.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

def siteEquiv : GaugeField G n ≃ Native.Eyes G (Site n) :=
  Equiv.prodComm ..

local notation "Nm" => SiteField G n
local notation "Qm" => GaugeField G n
local notation "Γ" => fourier G n
local notation "WA" => FFT.forward (Ax G) n
local notation "WC" => FFT.forward G.ColorIndex n
local notation "PR" => Native.Wilsonian.W G
local notation "Rt" => Native.Chart.drive n
local notation "Ep" => Native.Chart.rent (G := G) Rt

def fullH : Matrix (SiteField G n) (SiteField G n) ℂ := fun i j =>
  -Taylor.ink (glow G _).e0 (Chart.rent (Chart.drive n)) [aa G n i, aa G n j]

def fullD : Matrix (SiteField G n) (GaugeField G n) ℂ := fun i j =>
  (↑((glow G _).seed (linkEquiv G n i) (Chart.loco (G := G) Rt (siteEquiv G n j) 0)) : ℂ)

section
open MS.Bare.Focus
local notation "F" => glow G (Site n)
local notation "CP" => Native.colorTerm G (Site n)
local notation "LA" => Lattice.step (R := Per n)
local notation "LV" => Chart.loco Rt
local notation "Ζ" => panel G (Site n)
local notation "U" => Native.Paper G (Site n)

lemma AA_read (i j : Nm) : docket n PR [aa G n i, aa G n j] = -fullH G n i j := by
  rw [Wilsonian.witnessD]
  let X := aa G n i
  let Y := aa G n j
  let s := launch (F) CP LV
  change Taylor.ink _ _ _ + (U).hung s [X, Y] = _
  have he x : product (field Landau.parity) (atLetter ((U).dual x)) (s x) [X, Y] = 0 := by
    have hz := (U).diff ((Ζ).AId (linkEquiv G n i)) x
    have hw := (U).diff ((Ζ).AId (linkEquiv G n j)) x
    rw [D_eval _ (product _ _ _), D_product]
    rw [unheard _ (show X ≠ _ from hz), map_zero, LinearMap.zero_apply, zero_add]
    rw [(speaks_p _).signs, map_smul, LinearMap.smul_apply, Pi.smul_apply, D_eval _ (product _ _ _),
      D_product, Pi.add_apply, nil_product, nil_product, unheard _ (show Y ≠ _ from hw)]
    simp [Cylinder.atLetter]
  unfold Bonded.hung
  rw [Finset.sum_apply]
  simp_rw [Pi.smul_apply, he, smul_zero, Finset.sum_const_zero]
  rw [add_zero]
  unfold fullH
  rw [neg_neg]

lemma LC_read (i : Nm) (j : Qm) : docket n PR [ak G n i, cc G n j] = fullD G n i j := by
  rw [Wilsonian.witnessD]
  let X := ak G n i
  let V := cc G n j
  let u := (Ζ).AId (linkEquiv G n i)
  let L := Chart.loco Rt (G := G)
  change (D ((U).dual u) (Taylor.ink _ _ + (U).hung _)) [V] = _
  rw [map_add, Taylor.ink_off _ ((F).dual_off _), zero_add,
    (Bonded.Lifted.acted (lifting (F) CP L (Chart.ride Rt)) u), (show (U).fee u = (1 : ℂ) from rfl),
    one_smul, show launch _ _ _ u = stone (F) L _ from launch_stone ..]
  classical
  let f := siteEquiv G n j
  have hx : V = (U).plain ((Ζ).KId f) := rfl
  unfold stone
  rw [Finset.sum_apply]
  have hv a (Z : Raw (FixedMode G n) ℂ) :
    product σbranch ((Ζ).spark a) Z [V] = (D V ((Ζ).spark a)) [] * Z [] := by
    rw [D_eval V (product _ _ _), D_product]
    simp [spark, atLetter]
  rw [Finset.sum_eq_single_of_mem f (mem_univ _), hv f, hx, spark_me]
  exact one_mul _
  intro y _ hy
  rw [hv y, hx, spark_far _ _ (Ne.symm hy), Pi.zero_apply, zero_mul]

lemma gradFull (x : Site n) (y : Axis) (i : G.ColorIndex) (c : GaugeField G n) :
    fullD G n ((y, i), x) c = ↑(priv (siteEquiv G n c) (x + step y) i - priv (siteEquiv G n c) x i) := by
  change (↑(projector ((x, y), i) _) : ℂ) = _
  rw [projector_k, Chart.consulted, Pi.zero_apply, Maurer.volt_zero]
  rfl
end

private lemma picks_column {J : Type} [DecidableEq J] [Fintype J] (f : J → BH G)
    (W : FixedMode G n → ℂ) (i : J × Site n) :
    ∑ x : FixedMode G n, fourier G n x (Prod.map f id i) * W x =
      ∑ x : J × Site n, FFT.forward J n x i * W (Prod.map f id x) := by
  classical
  change (∑ x : BH G × Site n, _) = _
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type (α₁ := J)]
  rw [Finset.sum_eq_single_of_mem (s := Finset.univ) (f i.1) (mem_univ _),
    Finset.sum_eq_single_of_mem (s := Finset.univ) i.1 (mem_univ _)]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [fourier, FFT.forward]
  · intro j _ hj
    simp [FFT.forward, hj]
  intro j _ hj
  simp [fourier, hj]

lemma fft_symbol {J Q : Type} [DecidableEq J] [DecidableEq Q] [Fintype J] [Fintype Q] (f : J → BH G)
    (g : Q → BH G) (F : Dot G Cover) (v : J × Site n) (w : Q × Site n) :
    let f₁ : J × Site n → FixedMode G n := Prod.map f id;
    let g₁ : Q × Site n → FixedMode G n := Prod.map g id
    let T : Matrix (J × Site n) (Q × Site n) ℂ := Matrix.of (fun i j => docket n F [f₁ i, g₁ j])
    ((FFT.forward J n)ᵀ * T * FFT.forward Q n) v w = Bulk G n (sleeve lace (run F)) [f₁ v, g₁ w] := by
  intro X Y U
  let L := docket n F
  change ((FFT.forward J n)ᵀ * U * FFT.forward Q n) v w = _
  rw [← unmarked_fourier]
  change _ = D (Y w) (D (X v) (specialize Γ L)) []
  rw [specialize_deriv, map_sum, Finset.sum_apply]
  simp_rw [map_smul, specialize_deriv, Pi.smul_apply]
  simp_rw [Finset.sum_apply, Pi.smul_apply, specialize_nil, at_D, smul_eq_mul]
  rw [picks_column G n f (fun i => ∑ x : FixedMode G n, Γ x (Y w) * L [i, x]) v]
  simp_rw [show ∀ i : J × Site n, (∑ x : FixedMode G n, Γ x (Y w) * L [Prod.map f id i, x]) = _ from
      fun i => picks_column G n g (fun j => L [Prod.map f id i, j]) w]
  simp_rw [Matrix.mul_apply, transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  change _ * L [Prod.map f id i, Prod.map g id j] * _ = _
  ring

def angularP : Matrix (SiteField G n) (SiteField G n) ℂ :=
  (FFT.forward (Ax G) n)ᵀ * fullH G n * FFT.forward (Ax G) n

def angularD : Matrix (SiteField G n) (GaugeField G n) ℂ :=
  WAᵀ * fullD G n * WC

lemma flat_from (i j : FixedMode G n) : flatH G n [i, j] = Bulk G n (sleeve lace (run PR)) [i, j] := by
  have he : Tone.Frame.s₀ G = Book.mask 2 (run PR) := by
    rw [Tone.Frame.s₀, Wilsonian.at_rest]
    exact Tone.grade _ _
  unfold flatH
  rw [he, bulkZ, bulkZ]
  simp_rw [Orbit.point, sleeve_here,
    enough _ (show ((Orbit.stage [i, j]).length : ℤ) = 2 from by simp [Orbit.stage])]

lemma HHF (a b : SiteField G n) : angularP G n a b = -flatH G n [aa G n a, aa G n b] := by
  have h := fft_symbol G n (atomA G) (atomA G) PR a b
  rw [flat_from]
  let T : Matrix (SiteField G n) (SiteField G n) ℂ :=
    Matrix.of (fun i j => docket n PR [aa G n i, aa G n j])
  rw [← (show (WAᵀ * T * WA) a b = _ from h),
    show T = -fullH G n from funext fun i => funext fun j => AA_read G n i j, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.neg_apply, neg_neg]
  rfl

lemma DDF (a b) : angularD G n a b = flatH G n [ak G n a, cc G n b] := by
  have h := fft_symbol G n (atomK G) (atomC G) PR a b
  rw [flat_from]
  let T : Matrix (SiteField G n) (GaugeField G n) ℂ :=
    Matrix.of (fun i j => docket n PR [ak G n i, cc G n j])
  rw [← (show (WAᵀ * T * WC) a b = _ from h),
    show T = fullD G n from funext fun i => funext fun j => LC_read G n i j]
  rfl
end YM.WilsonMS.Position
