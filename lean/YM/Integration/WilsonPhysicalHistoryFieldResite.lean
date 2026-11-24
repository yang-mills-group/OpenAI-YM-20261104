import YM.Integration.WilsonPhysicalHistoryFieldBank
import YM.FormalBulk08.Firth.Turn

/-! Exact covariance of all original physical derivative words under the
literal finite preimage displacement of the filed incoming field. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryFieldResite
open Function Finset Lattice RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Exterior Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm Dove.Lab
open Source Labels PowerSeries MSbar MSbar.Whisk Push.Uniform
open WilsonPhysicalHistoryFieldDerivatives WilsonPhysicalHistoryFieldBank
open FVA1Physical.Round2.Curvature
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {r : ℕ}

def shift (x : Site n) : Primary n G ≃ Primary n G :=
  (coordinates G n).trans ((Lotus.tint x).trans (coordinates G n).symm)

private theorem zone (z x : Site n) (v : Fin r → Primary n G) :
    Whisk.zone (Measuring.chart n G) {z+x} (List.ofFn (shift x ∘ v)) =
    (Whisk.zone (Measuring.chart n G) {z} (List.ofFn v)).image (fun q=>q+x) := by
  classical
  simp only [Whisk.zone,Finset.image_union,Finset.image_singleton]
  congr 1
  ext y
  simp only [Finset.mem_image,List.mem_toFinset,List.mem_map,List.mem_ofFn',Set.mem_range]
  constructor
  · rintro ⟨_,⟨j,rfl⟩,rfl⟩
    exact ⟨_,⟨_,⟨j,rfl⟩,rfl⟩,rfl⟩
  · rintro ⟨_,⟨_,⟨j,rfl⟩,rfl⟩,rfl⟩
    exact ⟨_,⟨j,rfl⟩,rfl⟩

private theorem geometry (a : ℝ) (s : ℕ) (z x : Site n) (v : Fin r → Primary n G) :
    Whisk.spread (Measuring.chart n G) {z+x} a s (List.ofFn (shift x ∘ v)) =
    Whisk.spread (Measuring.chart n G) {z} a s (List.ofFn v) := by
  unfold Whisk.spread
  rw [zone]
  simp only [Whisk.extent,Finset.sup_image,Function.comp_def,Lattice.separation_translate]

private theorem tensor (x : Site n) (Y : Orb.Pap (wire G n)) (e : ℕ) (v : Fin r → Primary n G) :
    Whisk.read 0 (List.ofFn (shift x ∘ v)) (PowerSeries.coeff e (primary n (Kemp.resite x Y))) =
    Whisk.read 0 (List.ofFn v) (PowerSeries.coeff e (primary n Y)) := by
  simp only [WilsonPhysicalHistoryFieldBank.primary,PowerSeries.coeff_map]
  change Whisk.read 0 (List.ofFn (shift x ∘ v))
      (MvPolynomial.rename (coordinates G n).symm (PowerSeries.coeff e (Kemp.resite x Y))) =
    Whisk.read 0 (List.ofFn v) (MvPolynomial.rename (coordinates G n).symm (PowerSeries.coeff e Y))
  rw [WilsonPhysicalHistoryFieldDerivatives.kernel (coordinates G n) r _ (shift x ∘ v),
    WilsonPhysicalHistoryFieldDerivatives.kernel (coordinates G n) r _ v]
  change _ * rancho (Kemp.resite x Y) e r (coordinates G n ∘ shift x ∘ v) =
    _ * rancho Y e r (coordinates G n ∘ v)
  rw [Firth.resite_grade]
  congr 1
  unfold Kemp.carries jetty
  congr 1
  funext j
  apply Prod.ext <;> simp [shift,coordinates,Lotus.tint]

/-- Co-moving the actual torus bank and its anchor preserves the *entire*
physical derivative seminorm, at any coupling coefficient and angular rank. -/
theorem ordered (a : ℝ) (s : ℕ) (z x : Site n) (Y : Orb.Pap (wire G n)) (e r : ℕ) :
    Whisk.lump (Measuring.chart n G) {z+x} a s r 0 (PowerSeries.coeff e (primary n (Kemp.resite x Y))) =
    Whisk.lump (Measuring.chart n G) {z} a s r 0 (PowerSeries.coeff e (primary n Y)) := by
  classical
  let F (v : Fin r→Primary n G) := Whisk.rate (Measuring.chart n G) {z+x} a s 0
    (PowerSeries.coeff e (primary n (Kemp.resite x Y))) (List.ofFn v)
  simp only [Whisk.lump,word_function_sum]
  calc
    _ = ∑ v : Fin r→Primary n G, F (shift x ∘ v) :=
      ((Equiv.piCongrRight fun _ : Fin r=>shift (G:=G) x).sum_comp F).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      unfold F Whisk.rate
      rw [geometry,tensor]

theorem funded (a : ℝ) (s m : ℕ) (z x : Site n) (Y : Orb.Pap (wire G n)) (e : ℕ) (t : ℝ)
    (h : Whisk.Vault (Measuring.chart n G) {z} a s m 0 (PowerSeries.coeff e (primary n Y)) t) :
    Whisk.Vault (Measuring.chart n G) {z+x} a s m 0
      (PowerSeries.coeff e (primary n (Kemp.resite x Y))) t :=
  ⟨h.1,fun r hr => (ordered a s z x Y e r).le.trans (h.2 r hr)⟩

end YM.Integration.WilsonPhysicalHistoryFieldResite

