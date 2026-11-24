import YangMills.WilsonProof.NativeSupport.FrozenAtoms
import YangMills.WilsonProof.NativeSupport.EveryPattern

/-! The exact finite physical basis word, with every original spectator
retained. Its normalizing bill depends on the occupied grades alone. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset MeasureTheory Lattice RG Wilson RGComparison.Core16
open WilsonUniformUnmarkedInletConnectedCovariance Next.Foundations Labels
open scoped Classical BigOperators
variable {G : Gauge} {n c : Side}

theorem mean_mul_const (d : Descent n c) (β : ℕ → ℝ) (V : Config G c) (t : ℝ) (F : Config G n → ℝ) :
    mean d β (fun U=>t*F U) V=t*mean d β F V := by
  unfold mean
  rw [←mul_div_assoc]
  congr 1
  unfold mass
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [←integral_const_mul]
  apply integral_congr_ae (.of_forall _)
  intro U
  simp only [Descent.integrand]; ring

theorem mean_difference (d : Descent n c) (ok : d.OK G) (β : ℕ→ℝ) (V : Config G c)
    (f h : Config G n→ℝ) (cf : Continuous f) (ch : Continuous h) :
    mean d β (fun U=>f U-h U) V=mean d β f V-mean d β h V := by
  unfold mean
  rw [←sub_div]
  congr 1
  unfold mass
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  rw [←integral_sub (d.path_integrable ok β j f cf V) (d.path_integrable ok β j h ch V)]
  exact integral_congr_ae (.of_forall fun U=>by simp only [Descent.integrand,mul_sub])

variable {I : Type} [Fintype I] [DecidableEq I]

def bill (grade : I → ℕ) (G : Gauge) := ∏ i,atomPrice G (grade i)
def atom {n : Side} (grade : I → ℕ) (label : (i:I) → ((frames G).level (grade i)).Index)
    (a : I → Site n) (i : I) := (localSection G (grade i)).places (Pi.single (label i) 1) (a i)

theorem word_cost (d : Descent n c) (ok : d.OK G) (Y B : ℕ → ℝ)
    (grade : I → ℕ) (label : (i:I) → ((frames G).level (grade i)).Index) (a : I → Site n)
    (b : Bool) {ε : ℝ} (s : ℕ) (stencils : ∀ i,minSide G (grade i) ≤ s)
    (allWords : ∀ (F : I → Config G n → ℝ), (∀ i,Continuous (F i)) → (∀ i,GaugeInvariant (F i)) →
      (∀ i U,|F i U| ≤ 1) → (∀ i,LocalOn (halo s {a i}) (F i)) →
      |mean d Y (fun U=>∏ i,F i U) 1-mean d B (fun U=>∏ i,F i U) 1| ≤ ε) :
    let W:=fun U=>component b (∏ i,atom grade label a i U)
    |mean d Y W 1-mean d B W 1| ≤ 2^(Fintype.card I)*bill grade G*ε := by
  intro W
  let price (i:I):=atomPrice G (grade i)
  let F (σ : I→Bool) (i:I) (U:Config G n):=component (σ i) (atom grade label a i U)/price i
  let Z (σ : I→Bool) (U : Config G n):=∏ i,F σ i U
  let c (σ : I→Bool):=component b (∏ i,phase (σ i))*bill grade G
  have posP i : 0<price i := zero_lt_one.trans_le (atom_one G _)
  have cont σ i : Continuous (F σ i) :=
    ((component _).continuous.comp ((localSection G (grade i)).continuous_places _ _)).div_const _
  have gauge σ i : GaugeInvariant (F σ i) := fun h U=>congrArg (fun x=>component (σ i) x/price i)
    ((localSection G (grade i)).placed_invariant (sound G _) _ _ h U)
  have localF σ i : LocalOn (halo s {a i}) (F σ i) := fun U V h=>congrArg
    (fun x=>component (σ i) x/price i) (atom_local (grade i) (label i) _ (stencils i) U V h)
  have unit σ i U : |F σ i U| ≤ 1 := by
    change |component (σ i) (atom grade label a i U)/price i| ≤ 1
    rw [abs_div,abs_of_pos (posP i),div_le_one (posP i)]
    exact (component_norm _ _).trans (atom_bound _ _ _ _)
  have cmp σ : |mean d Y (Z σ) 1-mean d B (Z σ) 1| ≤ ε := allWords _ (cont σ) (gauge σ) (unit σ) (localF σ)
  have Bpos : 0≤bill grade G := prod_nonneg fun i _=>(posP i).le
  have bound σ : |c σ| ≤ bill grade G := by
    change |component b (∏ i,phase (σ i))*bill grade G| ≤ bill grade G
    rw [abs_mul,abs_of_nonneg Bpos]
    apply mul_le_of_le_one_left Bpos
    exact (component_norm ..).trans_eq (by rw [norm_prod];simp [phase_norm])
  have rep (U : Config G n) : W U=∑ σ: I→Bool,c σ*Z σ U := by
    rw [show W U=component b (∏ i,atom grade label a i U) from rfl,component_product]
    apply sum_congr rfl
    intro σ _
    dsimp only [c,Z,F]
    rw [prod_div_distrib]
    change _=(_*bill grade G)*(_/bill grade G)
    have bp : 0<bill grade G := prod_pos fun i _=>posP i
    field_simp
  have reads (γ : ℕ→ℝ) : mean d γ W 1=∑ σ : I→Bool,c σ*mean d γ (Z σ) 1 := by
    rw [funext rep]
    have pieces:=mean_sum d ok γ 1 (fun σ U=>c σ*Z σ U) (fun σ=>continuous_const.mul
      (continuous_finsetProd _ fun i _=>cont σ i))
    exact pieces.trans (sum_congr rfl fun σ _=>mean_mul_const d γ 1 (c σ) (Z σ))
  rw [reads Y,reads B,←sum_sub_distrib]
  calc _ ≤ ∑ σ:I→Bool,|c σ*mean d Y (Z σ) 1-c σ*mean d B (Z σ) 1| := abs_sum_le_sum_abs ..
       _ ≤ ∑ _σ:I→Bool,bill grade G*ε := by
            apply sum_le_sum; intro σ _
            rw [←mul_sub,abs_mul]
            exact mul_le_mul (bound σ) (cmp σ) (abs_nonneg _) Bpos
       _ = _ := by simp;ring

end YM.Integration.InletSusceptibility.Packet
