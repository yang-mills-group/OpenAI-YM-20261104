import YangMills.WilsonProof.NativeSupport.JointLinearPicture
import YangMills.WilsonProof.NativeSupport.FrozenPlanted

/-! The exact canonical basis cost for a frozen word and the genuine signed
two-placement difference. Independent positions enter through their own stencils. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset Lattice RG Wilson RGComparison.Core16
open WilsonUniformUnmarkedInletEnergySites WilsonUniformUnmarkedInletBondRemainder
open Next.Foundations Labels JointMoments
open scoped Classical BigOperators
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] {n c:Side}

theorem word_picture (d:Descent n c) (ok:d.OK G) (β δ:ℕ→ℝ) (r:ℝ)
    (grade:I→ℕ) (label:(i:I) → ((frames G).level (grade i)).Index) (a:I → Site n)
    (b:Bool) {ε:ℝ} (s:ℕ) (stencils:∀ i,minSide G (grade i) ≤ s)
    (allWords:∀ (F:I → Config G n → ℝ), (∀ i,Continuous (F i)) → (∀ i,GaugeInvariant (F i)) →
      (∀ i U,|F i U| ≤ 1) → (∀ i,LocalOn (halo s {a i}) (F i)) →
      (∑ q∈interior d,|picture d β δ 1 (fun X=>∏ i,F i X) r q|) ≤ ε):
    (∑ q∈interior d,|picture d β δ 1 (wordAt grade label a b) r q|) ≤ 2^(Fintype.card I)*bill grade G*ε := by
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
  have cmp σ : (∑ q∈interior d,|picture d β δ 1 (Z σ) r q|) ≤ ε := allWords _ (cont σ) (gauge σ) (unit σ) (localF σ)
  have Bpos : 0≤bill grade G := prod_nonneg fun i _=>(posP i).le
  have bound σ : |c σ| ≤ bill grade G := by
    change |component b (∏ i,phase (σ i))*bill grade G| ≤ bill grade G
    rw [abs_mul,abs_of_nonneg Bpos]
    apply mul_le_of_le_one_left Bpos
    exact (component_norm ..).trans_eq (by rw [norm_prod];simp [phase_norm])
  have rep (U : Config G n) : wordAt grade label a b U=∑ σ: I→Bool,c σ*Z σ U := by
    rw [show wordAt grade label a b U=component b (∏ i,atom grade label a i U) from rfl,component_product]
    apply sum_congr rfl
    intro σ _
    dsimp only [c,Z,F]
    rw [prod_div_distrib]
    change _=(_*bill grade G)*(_/bill grade G)
    have bp : 0<bill grade G := prod_pos fun i _=>posP i
    field_simp
  have ctZ σ:Continuous (Z σ):=continuous_finsetProd _ fun i _=>cont σ i
  have gZ σ:GaugeInvariant (Z σ):=fun k X=>prod_congr rfl fun i _=>gauge σ i k X
  rw [funext rep]
  calc
    _ ≤ _ := abs_picture_linear d ok β δ 1 r univ c Z (fun σ _=>ctZ σ) (fun σ _=>gZ σ)
    _ ≤ ∑ _σ:I→Bool,bill grade G*ε := sum_le_sum fun σ _=>mul_le_mul (bound σ) (cmp σ) (sum_nonneg fun q _=>abs_nonneg _) Bpos
    _ = _ := by simp;ring

theorem difference_picture (d:Descent n c) (ok:d.OK G) (β δ:ℕ→ℝ) (r:ℝ)
    (f e:Config G n → ℝ) (cf:Continuous f) (ce:Continuous e) (gf:GaugeInvariant f) (ge:GaugeInvariant e):
    (∑ q∈interior d,|picture d β δ 1 (fun X=>f X-e X) r q|) ≤
      (∑ q∈interior d,|picture d β δ 1 f r q|)+(∑ q∈interior d,|picture d β δ 1 e r q|) := by
  let F (b:Bool):=if b then f else e
  let a (b:Bool):ℝ:=if b then 1 else -1
  have ct (b:Bool):Continuous (F b):=by cases b <;> first | exact ce | exact cf
  have sym (b:Bool):GaugeInvariant (F b):=by cases b <;> first | exact ge | exact gf
  have p:=abs_picture_linear d ok β δ 1 r univ a F (fun b _=>ct b) (fun b _=>sym b)
  simpa [Fintype.sum_bool,a,F,sub_eq_add_neg,add_comm] using p

end YM.Integration.InletSusceptibility.Packet
