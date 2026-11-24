import YM.Integration.FVA1Physical.Sources.Round2.PurchasedFieldTaylor
import YM.Integration.FVA1Physical.Sources.Round2.DistributedFields

/-! The source error required by the nonlinear normalized Lapaz expansion, on
its actual shifted conditional Gaussian and including inherited backgrounds. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Matrix Function Filter Set Finset Lattice RG YM.Wilson Tree Precision Exterior Pressure
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open MSbar MSbar.Whisk MSbar.Bout MSbar.Cacao MSbar.Lis MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal
open Push.Uniform Next.SectorChange MSbar.Jade YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι→Lamp G)

theorem field_taste (A : Mosaic.Issue G) (V : Voice G) (o : ι→Site A.f) (X Y : Support A.f)
    (live : ∀ i,slotEdge J A.S A.F o i∈board A.F X) (U : Config G A.f)
    (Z : Positions (Primary A.c G)) (g : ℝ) (x : SpaceP A.F X G) (part : Bool) (n : ℕ) :
    let t:=sampleY A.F A.pre A.v V X Y U (g•Z) ∘ includeX A.F X
    taste n (picture (meetVar Z (berth A.F A.pre A.v V X Y U Z g x)) (jointFieldBank J A o part)) g =
      fieldTaylor J A.S A.F o X live t g part n x := by
  intro t
  unfold taste picture fieldTaylor jointFieldBank
  apply sum_congr rfl
  intro k _
  apply congrArg (g^k*·)
  rw [PowerSeries.coeff_map,PowerSeries.coeff_mk,MvPolynomial.eval_rename]
  apply congrArg (fun s => MvPolynomial.eval s (lampRow J part (activeSlots J A.S A.F o) k))
  funext j
  let s:=slotPrices J A.S A.F o X live j
  let idx:=includeX (G:=G) A.F X
  change g⁻¹*sampleY A.F A.pre A.v V X Y U (g•Z) (idx s) +
      ((imbed idx)*ᵥ x) (idx s)=g⁻¹*sampleY A.F A.pre A.v V X Y U (g•Z) (idx s)+x s
  exact congrArg (_+·) (congrFun (Kelvin.shares idx (secureY A.F X G) x) s)

/-- Pointwise source constraint of the normalized nonlinear Lapaz ratio theorem.
Every conditional draw in the real chart has the claimed error, and the field
polynomial used inside the formal Gaussian is exactly the FVA2 source. -/
theorem field_salary_input (part : Bool) (p : ℕ) :
    ∃ δ C:ℝ, 0<δ ∧ 0≤C ∧ ∀ (A : Mosaic.Issue G) (V : Voice G) (_ : Clear G V) (χ : ChartRatio G)
      (_ : LocalRatio χ) (o : ι→Site A.f) (X Y : Support A.f)
      (_ : ∀ i,slotEdge J A.S A.F o i∈board A.F X) (U : Config G A.f) (Z : Positions (Primary A.c G))
      (g a b K H M : ℝ), 0<g → 3*shade G*K≤δ → X⊆Y →
      let O:=represent (tint G (Exterior.Body 1 A.c) (g•Z))
      let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) (g•Z)
      let m:=sampleY A.F A.pre A.v V X Y U (g•Z) ∘ includeX A.F X
      Couch V A.F ν Y χ (linCash A.F (g•Z)) O a b K H M →
      ∀ x∈clipM A.F X Y (hotel A.F X Y V O ν a b) χ g m U,
      |look part (tally J o (draw A.F X U m g x)) -
        taste p (picture (meetVar Z (berth A.F A.pre A.v V X Y U Z g x)) (jointFieldBank J A o part)) g| ≤
        C*(3*shade G*K)^(p+1) := by
  obtain ⟨δ,C,hδ,hC,price⟩:=drawn_remainder J part p
  refine ⟨δ,C,hδ,hC,?_⟩
  intro A V clear χ hχ o X Y live U Z g a b K H M hg room xy O ν m paid x hx
  let s:=slotPrices J A.S A.F o X live
  let q:=fun i=>g⁻¹*m (s i)+x (s i)
  have k0:0≤K:=le_trans (add_nonneg (norm_nonneg _) (paid.glued.le.trans paid.lifts)) paid.ht
  have hrate : 0≤3*shade G*K:= mul_nonneg (mul_nonneg (by norm_num) (shade_pos G).le) k0
  have gs : g • Lumen.vector q = fun i=>tape (G:=G) (m+g•x) (⟨slotEdge J A.S A.F o i,live i⟩) := by
    funext i;apply PiLp.ext;intro k
    change g*(g⁻¹*m (s (i,k))+x (s (i,k)))=m (s (i,k))+g*x (s (i,k))
    rw [mul_add,←mul_assoc,mul_inv_cancel₀ hg.ne',one_mul]
  have cap : g*‖Lumen.vector q‖≤3*shade G*K:=by
    rw [←norm_smul_of_nonneg hg.le,gs]
    exact (pi_norm_le_iff_of_nonneg hrate).mpr fun i=>drawn_log_cap A.F V X Y O U ν χ hχ clear _ paid xy m x hx ⟨_,live i⟩
  rw [field_taste J A V o X Y live U Z g x part p,←Real.norm_eq_abs]
  exact (price A.S A.F o X live U m x g hg (cap.trans room)).trans ((le_of_eq (by rw [mul_pow];ring :
    C*‖Lumen.vector q‖^(p+1)*g^(p+1)=C*(g*‖Lumen.vector q‖)^(p+1))).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hg.le (norm_nonneg _)) cap _) hC))

end YM.Integration.FVA1Physical.Round2.Curvature
