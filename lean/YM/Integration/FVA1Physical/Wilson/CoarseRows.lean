import YM.Integration.FVA1Physical.Wilson.RowTransport

/-! Spatially rooted coefficient bounds on the physical coarse chart.
The field substitution is the derivative of the genuine stationary point,
and retains the independent conditional Wilson denominator. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH MSbar.Measuring
open PhysicalNext.Repeat.Legato Push.Uniform MSbar.Midpoint MSbar.Bakery.Film
open scoped Classical Topology BigOperators
variable {G:Gauge}

def emittedRows (A:Issue G) (χ:ChartRatio G) (src:PowerSeries (Pot (Joint A.F G))) (p:ℕ) :=
  PowerSeries.map (rail (poring A.F A.ρ)).toRingHom (normalizedRows A χ src p)

private theorem readPoint (A:Issue G) (branch:A.S.patch.Branches A.S.kernel G)
    (prem:Premier (main A.f A.pre.clip A.pre.path))
    (crit:Critical A.F A.pre.clip A.pre.path A.ρ) (pd:(mold A.pre A.F A.v).PosDef)
    (z:Positions (Primary A.c G)) :
    poring A.F A.ρ *ᵥ (A.fClock⁻¹ • z) = bulkPoint A z := by
  rw [stationary_point A branch prem crit pd z,poring,LinearMap.toMatrix'_mulVec]
  rfl

theorem emitted_read (A:Issue G) (χ:ChartRatio G) (src:PowerSeries (Pot (Joint A.F G))) (p i:ℕ)
    (branch:A.S.patch.Branches A.S.kernel G) (prem:Premier (main A.f A.pre.clip A.pre.path))
    (crit:Critical A.F A.pre.clip A.pre.path A.ρ) (pd:(mold A.pre A.F A.v).PosDef)
    (z:Positions (Primary A.c G)) :
    PowerSeries.coeff i (bulkColumn A χ z src p) =
      MvPolynomial.eval (A.fClock⁻¹ • z) (PowerSeries.coeff i (emittedRows A χ src p)) := by
  rw [normalizedRows_read,emittedRows,PowerSeries.coeff_map]
  change _ = MvPolynomial.eval _ (rail _ _)
  rw [show MvPolynomial.eval _ (rail _ _) = _ from congr_fun (Rolling.clearL _ _) _,readPoint A branch prem crit pd]

theorem coarse_vault {c n:Side} (g:Ratio c n) {ι:Type} [Fintype ι] (l:ι→Site c)
    (W:Finset (Site c)) {a b B:ℝ} (ha:0≤a) (hb:b≤a*g.count.val) (s h:ℕ) (z:View ι) (f:Pot ι)
    (budget:Vault (g.embed ∘ l) (W.image g.embed) a s h z f B) : Vault l W b s h z f B := by
  refine ⟨budget.1,fun k hk=>le_trans ?_ (budget.2 k hk)⟩
  unfold lump
  apply shiny
  intro T _
  let U:= zone l W T
  let V:= zone (g.embed ∘ l) (W.image g.embed) T
  have part (x:Site c) (hx:x∈U) : g.embed x∈V:=by
    rcases Finset.mem_union.mp hx with h|h
    · exact mem_union_left _ (mem_image_of_mem _ h)
    · obtain ⟨i,hi,eq⟩:=List.mem_map.mp (List.mem_toFinset.mp h)
      exact mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,hi,congr_arg g.embed eq⟩))
  have lengths:g.count.val * extent U ≤ extent V := by
    by_cases h:U.Nonempty
    · obtain ⟨i,hi,hq⟩:=exists_mem_eq_sup U h fun i=>Finset.sup U (fun j=>separation i j)
      obtain ⟨j,hj,hd⟩:=exists_mem_eq_sup U h fun j=>separation i j
      rw [show extent U=separation i j from hq.trans hd]
      exact (Corona.below g i j).trans (curve (part _ hi) (part _ hj))
    rw [Finset.not_nonempty_iff_eq_empty.mp h];simp [extent]
  have he:extent U ≤ extent V := (Nat.le_mul_of_pos_left _ g.count.property).trans lengths
  have hx:b*(extent U) ≤ a*(extent V) := by
    have step:=mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg (α:=ℝ) (extent U))
    rw [mul_assoc,←Nat.cast_mul] at step
    exact step.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr lengths) ha)
  apply mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  change (1+(extent U:ℝ))^s * Real.exp (b*extent U) ≤ (1+(extent V:ℝ))^s*Real.exp (a*extent V)
  exact mul_le_mul (pow_le_pow_left₀ (by positivity : 0≤1+(extent U:ℝ)) (by exact_mod_cast Nat.add_le_add_left he 1) s)
    (Real.exp_monotone hx) (Real.exp_pos _).le (by positivity)

theorem emitted_rows (A:Issue G) (χ:ChartRatio G) (src:PowerSeries (Pot (Joint A.F G))) (p i s q:ℕ)
    (branch:A.S.patch.Branches A.S.kernel G) (prem:Premier (main A.f A.pre.clip A.pre.path))
    (crit:Critical A.F A.pre.clip A.pre.path A.ρ) (pd:(mold A.pre A.F A.v).PosDef)
    (b:Site A.c) (z:Positions (Primary A.c G)) {α β C B:ℝ} (ha:0≤α) (hb:β ≤ α*A.S.ratio.count.val)
    (land:Syrup (address A.F G) (Tramp.path A.S.ratio G) α s (poring A.F A.ρ) C)
    (income:Vault (address A.F G) {A.S.ratio.embed b} α s q (bulkPoint A z)
      (PowerSeries.coeff i (normalizedRows A χ src p)) B) :
    Vault (Measuring.chart A.c G) {b} β s q (A.fClock⁻¹ • z)
      (PowerSeries.coeff i (emittedRows A χ src p)) (C^q*B) := by
  apply coarse_vault A.S.ratio _ {b} ha hb
  simp only [Finset.image_singleton,emittedRows,PowerSeries.coeff_map]
  apply rooted_vault_pullback (address A.F G) (Tramp.path A.S.ratio G) (poring A.F A.ρ) s q ha land
  rw [readPoint A branch prem crit pd]
  exact income

end YM.Integration.FVA1Physical.Wilson
