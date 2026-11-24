import YM.Integration.WilsonUniformUnmarkedCompact

/-! The complete signed physical candidate retains the cover strip at every
occupied field rank. Its price is a polynomial in the original logarithmic
clock, uniform in the upper date, with no coupling-sized compactness cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonUniformUnmarkedSpatialLimit
open Filter Function Finset PowerSeries Lattice RG Wilson Tree Stationary Push.Uniform Bloch Exterior Precision
open FormalBulk08 Jets Flat Reef Mesa Lava Shore Lotus Wine Bank Orb Next.Free Series Gorge
open PhysicalNext.Repeat.Legato MSbar MSbar.Heath MSbar.Rolling MSbar.Cacao MSbar.Midpoint MSbar.Bakery
open RG16 RG16.Literal Pert.Asymptotics WilsonConditionalTaylorBulkHistory WilsonUniformUnmarkedCompact
open scoped Classical Topology BigOperators ENNReal

theorem sides {G : Gauge} (R : Run G) (j : ℕ) : Tendsto (R.family.side j) atTop atTop := by
  have g := (show StrictMono (fun m:ℕ=>(R.family.side j m).val) from fun _ _ h=>
    Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator j).pos).tendsto_atTop
  exact tendsto_atTop.2 fun n=>g.eventually_ge_atTop n.val

theorem bail {I : Type} {r : ℕ} (n : ℕ→Side) (growth : Tendsto n atTop atTop)
    {η C : ℝ} {T : Tile (Biglot I) r} {P : (t:ℕ)→Tile (Tor (n t) I) r}
    (limit : ∀ v, Tendsto (fun t=>P t (drip (n t) ∘ v)) atTop (𝓝 (T v)))
    (bought : ∀ᶠ t in atTop, Bail (lake (n t) I) η (P t) C) : Bail (fame I) η T C := by
  refine ⟨bought.exists.choose_spec.1,fun i a=>?_⟩
  have wide_fixed (v : chain (Biglot I) r) : ∀ᶠ m : Side in atTop,
      wide (lake m I) (drip m ∘ v)=wide (fame I) v := by
    have he (x y: Fin r) := effect ((v x).1-(v y).1)
    filter_upwards [eventually_all.mpr fun x=> eventually_all.mpr (he x)] with m hm
    unfold wide; congr 1; ext ⟨x,y⟩
    change Laurent.size (lift (wrap m _-wrap m _))= Laurent.size ((v x).1-(v y).1)
    rw [←map_sub,hm]
  rw [ENNReal.tsum_eq_iSup_sum,iSup_le_iff]; intro S
  let f (m : Side) : Gorge.pack i a → Gorge.pack i (drip m a) :=
    fun v=>⟨drip m ∘ v.val,congrArg (drip m) v.property⟩
  have good : ∀ᶠ m : Side in atTop,Set.InjOn (f m) S := by
    filter_upwards [S.eventually_all.mpr (fun (v:Gorge.pack i a) _=>eventually_all.mpr fun j=>boil_drip (v.val j))] with m hm t ht p hp e
    apply Subtype.ext;funext j;rw [←hm t ht j,←hm p hp j]
    exact congrArg _ (congrFun (congrArg Subtype.val e) j)
  have ht (v : Gorge.pack i a) : Tendsto (fun t=>glitter (lake (n t) I) η (P t) (f (n t) v).val) atTop
      (𝓝 (glitter (fame I) η T v.val)) := by
    have cont : Continuous (fun x:ℝ=>Gorge.shine η (wide (fame I) v.val)* ‖x‖ₑ) := by
      simp_rw [Gorge.shine,← ofReal_norm, ←ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_norm)
    refine (cont.continuousAt.tendsto.comp (limit v.val)).congr' ?_
    filter_upwards [growth.eventually (wide_fixed v.val)] with t h
    change _=glitter _ η (P t) (drip (n t) ∘ v.val)
    unfold glitter; rw [h]; rfl
  apply le_of_tendsto (tendsto_finsetSum _ (fun x _=>ht x))
  filter_upwards [bought,growth.eventually good] with t h hi
  rw [←Finset.sum_image (f:=fun v=>glitter (lake (n t) I) η (P t) v.val) hi]
  exact (ENNReal.sum_le_tsum _).trans (h.2 i _)

variable {G : Gauge} (R : Run G) (simple : G.Simple) (u : G.ColorIndex) (V : Voice G)
variable (bought : WilsonConditionalTaylorPurchase.Inventory u V R.kit)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags : ∀ j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

include simple bought in
theorem logarithmic (E : ℕ) : ∀ᶠ k : ℕ in atTop, ∀ N per, k ≤ N → ∀ j, k ≤ j → j ≤ N →
    ∀ e, 0<e → e ≤ E → ∀ r, r ≤ e+1 → let n:=R.family.side j per
    Bail (lake n _) (Alto.candles R.family.path.levels j/4) (rancho (course R u wood tags N j n) e (r+1))
      ((Alto.hat R.family.path.levels j)^(Alto.Dean E)) := by
  let C:=R.family
  have wGrow:=Alto.broad.comp (Multi.Wage.hat_tend simple C.path.levels)
  obtain ⟨start,broad⟩:=eventually_atTop.mp (wGrow.eventually_ge_atTop 1)
  filter_upwards [WilsonUniformUnmarkedFiniteStrip.wedge R simple u V bought wood tags 6 E le_rfl,
    eventually_ge_atTop start] with k wedge early N per kN j lo hi e pos cap r val n
  let w:=Alto.hat C.path.levels j
  have w1 : 1≤w:=broad j (early.trans lo)
  have w0:=zero_le_one.trans w1
  have width : 0≤Alto.candles C.path.levels j :=by unfold Alto.candles Alto.cWidth; positivity
  apply WilsonUniformUnmarkedCommonStrip.render (marble_agate _ _) width (pow_nonneg w0 _) 6
  intro i
  let U:=course R u wood tags N j n
  change (∑ t : Fin r→wire G n,WilsonUniformUnmarkedTensorRows.weight n G i t (Alto.candles C.path.levels j) 6*
    |((r+1).factorial:ℝ)*rancho U e (r+1) (Fin.cons i t)|) ≤ _
  rw [WilsonUniformUnmarkedTensorRows.charges U i _ 6 e r pos]
  have h:=((wedge N per kN j lo hi).shares e cap).fan r val ((WilsonMovingGaussianCoordinates.link G n).symm i)
  have cost : w^(Alto.Dean e)/w^(r+1) ≤ w^(Alto.Dean E) :=
    (div_le_self (pow_nonneg w0 _) (one_le_pow₀ w1)).trans (pow_le_pow_right₀ w1 (Alto.ranked cap))
  exact h.trans cost

include simple bought in
theorem physical (E : ℕ) : ∀ᶠ k : ℕ in atTop, ∀ (N per a : ℕ→ℕ) (A : ℕ→Mesa.Pot G),
    Tendsto (N ∘ a) atTop atTop → Tendsto (per ∘ a) atTop atTop → Capped R u wood tags k E N per a A →
    ∀ j, k ≤ j → ∀ e, 0<e → e≤E → ∀ r, r≤e+1 →
    Bail (fame _) (Alto.candles R.family.path.levels j/4) (A j e (r+1))
      ((Alto.hat R.family.path.levels j)^(Alto.Dean E)) := by
  filter_upwards [logarithmic R simple u V bought wood tags E] with k ledger N per a A fine grows paid j lo e pos cap r val
  let n:=fun t=>R.family.side j (per (a t))
  apply bail n ((sides R j).comp grows) (P:=fun t=>rancho (course R u wood tags (N (a t)) j (n t)) e (r+1)) (paid j e r lo pos cap val)
  filter_upwards [fine.eventually_ge_atTop j] with t live
  exact ledger _ _ (lo.trans live) j lo live e pos cap r val

end YM.Integration.WilsonUniformUnmarkedSpatialLimit
