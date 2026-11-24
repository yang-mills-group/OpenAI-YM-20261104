import YM.Integration.FVA1Physical.Wilson.DistributedPurchase

/-! All finite mixed blocking-source columns on the genuine distributed
incoming action. The derivative root may vary anywhere in the torus and all
marked positions may range over the expanding native collar. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MeasureTheory Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Duel MSbar.Bout
open MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling
open PhysicalNext.Repeat.Legato Push.Uniform Pressure RGComparison.Core16 Next.SectorChange
open scoped Classical Topology
variable {G : Gauge}

theorem distributed_scores (J : Voice G) (clear : Clear G J) (χ : ChartRatio G) (hχ : LocalRatio χ)
    (simple : G.Simple) (H H' : Stage) (P : Patch) (K : KernelChoices) (branch : P.Branches K G)
    (p s q d L : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (b : Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      ‖z‖ ≤ A.fClock*D →
      let y:=tip G P.L x
      Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      ∀ ℓ:List (Primary A.c G), ℓ.length ≤ d → ranged A.F ℓ b (L*closeN y) →
      let src:=Duel.readScore (Duel.hands A.F G) (Duel.stampD A.F A.v G) (barbed A.F A.v χ A.T) ℓ
      ∀ U∈hotel A.F (boxX y b) (boxY y b) J (represent (tint G (Exterior.Body 1 A.c) z))
        (vest (priced A.F A.v A.pre.clip A.pre.path) z) (pillow y) (room y),
      ∀ i ≤ p, |PowerSeries.coeff i (bulkColumn A χ z src p) -
        PowerSeries.coeff i (innerColumn A χ J y z b U src p)| ≤ y^(-(q:ℝ)) := by
  let m:=(d+1)*(p+2)
  have hm:p+2 ≤ m:=by exact le_mul_of_one_le_left (Nat.zero_le _) (Nat.succ_pos d)
  obtain ⟨I⟩:=pre_order G H'.width H'.paths P.J K (n:=p+3) (by omega)
  let B:=Ruby.milkR I P 1 s (m+d) p
  let X:=fun x:ℝ=>tip G P.L x
  have rise : Tendsto X atTop atTop:=Work.E09.betaF_growth G P.L
  let rootWeight:=fun x=>liftW (αm (X x)) s (L*closeN (X x))
  have hroot:Mosaic.Run atTop X rootWeight 0:= by
    simpa only [one_mul] using (Mosaic.Issue.nearB rise 1 zero_lt_one s L).2
  let fee(x):=1+(2:ℝ)^d*((p+1:ℕ)*(2^m*(rootWeight x*B)))
  have hfee:Mosaic.Run atTop X fee 0:= (Mosaic.Run.token rise 1).addR rise
    ((((hroot.mulY rise B).mulK rise (2^m)).mulK rise ((p+1:ℕ):ℝ)).mulK rise (2^d))
  filter_upwards [distributed_columns J clear χ hχ simple H H' P K branch p s m q hm hD,
    (hfee.Ypow rise d) 1 zero_lt_one, (Alto.broad.comp rise).eventually_ge_atTop 1,
    Mosaic.Issue.gate (tendsto_id : Tendsto (fun x:ℝ=>x) atTop atTop) simple tendsto_id P.L m]
    with x offer price wide gate
  intro A z b patch ker season hz y kind plane wedge ℓ count local_ src
  have theta0 : 0 ≤ αm y := by unfold αm hatW Alto.flurry; positivity
  have rate : αm y ≤ 1:=gate.2.2.1.trans ((one_div_le_one_div_of_le one_pos
    (one_le_pow₀ wide : 1 ≤ (hatW y)^2)).trans_eq (div_one _))
  have raw (i:ℕ)(hi:i ≤ p) := (Ruby.antigen A.F A.v χ s I ker season.bends hχ 1 theta0 rate p
    (by omega) (m+d) i hi).1
  simp only [patch] at raw
  have bound:=Bout.hearts A.F A.v ℓ p b raw local_ theta0 rfl count (le_refl (m+d))
  have bpos : 0 ≤ B:=(raw p le_rfl).1
  have fpos : 1 ≤ fee x :=by
    dsimp only [fee,rootWeight]
    have nn:= (wpos (αm (X x)) s (L*closeN (X x))).le
    apply le_add_of_nonneg_right
    positivity
  have paid : (fee x)^d ≤ y:=by simpa only [Real.rpow_one] using (le_abs_self _).trans price
  have eqn : src = cycleP A.F A.v ℓ := congrFun (Duel.hand A.F A.v χ A.T hχ kind) ℓ
  rw [eqn]
  apply offer A z b patch ker season hz kind plane wedge
  intro i hi
  have data:=bound i hi
  refine ⟨Quote.widen data.1 ((pow_le_pow_right₀ fpos count).trans paid) le_rfl, data.2.trans ?_⟩
  exact Nat.mul_le_mul_right _ (count.trans (Nat.le_succ _))
end YM.Integration.FVA1Physical.Wilson
