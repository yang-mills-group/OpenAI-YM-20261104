import YM.Integration.WilsonIndependentPublicReportComplex

/-! Apply the actual report to both sides of the finite Wilson-orbit
comparison. The unmarked clock price precedes selection of the exterior. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentPublicReportedOrbit
open Lattice RG XSpace XSpace.Rose XSpace.Cirrus Precision Source PertExtension
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Oracle RegulatorIR.Atlas RegulatorIR.Uniform RegulatorIR.Epoch RegulatorIR.Epoch.League
open RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration RegulatorIR.Taping RegulatorIR.Prim
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit
open WilsonIndependentRawNamedProduct WilsonIndependentMatchedNamedPair
open WilsonIndependentPublicReportComplex (row)
open scoped Classical ENNReal NNReal BigOperators PowerSeries

variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    {H:Hol G}(P:Master H)(chart:ChartRatio G)(K:KernelChoices)(V:XSpace.Run)
    (e h k j:ℕ)(Y:Program K)(branches:∀ p:Patch,p.Branches K G)
    (p b u:ℕ)(γ:ℝ)(extra:ℕ)(col:G.ColorIndex)(late:4 ≤ j)
    (B:WilsonIndependentEvenPassport.Menu P chart K V e h k j extra)

def PaidAt (F:Tent (M V B.a))(aperture:Requests B.a → ℝ)(q D:ℕ)(fee:ℝ)(d:ℕ):Prop:=
    let C:=S V B.a B.positive j late
    ∀ (l r:Bool)(a a':ℕ)(b₁:(R.family.labels.level a).Index)(b₂:(R.family.labels.level a').Index)
      (sample:Requests B.a → Sample 2)(o z:Requests B.a → Cover)(x:Requests B.a → Room)
      (c₀:ℝ), (∀ w,(sample w).F=V.step w.val)  → 
      (∀ w,WilsonIndependentRawPairOpening.span x o z w ≤ aperture w)  →  0<c₀  → 
      (C.dialect Y G branches (sheet F)).cushion c₀ x  → 
    ∃ M₀:ℝ,0 ≤ M₀ ∧ ∃ s:ℕ,∀ (w:Requests B.a)(page:Page (M V B.a)),
      let μ:=(V.step w.val).p.side.val
      let original:=Bare.normalized (W.tree (sample w).F.p) G
        (printed R W (sample w) l a (o w) b₁*printed R W (sample w) r a' (z w) b₂)
      let stopped:ℂ⟦X⟧:=PowerSeries.mk fun i=>(note ((report R W l r a a' b₁ b₂
        (C.payroll Y G branches (sheet F)) o z).main (Page.finallyW (M V B.a) w) i 0):ℂ)
      ‖PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply (F page) D original)-
        PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply (F page) D stopped)‖ ≤ 
        (fee*(1+|Real.log (C.l page)|)^d)*
          (M₀*(1+aperture w+Real.log (μ:ℝ))^s*(μ:ℝ)^(-(γ/2)))
local notation "Here" => PaidAt (R:=R) (W:=W) (P:=P) (chart:=chart) (K:=K) (V:=V)
  (e:=e) (h:=h) (k:=k) (j:=j) (Y:=Y) (branches:=branches) (γ:=γ) (late:=late) (B:=B)

theorem appointed (good:G.Simple)
    (paid:WilsonIndependentTwoMomentGrant.Accounts P chart K V e h k j Y branches
      p b u γ extra col late B)(q:ℕ)(hq:q ≤ p)(D:ℕ):
    let C:=S V B.a B.positive j late
    ∃ fee:ℝ,0 ≤ fee ∧ ∃ d:ℕ,∀ (aperture:Requests B.a → ℝ)(_pos:∀ w,0 ≤ aperture w)
    (F:Tent (M V B.a))(_book:Notebook C Y G branches col (RegulatorIR.FVAAlt2.Rocket.native _) F p),
    WilsonIndependentPublicRawOrbit.Priced R W K Y branches V B.a j B.positive late p γ aperture F →
      Here F aperture q D fee d:=by
  intro C
  obtain ⟨fee,hfee,d,window⟩:=WilsonIndependentPublicClockWindow.original P chart K V e h k j Y
    branches p b u γ extra col late B good paid q hq D
  refine ⟨fee,hfee,d,?_⟩
  intro aperture pos F book orbit
  change ∀ (l r:Bool) (a a':ℕ), _
  intro l r a a' b₁ b₂ sample o z x c₀ same far clear safe
  have h:=orbit l r a a' b₁ b₂ sample o z x c₀ same far clear safe
  choose s₀ m₀ hm pr using fun i:Fin (q+1)=>h i (by omega)
  let cash:=∑ i,m₀ i
  let s:=∑ i,s₀ i
  have cm:0 ≤ cash:=Finset.sum_nonneg (fun i _=>hm i)
  refine ⟨(q+1:ℕ)*cash,by positivity,s,?_⟩
  intro w page μ original stopped
  let L:ℝ:=1+aperture w+Real.log (μ:ℝ)
  have mu:1 ≤ (μ:ℝ):=by exact_mod_cast (V.step w.val).p.side.pos
  have leL:1 ≤ L:=by dsimp [L]; linarith [pos w,Real.log_nonneg mu]
  have hL:0 ≤ L:=by linarith
  let fare:=fee*(1+|Real.log (C.l page)|)^d
  have hfare:0 ≤ fare:=by dsimp [fare];positivity
  let E:=cash*L^s*(μ:ℝ)^(-(γ/2))
  have price (i:Fin (q+1)):
      ‖PowerSeries.coeff (i:ℕ) original-PowerSeries.coeff (i:ℕ) stopped‖ ≤ E:=by
    have earn:=pr i w
    change ‖PowerSeries.coeff (i:ℕ) original-_‖  ≤ m₀ i*L^(s₀ i)*(μ:ℝ)^(-(γ/2)) at earn
    have hc:m₀ i ≤ cash:=Finset.single_le_sum (fun n _=>hm n) (Finset.mem_univ i)
    have hs:s₀ i ≤ s:=Finset.single_le_sum (fun n _=>Nat.zero_le (s₀ n)) (Finset.mem_univ i)
    change ‖PowerSeries.coeff (i:ℕ) original-PowerSeries.coeff _ (PowerSeries.mk _)‖ ≤ _
    rw [PowerSeries.coeff_mk]
    exact earn.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul hc (pow_le_pow_right₀ leL hs) (pow_nonneg hL _) cm) (by positivity))
  have rows (i:ℕ):‖row (F page) D q i‖ ≤ fare:=by
    have l:= window F book page (PowerSeries.X^i) 1 (fun z _=>by
      rw [PowerSeries.coeff_X_pow];split <;> simp)
    simpa only [row,fare,C,mul_one] using l
  rw [WilsonIndependentPublicReportComplex.difference]
  calc
    _  ≤  ∑ i∈Finset.range (q+1),‖(PowerSeries.coeff i original-PowerSeries.coeff i stopped)*
          (row (F page) D q i:ℂ)‖:=norm_sum_le _ _
    _  ≤  ∑ _i∈Finset.range (q+1),E*fare:=by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,Complex.norm_real]
      exact mul_le_mul (price ⟨i,Finset.mem_range.mp hi⟩) (rows _) (norm_nonneg _) (by dsimp [E];positivity)
    _ = _:=by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; dsimp [E,fare,L];ring

/-- An actual book chosen before the fields, reused by all named pairs. -/
theorem original (good:G.Simple)(hi:γ<1)
    (paid:WilsonIndependentTwoMomentGrant.Accounts P chart K V e h k j Y branches
      p b u γ extra col late B)(q:ℕ)(hq:q ≤ p)(D:ℕ):
    let C:=S V B.a B.positive j late
    ∃ fee:ℝ,0 ≤ fee ∧ ∃ d:ℕ,∀ (aperture:Requests B.a → ℝ)(_pos:∀ w,0 ≤ aperture w),
    ∃ F:Tent (M V B.a),Notebook C Y G branches col (RegulatorIR.FVAAlt2.Rocket.native _) F p ∧
      (∀ w:Requests B.a,sheet F (Page.opening _ w)=Clocks.flat) ∧ Here F aperture q D fee d:=by
  intro C
  obtain ⟨fee,hfee,d,price⟩:=appointed R W P chart K V e h k j Y branches p b u γ extra col late B
    good paid q hq D
  refine ⟨fee,hfee,d,?_⟩
  intro aperture pos
  obtain ⟨F,book,clock,orbit⟩:=WilsonIndependentPublicRawBook.original
    R W K Y branches V P chart e h k j p b u γ hi extra col late B paid aperture pos
  exact ⟨F,book,clock,price aperture pos F book orbit⟩

end YM.Integration.WilsonIndependentPublicReportedOrbit
