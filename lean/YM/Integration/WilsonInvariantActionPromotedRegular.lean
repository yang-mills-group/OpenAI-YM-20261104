import YM.Integration.WilsonInvariantActionPromotedPair
import YM.Integration.WilsonInvariantActionPromotedQuota
import YM.Integration.WilsonFundedActionPairSector
import YM.Integration.WilsonRegisteredBilateralRange

/-! The two registered regular marks on the actual signed separated test.
Both finite conditional vacuum subtractions use the full original rows. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonInvariantActionPromotedRegular
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Marker Extraction Extraction.Order
open Maxwell.Free Climb Table Spec PhysMS OPE OPE.Therm RG17 Next.Rank.Price Next.UVStress
open PhysicalNext.Repeat.Legato Trace.Pilot SharpGram.Lenses WilsonLimitConstruction Pert.Asymptotics
open WilsonInheritedRegisteredField WilsonRegisteredAngularPair WilsonRegisteredShortField
open private volume_bill from YM.Integration.WilsonInvariantActionPromotedPair
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple) {ρ:ℝ} {T:Campaign R} {P:Campaign.Pillars R T}
    (funded:FundedOriginalProperties.{u} simple ρ P) {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (L:Layout F)
local notation "β" => R.family.path.levels.clock.hatBeta
variable {N per j : ℕ}

def difference (live : j<N) (v w:R.family.label 4) (x:Fin 2→Site (R.family.side (j+1) per)) (b:ℕ)
    (η χ:ℂ→L[ℝ]ℝ) (V:Config G (R.family.side j per)) (U:Config G (R.family.side (j+1) per)) : ℝ :=
  let f:=fun X=>η (regular R.makes live v (x 0) X)
  let g:=fun X=>χ (regular R.makes live w (x 1) X)
  let A:=center R (N:=N) true f V
  let B:=center R (N:=N) true g V
  (f U-A)*(g U-B)-(η (short R.makes live v (x 0) b U)-A)*(χ (short R.makes live w (x 1) b U)-B)

def response (live : j<N) (v w:R.family.label 4) (b:ℕ) (η χ:ℂ→L[ℝ]ℝ) (φ:Test 2) : ℂ :=
  ∑ x:Fin 2→Site (R.family.side N per),WilsonExternalMeshMass.charge R.family φ x *
    (↑(∫V,actualAverage R.family (N:=N) (fun U=>
      difference R live v w (fun y=>(R.family.S.toDepth live per).parent (x y)) b η χ V U) V
        ∂scene R.family.path N per j):ℂ)

include simple in
private theorem coupling_bound {m k N p:ℕ} (order:m ≤ k) (hk:k ≤ N) {g:ℝ}
    (gp:0<g) (temp:1/2<β m*g^2) : regulatorRun R.family N p k ≤ 2*g := by
  let b:=R.family.path.β N p k
  let t:=regulatorRun R.family N p k
  have bp : 0<b := Overlay.beta_positive R.makes.wilson hk
  have hp : 0<β m := zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have tp : 0 ≤ t := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have cash : t^2*b=1 := by
    dsimp [t,regulatorRun,b];rw [inv_pow,Real.sq_sqrt bp.le,inv_mul_cancel₀ bp.ne']
  have mono : β m ≤ β k := WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos simple).le order
  have cap : β m/2 ≤ b := (by linarith only [mono] : β m/2 ≤ β k/2) |>.trans (R.makes.wilson.represents N p k hk).band.1
  have first : t^2 ≤ 2/(β m) := (le_div_iff₀ hp).mpr (by
    nlinarith only [mul_le_mul_of_nonneg_right cap (sq_nonneg t),cash])
  have second : 2/(β m) ≤ (2*g)^2 := (div_le_iff₀ hp).mpr (by nlinarith only [temp])
  change t ≤ 2*g
  nlinarith only [first.trans second,mul_pos gp (show (0:ℝ)<2 by norm_num),tp]

variable (pace:WilsonWindowReportingPace.Slow R.kit) (E:Services R.family f S)
    {B:ℕ} (hB:0<B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    {g:ℝ→ℝ} (coupling:Coupling G g)

include simple funded pace E hB level coupling in
theorem filed (s e q : ℕ) (φ:Test 2) {ε:ℝ} (he:0<ε) :
    ∀ᶠ r in trail,let m:=L.level r; let k:=WilsonInvariantActionPosition.berth R s m
      let e':=(s+2)*5+e
      ∀ (hr:0<r) (j:ℕ),j+1=k → R.family.ref 4 ≤ m →
      ∀ (a w:R.family.label 4) (Ma Mw:ℝ),0 ≤ Ma → 0 ≤ Mw →
      (∀N p,m ≤ N→quota R.family 4 m N p (atRef L 4 r (N,p) a) ≤ R.family.S.a m^4*(β m^e*Ma)) →
      (∀N p,m ≤ N→quota R.family 4 m N p (atRef L 4 r (N,p) w) ≤ R.family.S.a m^4*(β m^e*Mw)) →
      ∀ᶠ z:ℕ×ℕ in L.lens,∀ live:j<z.1,∀ η χ:ℂ→L[ℝ]ℝ,
      ‖response R (per:=z.2) live (atRef L 4 r z a) (atRef L 4 r z w)
          (WilsonDegreeFourInheritedRange.height R (q+2*(e'+1)+2*e') k) η χ (dilate hr φ)‖
        ≤ ε*(g r)^q*(‖η‖*‖χ‖)*(Ma*Mw) := by
  let M:ℝ:=(∫x,‖φ x‖)+1
  let e':=(s+2)*5+e
  have hm : 0<M := by dsimp [M]; positivity
  let fee:=ε/(M*(2:ℝ)^q)
  have hf : 0<fee := div_pos he (mul_pos hm (pow_pos (by norm_num) _))
  obtain ⟨j₀,after⟩ := eventually_atTop.mp (WilsonRegisteredBilateralRange.original R simple funded e' q hf)
  have grows : Tendsto L.level trail atTop := by rw [level]; exact WilsonMeasuredWindow.stop_tendsto _ simple B hB
  have market:=grows.eventually (WilsonInvariantActionPromotedQuota.price R simple pace F L E s 4 e)
  have temperature := (WilsonPhysicalCutoffCurrency.temperature R simple pace hB g coupling).eventually
    (lt_mem_nhds (show (1/2:ℝ)<1 by norm_num))
  filter_upwards [grows.eventually_ge_atTop j₀,market,temperature,coupling.positive] with r age buy hot gp
  dsimp only
  let m:=L.level r
  let k:=WilsonInvariantActionPosition.berth R s m
  have mk : m<k := (WilsonInvariantActionPosition.arrival R s m).1
  have warm : 1/2<β m*(g r)^2 := by simpa only [m,level] using hot
  intro hr j date ref a w Ma Mw ha hw pa pw
  have mj : m ≤ j := Nat.le_of_lt_succ (by change m<j+1;rw [date];exact mk)
  have jage : j₀ ≤ j := age.trans mj
  have kr : R.family.ref 4 ≤ j+1 := date ▸ ref.trans mk.le
  let T:=dilate hr φ
  have cart:=(WilsonExternalMeshMass.funded R.family f T T.continuous T.hasCompactSupport
    (show (0:ℝ)<1 by norm_num)).filter_mono L.certified
  filter_upwards [cart] with z kit
  intro live η χ
  have stop : k ≤ z.1 := by change WilsonInvariantActionPosition.berth R s (L.level r) ≤ z.1; rw [←date]; exact live
  let a':=atRef L 4 r z a
  let w':=atRef L 4 r z w
  have ca:quota R.family 4 (j+1) z.1 z.2 a' ≤ R.family.S.a (j+1)^4*(β (j+1)^e'*Ma) := by
    rw [date];exact buy rfl ha a ref pa z.1 z.2 stop
  have cw:quota R.family 4 (j+1) z.1 z.2 w' ≤ R.family.S.a (j+1)^4*(β (j+1)^e'*Mw) := by
    rw [date];exact buy rfl hw w ref pw z.1 z.2 stop
  let b:=WilsonDegreeFourInheritedRange.height R (q+2*(e'+1)+2*e') k
  let K:=fee*(2*g r)^q*(‖η‖*‖χ‖)*(Ma*Mw)
  have κ : 0 ≤ K := by dsimp [K];positivity
  have unit : regulatorRun R.family z.1 z.2 k ≤ 2*g r := coupling_bound R simple mk.le stop gp warm
  have raw:=after j jage z.1 z.2 live 4 4 kr kr a' w'
  have point (o:Fin 2→Site (R.family.side (j+1) z.2)) (V:Config G (R.family.side j z.2))
      (U:Config G (R.family.side (j+1) z.2)) : ‖difference R live a' w' o b η χ V U‖ ≤ K := by
    have lo:=raw o Ma Mw ha hw ca cw η χ true true V U
    change |difference R live a' w' o (WilsonDegreeFourInheritedRange.height R (q+2*(e'+1)+2*e') (j+1)) η χ V U| ≤ _ at lo
    rw [date] at lo
    rw [Real.norm_eq_abs]
    refine lo.trans ?_
    dsimp [K]
    gcongr
    · exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  let law:=scene R.family.path z.1 z.2 j
  haveI : IsProbabilityMeasure law := probability R.makes.wilson live.le
  let H:=fun x:Fin 2→Site (R.family.side z.1 z.2)=>∫V,actualAverage R.family (N:=z.1)
    (fun U=>difference R live a' w' (fun t=>(R.family.S.toDepth live z.2).parent (x t)) b η χ V U) V ∂law
  have bound (x:Fin 2→Site (R.family.side z.1 z.2)) : ‖H x‖ ≤ K := by
    have each (V:Config G (R.family.side j z.2)) := actualAverage_norm_le R.family R.makes live
      (point (fun t=>(R.family.S.toDepth live z.2).parent (x t)) V) V
    simpa only [H,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=law) (ae_of_all _ each)
  let c:=fun x:Fin 2→Site (R.family.side z.1 z.2)=>WilsonExternalMeshMass.charge R.family T x
  have total:∑x,‖c x‖ ≤ M := by simpa only [c,T,volume_bill φ hr,M] using kit
  change ‖∑ x,c x*(↑(H x):ℂ)‖ ≤ _
  calc
    ‖∑ x,c x*(↑(H x):ℂ)‖ ≤ ∑x,‖c x*(↑(H x):ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑x,‖c x‖*K := by
      apply sum_le_sum;intro x _;rw [norm_mul,Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (bound x) (norm_nonneg _)
    _ = (∑x,‖c x‖)*K := (sum_mul ..).symm
    _ ≤ M*K := mul_le_mul_of_nonneg_right total κ
    _ = ε*(g r)^q*(‖η‖*‖χ‖)*(Ma*Mw) := by
      dsimp only [K,fee]; rw [mul_pow]; field_simp

end YM.Integration.WilsonInvariantActionPromotedRegular
