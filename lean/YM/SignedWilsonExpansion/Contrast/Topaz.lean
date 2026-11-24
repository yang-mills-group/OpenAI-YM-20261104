import YM.SignedWilsonExpansion.Museum.Stacks
import YM.SignedWilsonExpansion.Camera.Pad
import YM.SignedWilsonExpansion.Contrast.Sierra
/-! # Joint physical test proof via Paired Mesh. Supports all panels. Unbounded lifts but finite addresses.
    weights BOTH U and 2U via pairing (i.e. alternate reporter, exact dilation grid sampling
    of the same test, cf admission), separate Jacob. Crest.Phys spectral exports.
  -/
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.SignedWilsonExpansion.Carbon.Worksheets
open Function Set Filter Asymptotics Finset MeasureTheory Lattice Wilson RG PhysicalNext.Repeat.Legato Maxwell Maxwell.Free Extraction
open XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Arrival Scale Scale.Jury MS MS.Native MS.Land MS.High MS.Fleet
open Museum Camera FullVolume Belle Belfry Belle.Path Belle.Buffet Cirrus Contrast ProbeB
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{n e:ℕ}{ι σ:Type}{L:Filter ι}{r f:ℝ} {ρ:ι→ ℝ}
local notation "X"=> Points n
local notation "λ'"=> Shake (n:=n)
variable (U:Pad n) (p:Test n)
universe u₀
abbrev bp (x:Shake (n:=n)):λ':= fun i a=> 2*x i a
lemma forecast (x:Shake (n:=n))(t:ℝ): Extraction.tag t (bp x)=(2:ℝ) • Extraction.tag t x:=by
    apply PiLp.ext; intro i; apply PiLp.ext; intro a; change t *(↑((2:ℤ)* x i a):ℝ)=(2:ℝ) * (t *( ↑(x i a):ℝ )); push_cast; ring
abbrev inUse (r:ℝ): Set (Shake (n:=n)):= Extraction.tag r ⁻¹' zone U
def bought (r:ℝ) : Finset (Shake (n:=n)):= if h:(inUse U r).Finite then h.toFinset else ∅
def cents (p:Test n)(r:ℝ)(x:Shake (n:=n)):ℂ:= ∫ y in Extraction.segment r x,p y
lemma appears (s:0<r)(x: λ'): x∈ bought U r ↔ Extraction.tag r x ∈ zone U:=by
    have h:( inUse U r ).Finite := Integration.Cope.finite_mesh U.roi.1 s; rw [bought, dif_pos h]; exact h.mem_toFinset
lemma budget (s:0<r): ∑ x∈ bought U r, ‖cents p r x‖ ≤ ∫ x,‖p x‖:=by
   have int' : Integrable (fun x=>‖p x‖):= ( p.continuous.integrable_of_hasCompactSupport p.hasCompactSupport ).norm
   let g(x):=(Extraction.segment r x).indicator (fun y:Points n=>‖p y‖)
   have he (x:Points n) : ∑ i∈ bought U r,g i x ≤ ‖p x‖:= calc
      _ ≤ ∑ i∈ insert (address r x) (bought U r),g i x:= sum_le_sum_of_subset_of_nonneg (Finset.subset_insert .. ) (fun i _ _=>by unfold g indicator; split <;>first|exact norm_nonneg _|exact le_rfl ) -- syntax?
      _ = _:= by
           rw [sum_eq_single (address r x)]
           · exact indicator_of_mem ( s:=Extraction.segment r (address r x) ) rfl _
           · intro y _ h; exact indicator_of_notMem ( s:=Extraction.segment r y ) ( show x ∉Extraction.segment r y from Ne.symm h ) _
           simp
   have hi(i: λ'): Integrable (g i) := int'.indicator (measurable_segment s i)
   refine (Finset.sum_le_sum fun i hi=> norm_integral_le_integral_norm (μ:=volume.restrict ( Extraction.segment r i )) _).trans (?_) -- fs not inferred?
   refine Eq.subst (motive:=fun t:ℝ=> t ≤ ∫ y,‖p y‖) (?_) ( integral_mono (integrable_finsetSum _ (fun i _=> hi i)) int' he ); rw [ integral_finsetSum _ (fun i _=> hi i)]; exact Finset.sum_congr rfl fun i _=> integral_indicator ( measurable_segment s i )
abbrev posted (r:ℝ)(m:Shake (n:=n)→ℂ):= ∑ x∈ bought U r, cents p r x * m x
variable (T: Tendsto ρ L (𝓝 0))(t:∀ᶠ i in L,0<ρ i)(h: tsupport p⊆ interior U.F)
local notation "S"=> tsupport ( p : Points n→ℂ )
def harvest (r:ℝ) : Prop:= ∀ x:X, x∈ tsupport p→ Extraction.tag r (Extraction.address r x)∈ zone U
include h t T
lemma likely : ∀ᶠ i in L, harvest U p (ρ i):=by
   obtain ⟨u,v,hV⟩:= p.hasCompactSupport.exists_cthickening_subset_open isOpen_interior h
   have he:= T.const_mul (4*n:ℝ); rw[mul_zero] at he; filter_upwards [ t,he.eventually_le_const v ] with i hi hv x hx; exact interior_subset ( hV ( Metric.closedBall_subset_cthickening hx _ ( ( approximate hi x ).trans hv ) ) )
omit h t T in
lemma feed (vp:harvest U p r) (s:0<r) (u:λ'→ℂ) : p.applyTo (u ∘ address r)=posted U p r u ∧ Integrable (fun x:X=> p x*u (address r x)):=by
    let g(x):=( Extraction.segment r x ).indicator (fun y:X=> p y*u x); have hp : (fun x:X=> p x*u (address r x))=( fun x=>∑ y∈ bought U r,g y x ) :=by
         ext1 x; by_cases ht:x∈ tsupport p
         · rw [sum_eq_single_of_mem ( Extraction.address r x ) ( ( appears U s _ ).mpr ( vp x ht ) ) ]
           · exact ( indicator_of_mem (s:=Extraction.segment r ( address r x ))  ( show x∈Extraction.segment r (address r x) from rfl ) (fun y:X=> p y*u (address r x)) ).symm
           intro i _ hv; exact indicator_of_notMem ( show x ∉ Extraction.segment r i from Ne.symm hv ) _
         have he(x': λ'): g x' x=0:= by unfold g; rw [Set.indicator_apply,image_eq_zero_of_notMem_tsupport ht,zero_mul ]; split_ifs <;>rfl
         simp only [he,image_eq_zero_of_notMem_tsupport ht,zero_mul,sum_const_zero]; -- inspect
    have hn (i:λ') : Integrable (g i):=(( p.continuous.integrable_of_hasCompactSupport p.hasCompactSupport ).mul_const _).indicator (measurable_segment s i)
    unfold Test.applyTo; simp_rw [Function.comp_apply]; rw [hp, integral_finsetSum _ (fun i _=> hn i)]; exact ⟨Finset.sum_congr rfl fun i _=> ( ( integral_indicator (μ:=volume) ( measurable_segment s i ) ).trans ( integral_mul_const .. ) ), integrable_finsetSum _ (fun i _=> hn i) ⟩ -- named correction
lemma minted (u:X→ℂ) (hv:ContinuousOn u (conf n)): Tendsto (fun i=> posted U p (ρ i) (u ∘ Extraction.tag (ρ i))) L (𝓝 (p.applyTo u)):=by
    refine ( billing (L:=L) p (A:=fun i:ι=>(u∘ Extraction.tag (ρ i)) ∘ address (ρ i)) (?_) ( ( t.and (likely U p T t h) ).mono fun i hi=> ( feed U p hi.2 hi.1 _ ).2 ) ( p.smearing hv ) ).congr' ( ( t.and (likely U p T t h) ).mono fun i hi=> ( feed U p hi.2 hi.1 _ ).1 )
    refine Museum.continuouslyTested p.hasCompactSupport u _ ( hv.mono p.tsupport_subset ) (?_); intro F hl x hx r hr; let v(i):= Extraction.tag (ρ i) ( address (ρ i) (r i) ); have H:= tendsto_nhdsWithin_iff.mp hr; have hn : Tendsto v (F:Filter ι) (𝓝 x) := by
         refine Metric.tendsto_nhds.mpr (fun ε u=>?_); have HP:=( T.const_mul (4*n:ℝ)); rw [mul_zero] at HP; filter_upwards [( Metric.tendsto_nhds.mp H.1 (ε/2) (half_pos u)), Eventually.filter_mono hl ( HP.eventually_lt_const (half_pos u) ), Eventually.filter_mono hl t] with i hi t w; exact lt_of_le_of_lt ( dist_triangle (v i) ( r i ) _ ) (( add_lt_add ( lt_of_le_of_lt ( approximate w ( r i ) ) t ) hi )|>.trans_eq (add_halves _) )
    exact ( hv x ( p.tsupport_subset hx ) |>.continuousAt ( ( conf_open n ).mem_nhds ( p.tsupport_subset hx ) ) |>.tendsto.comp hn )
omit h T
variable {μ:ι→ℝ} {Q:Shake (n:=n)→ι→ℂ}(Y:∀ ε:ℝ,0<ε→∀ᶠ i in L,∀ x:λ', Extraction.tag (ρ i) x∈ zone U → ‖Q x i‖ ≤ ε* ‖μ i‖ )
lemma rupees (Y:∀ ε:ℝ,0<ε→∀ᶠ i in L,∀ x: λ',Extraction.tag (ρ i) x∈ zone U→ ‖Q x i‖ ≤ ε * ‖μ i‖ ) : (fun i=> posted U p (ρ i) (fun x=> Q x i))=o[L] μ:=by
    let c:ℝ:=∫ x, ‖p x‖; have hm:0≤c:= integral_nonneg fun i=> norm_nonneg _; apply IsLittleO.of_bound; intro ε e; let y:=ε/(1+c); have he:0<y:=div_pos e (by linarith); filter_upwards [ t,Y y he ] with i hi hc; unfold posted; refine le_trans (norm_sum_le _ _) (?_)
    simp_rw [norm_mul]; refine le_trans (b:=∑ x∈ bought U (ρ i), ‖cents p ( ρ i ) x‖ * ( y * ‖μ i‖ )) ( sum_le_sum fun x hx=> mul_le_mul_of_nonneg_left ( hc x ( ( appears U hi _ ).mp hx ) ) (norm_nonneg _) ) (?_); rw [←sum_mul]; refine le_trans (mul_le_mul_of_nonneg_right (( budget U p hi ).trans ( show c≤1+c by linarith )) (mul_nonneg he.le ( norm_nonneg _ ) )) ( Eq.le (?_) ); rw [ ←mul_assoc ]; unfold y; field_simp
variable {F:Schedule}{Z:Pad 3} (φ:Test 3) (V:Pad 3) (K:tsupport φ ⊆ interior V.F) 
open FVA2.Register PowerSeries
abbrev tasted (Q:Pad 3) (p:Test 3)(r:ℝ)(m:Shake (n:=3)→ℂ) := posted Q p r fun x=>m (bp x)
def dialed (u:Shake (n:=3)→ℂ)(r:ℝ)(x:Points 3):ℂ:= u ( bp ( Extraction.address r ((2:ℝ)⁻¹ • x) ) )
omit t in
lemma dials (s:0<r)(v:harvest V φ r) (u:Shake (n:=3)→ ℂ): ( ProbeB.double φ ).applyTo ( dialed u r )=tasted V φ r u:=by
    rw [ ProbeB.expands ]; simp_rw [dialed, inv_smul_smul₀ (show (2:ℝ)≠0 from by norm_num) ]; exact ( feed V φ v s (u ∘ bp) ).1
include K t T
variable {D:Shake (n:=3)→ι→ℂ} {D':Shake (n:=3)→ι→ℂ} (N: WilsonPrescription G){q: Bool}{Y':MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S₀:Prescription (Press.portDeck G)}{h0:G.Simple}(H: Main.Match N h0 Y' S₀ q)(ν:ℝ)
local notation "B*"=> Carbon.four N
local notation "c"=> (2:ℂ)^12
local notation "R2"=> ProbeB.receipt ( Carbon.four N ) 2
abbrev feesQ (φ:Test 3) (V:Pad 3)(r:ℝ)(x:Shake (n:=3)→ℂ) := posted V φ r x - c*tasted V φ r x
include H ν in
lemma launches (Q:Shake (n:=3)→ι→ℂ) (W:∀ ε:ℝ,0<ε→∀ᶠ i in L,∀ x:Shake (n:=3), Extraction.tag (ρ i) x∈ zone V → ‖( Q x i - c*Q (bp x) i )- R2 (Extraction.tag (ρ i) x) * ( μ i :ℂ )^2‖ ≤ ε*‖μ i ^2‖ ) : (fun i=> feesQ φ V (ρ i) (fun x=> Q x i)-ProbeB.quote B* φ 2 * (μ i:ℂ)^2 )=o[L](μ^2):=by
    let Ω:=Measure.start N.scheme N.criterion 4; let u:= H.details.toServed.toPosted.toQuoted.toContract.toMission.born; have hP:= ProbeB.receipt_health Y' N.scheme N.criterion S₀ h0 u.Taylor u.still u.base ν 2; let Z(i):= posted V φ (ρ i) (R2 ∘ Extraction.tag (ρ i)); have he: ProbeB.quote B* φ 2= φ.applyTo R2:= ProbeB.quoted Y' N.scheme N.criterion S₀ h0 u.Taylor u.still u.base φ ν _
    have hh:(fun i=> Z i-ProbeB.quote B* φ 2 )=o[L](1:ι→ℝ):=by rw [he]; apply (isLittleO_one_iff ℝ).mpr; convert ( minted V φ T t K R2 hP ).sub_const (φ.applyTo R2 ) using 1; rw [sub_self]
    have hm:= ( Wipe.earth_p ( isBigO_refl (μ^2) L ) ) -- edit call
    have hh' := (hh.mul_isBigO hm).congr_right (fun i=> one_mul ( μ i ^2 )); refine (( rupees V φ t W ).add hh').congr_left fun i=>?_ -- add
    unfold Z feesQ tasted posted; simp_rw [ mul_sub, sub_mul, Finset.mul_sum, sum_mul, Function.comp_apply, Finset.sum_sub_distrib,← mul_assoc, Pi.pow_apply, Complex.ofReal_pow ]; simp_rw [ mul_comm c ( cents φ _ _ ) ]; abel
end YM.SignedWilsonExpansion.Carbon.Worksheets
