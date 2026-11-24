import YM.MS.Vista.Folk
/-!
# Bill scalar. Uniform ℝ heat length-n tail bound using touched-off cutoff; clamp length even in sharper polylog method. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo Orbit.LogReal
open scoped Topology ContDiff Interval
variable {I W E:Type}{G:Gauge}{ L:I→Side}{b:Bool}{V: Visa I}{F H:Glade G I}{K:Belt I}
local notation "Ρ"=>After V L
local notation "Φ"=>unbounded V
local notation "Σ_"=>Mid V L
abbrev Dwind (L:I→Side)(i:I):= (tickA L i)^(-eps_gain)
lemma δ_end (p:(Ρ).time): Beef Ρ p= Dwind L p.1:= by unfold Dwind Beef goodM; rw [afterR]
lemma boost (p: (Ρ).time) : lamp (tstart p) ≥ (tickA L p.1)*exp ( tstart p-until0 L p.1 ):= by
    let r:=until0 L p.1; have hh:= afterT p; rw [ exp_sub]; apply le_trans _ (le_max_right 1 (τ (tstart p))); rw [← mul_div_assoc,div_le_iff₀ (exp_pos _)]; have hx:= exp_monotone hh; have ht:= τ_h L p.1; unfold τ at *; rw [ ← ht ]; nlinarith
lemma νR (p:(Ρ).time): 0≤tstart p:= le_trans ( φ_day L p.1 ) ( afterT p )
abbrev entrance (p:(Ρ).time): (Φ).time:=⟨ p.1,tstart p,show 0≤ tstart p from νR p⟩
lemma price_tag (p:(Ρ).time): ( Beef Φ ) ( entrance p ) ≤ ( Beef Ρ ) p * Tail V L p:= by
   obtain he:= boost p; unfold Beef goodM Tail; change _ ^ (-eps_gain) ≤ ( tickA L p.1 )^(-eps_gain)* _; have hz:= δ_p L p.1;
   apply le_trans (Real.rpow_le_rpow_of_nonpos ( by positivity : 0<(tickA L p.1) * exp ( tstart p - until0 L p.1 )) he ( neg_nonpos.mpr p_gain.le )); rw [Real.mul_rpow hz.le ( exp_pos _ |>.le ), ← Real.exp_mul, mul_comm ( tstart p-until0 L p.1 )]; -- argument `boost` yes.
lemma lunar (H:HandC false false Φ F (Beef Φ)): paid (Ρ).price (fun p=>‖Vane.scalar (bend G I F) p‖) ( Tail V L * Beef Ρ ):= by
    obtain ⟨C,hC,k,hK⟩:= Vane.scalar_bill H; refine ⟨ C,hC,k,fun i=>(hK (entrance i)).trans ?_⟩; rw [mul_comm (Tail V L)]; exact mul_le_mul_of_nonneg_left ( price_tag i ) (by have hv:0 < (Φ).price.basic (entrance i) := (Φ).price.basic_pos _; positivity)
-- ∫ isotopy cutoff `(exp−eps(δ))`: tail cost.On.clock outputs at threshold.
abbrev Barrier (V:Visa I)(L:I→Side)(i:I):= castdown ( M:=V ) ( P:=After V L ) soonM i
abbrev bill_out (V:Visa I)(L:I→Side)(k:ℕ)(i:I):= wallet V i (until0 L i)^k * Dwind L i
abbrev cash_out (V:Visa I)(L:I→Side)(f:I→ℂ):= paid ( Boot ( P:=After V L ) soonM ) (fun i=> ‖f i‖) (Dwind L) -- V implicit confusion
lemma toboot (p:I): ( Boot (M:=V) (P:=After V L) soonM ).basic p=wallet V p (until0 L p):= rfl
lemma w_size (p:(Ρ).time): ( Ρ ).price.basic p=V.bank p.1*(1+tstart p):= by rw [soonM.fund]; unfold wallet; rw [abs_of_nonneg ( νR p ) ] -- V & L.K
lemma climb_f (p:(Ρ).time): (Ρ).price.basic p≤ wallet V p.1 (until0 L p.1) * (1+ (tstart p-until0 L p.1)):= by rw [w_size]; unfold wallet; rw [ abs_of_nonneg ( φ_day L p.1 ), mul_assoc]; apply mul_le_mul_of_nonneg_left _ ( zero_le_one.trans ( V.here p.1 ) ); nlinarith [ φ_day L p.1,afterT p]
-- stock ζ four integrate.V_end.
abbrev flurries (x y:ℝ):= exp (-(eps_gain/2)*(y-x))
lemma flurry (x:ℝ): IntegrableOn (flurries x) (Set.Ioi x) ∧ ∫ y in Set.Ioi x,flurries x y=4:= by
   rw [show flurries x=fun v:ℝ=> exp ((eps_gain/2)*x) * exp (-(eps_gain/2)*v) from funext (fun i=>by unfold flurries; rw [← exp_add]; congr 1; ring)]; constructor; · exact (integrableOn_exp_mul_Ioi (a:=-(eps_gain/2)) (by norm_num [eps_gain]) x).const_mul _
   rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num [eps_gain]),neg_mul, exp_neg ]; field_simp; ring
-- degree/storage. Beam.
abbrev EndN (F:Glade G I)(L:I→Side)(i:I):ℂ:= F i (tstart ( Barrier V L i )) [] -- F after warp parameter t
lemma Δ_paid (ht:LookS F H)(hp: paid (Ρ).price (fun p=>‖Vane.scalar H p‖) (Tail V L*Beef Ρ)): (∀ i,Vane.Allow F i) ∧ ( cash_out V L ( Vane.blade F-EndN (V:=V) F L ) ):= by
    obtain ⟨C,hC,k,hK⟩:=hp; obtain ⟨D,hD,hX⟩:=Belt.capped p_gain k; let c:=C*D; have he(i:I): IntegrableOn (fun t=> H i t []) ( Set.Ioi (until0 L i) ) ∧ ‖∫ t in Set.Ioi (until0 L i),H i t []‖ ≤ 4*c*bill_out V L k i:= by
        let z:=until0 L i; let N:=wallet V i z; let g(x):= c*N^k*Dwind L i*flurries z x; let f(t):= H i t []; obtain ht:= ( ( ht.der i ).at_const id [] contDiff_id ).continuous; have hx:IntegrableOn g ( Set.Ioi z ):= ( flurry z |>.1 ).const_mul _; have hv : 0<N:= ( Boot ( P:=Ρ ) ( M:=V ) soonM ).basic_pos i
        have hV := Real.rpow_pos_of_pos (δ_p L i) ( -eps_gain ); let μ:=volume.restrict ( Ioi z ); have H : ∀ᵐ t ∂μ,‖f t‖ ≤ g t:= by
           filter_upwards [( ae_restrict_mem measurableSet_Ioi )] with p hp; let j:(Ρ).time:= ⟨i,p,show until0 L i ≤ p from hp.out.le ⟩; have hQ:=hK j; apply hQ.trans; rw [ Pi.mul_apply, δ_end ]; obtain hu := climb_f j; have hG := (Ρ).price.basic_pos j; change C*_*( exp (-eps_gain*(p-z))*Dwind L i ) ≤ _; calc
              _ ≤ C*( N*(1+(p-z)) )^k*( exp (-eps_gain*(p-z))*Dwind L i ):= by gcongr -- hu length.W
              _ = C*N^k*Dwind L i * ((1+(p-z))^k*exp (-eps_gain*(p-z))):= by rw [mul_pow]; ring
              _ ≤ _:= (mul_le_mul_of_nonneg_left (hX _ (sub_nonneg.mpr (show z ≤ p from hp.out.le))) (by unfold Dwind; positivity : 0≤ C*N^k*Dwind L i))|>.trans_eq (by unfold g c flurries; ring)
        have hW: Integrable f μ:= hx.mono' ( ht.aestronglyMeasurable ) H; exact ⟨ hW,( norm_integral_le_of_norm_le hx H ).trans_eq (by unfold g N z; rw [integral_const_mul, flurry _ |>.2 ]; unfold bill_out; ring) ⟩ 
    have H (i:I): Vane.Allow F i:= tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (fun x _=>ht.modal.pace i x []) ( he i |>.1 ); refine ⟨ H,4*c, by unfold c; positivity,k,fun i=>?_⟩; obtain hp:=integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _=> ht.modal.pace i x [] ) (he i |>.1 ) ( H i ); rw [toboot]; rw [ mul_assoc (4*c) ]; change ‖Vane.blade F i-F i ( until0 L i ) []‖≤ _; rw [← hp]; exact he i|>.2
end YM.MS.Vista
