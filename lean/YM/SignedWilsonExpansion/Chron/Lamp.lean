import YM.SignedWilsonExpansion.Chron.Inter
/-!
# Joint exterior with previous field §II-b. Retained full support hit log Taylor
 restore, on `tall` tilted ψI. watch ratio VS ψI. In addition to the Impulse option
 conditioning only on exterior. All paid hits (no tail deletion).
-/
set_option autoImplicit false
set_option maxHeartbeats 840000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.Logwood.Vintage
open Set Function MeasureTheory Lattice RG Wilson OPE.Therm FVA1Physical.Exchange FVA1Physical.Exchange.F6Regular FVA1Physical.Marked.Inherited
open private unit_thermal centered_linear from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6FirstThermal
open private general_measured from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6MeasuredExterior
open private scalar_ratio from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6PolynomialLaw
open private subenv from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6RegularCovariance
open FVA1Physical.Exchange.RoseCut
open private fibre_prob from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionNormalizedConnected
open scoped ENNReal Topology ContDiff Classical BigOperators
section
variable {E I X:Type*}[MeasurableSpace E][MeasurableSpace X][MeasurableSpace I][Norm E]{F:X×I→E}
lemma beamA (h:Envelope F)(x:X):Envelope (fun w=>F (x,w)):= stocked h (measurable_const.prodMk measurable_id)
end
variable {G:Gauge}{H:History G}{j N p:ℕ}
variable (pH:H.Selected) (J:Finset (Edge (Site (H.S.side (j+1) p)))) (hj:j<N)
local notation "X" => XU H j p J
local notation "κ" => (ψI J N)
local notation "I" => ↥J→G.El
local notation "ρ" => patch_haar J
local notation "R" => ( H.rep N p (j+1) )
def dollar (N:ℕ)(x:X×(↥J→G.El)):ℝ:= referenceTilt (H.rep N p (j+1)) (plumeL J (x.1,1)) (plumeL J x)
abbrev τL (N:ℕ):ℝ:= ticketA J (H.rep N p (j+1)).p (H.levels.clock.allowance (j+1))
def tallL (N:ℕ)(x:X):Measure (↥J→G.El):= fibreLaw ( ψI J N x ) (fun w=>Real.exp ( dollar J N (x,w) ))
def mintW (N k:ℕ)(x:X×(↥J→G.El)):ℝ:=Real.exp (dollar J N x)*tiltTaylor k (-dollar J N x)
def levy (N k:ℕ)(x:X):= ∫w,mintW J N k (x,w) ∂  (ψI J N x) 
def watch (N k:ℕ)(F:X×(↥J→G.El)→ℝ)(x:X):ℝ:= ( ∫w,mintW J N k (x,w)* F (x,w)∂  (ψI J N x)  )/(levy J N k x)
def birth (N:ℕ)(F:X×(↥J→G.El)→ℝ)(x:X):ℝ:= ∫w,F (x,w)∂  (ψI J N x) 
def plainL (N:ℕ)(F:X×(↥J→G.El)→ℝ)(x:X):ℝ:=∫w,F (x,w) ∂ tallL J N x
/-- quiet relative to tallL -/
def levy1 (N:ℕ)(x:X):= ∫w,1-dollar J N (x,w)∂(tallL J N x)
def sealL (N:ℕ)(F:X×(↥J→G.El)→ℝ)(x:X):ℝ:=firstRead (tallL J N x) (fun w=>F (x,w)) (fun w=>dollar J N (x,w))
include pH hj
lemma weighed : Envelope (dollar J N):=by
   have g := ( pH.represents N p _ hj ).good; let u:Envelope ((H.rep N p (j+1)).activities.additive (H.rep N p (j+1)).p) := ⟨ (H.rep N p (j+1)).activities.E_measurable g.labels.regular,( Activities.ESeries g.labels ).bound ⟩; exact subenv ( stocked u (cloud_meas J) ) ( stocked u ( (cloud_meas J).comp (measurable_fst.prodMk measurable_const) ) )
lemma cashout (x:X): IsProbabilityMeasure (tallL J N x):= by letI:=minted pH J hj x; let u:= ( beamA ( weighed pH J hj ) x ).exp; exact fibre_prob ( (ψI J N x) ) (u.integrable _ ) (fun _=>(Real.exp_pos _).le) (earnsPositive u (fun w=>Real.exp_pos _) _ )
lemma born (F:X×(↥J→G.El)→ℝ)(pF:Envelope F): Envelope (birth J N F):=by
   let Gx (x:X):=∫w,color J N (x,w)*F (x,w) ∂ρ; have hs: Envelope Gx:=passInt (( color_env pH J hj ).mul pF) ρ
   constructor
   · rw [show birth J N F=fun x=>Gx x/sale J N x from funext (fun i=>general_measured ρ ( beamA ( color_env pH J hj ) i ).meas (fun w=>(color_pos pH J hj _ w).le) _ ) ]; exact hs.meas.div ( sale_env pH J hj ).meas
   refine ⟨pF.cost.choose, fun i=>?_⟩; letI:=minted pH J hj i; simpa only [birth,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const ( μ:= κ i ) ( Filter.Eventually.of_forall (fun w=>pF.cost.choose_spec (i,w)) )
lemma plated (x:X×(↥J→G.El))(τ:1≤ (H.rep N p (j+1)).p.supportExponent) : |dollar J N x|≤ τL J N:=by
    apply RoseCut.FiledAction.funded_edit (H.rep N p (j+1)).p τ ( pH.represents N p _ hj ).good.labels ( plumeL J x ) ( plumeL J (x.1,1) )
    intro e he; have u:e∉J:=fun t=> he (Finset.mem_image.mpr ⟨e,t,rfl⟩); simp only [plumeL,fillPatch,dif_neg u]
lemma mintedPositive (k:ℕ)(x:X×(↥J→G.El))(τ:1≤ (H.rep N p (j+1)).p.supportExponent)(ε:τL J N≤1/4): 0 < mintW J N k x := (scalar_ratio k _ _ ε ( plated pH J hj x τ ) ).1
lemma tabulated (k:ℕ)(F:X×(↥J→G.El)→ℝ)(x:X)(pF:Envelope F)(M:ℝ)(fee:∀ u,|F u|≤ M)(τ:1≤ (H.rep N p (j+1)).p.supportExponent)(ε: τL J N ≤ 1/4):
    0<levy J N k x ∧ |watch J N k F x-birth J N F x|≤8*M*τL J N^(k+1):=by
    letI:= minted pH J hj x; have e(w): |dollar J N (x,w)|≤ τL J N:= plated pH J hj (x,w) τ
    exact scalar_thermal_quotient ( (ψI J N x) ) (fun w=> dollar J N (x,w)) (fun w=>F (x,w)) (beamA ( weighed pH J hj ) x) (beamA pF x) M _ ( (abs_nonneg _ ).trans ( e 1 ) ) ε e (fun w=> fee _) k
theorem transferred (k:ℕ)(F:X×(↥J→G.El)→ℝ)(x:X):
    watch J N k F x=( ∫w,tiltTaylor k (- dollar J N (x,w)) * F (x,w) ∂ tallL J N x ) / ( ∫w,tiltTaylor k (- dollar J N (x,w)) ∂ tallL J N x ) :=by
   let t:= (ψI J N x) ; letI:= minted pH J hj x; let W(w):=Real.exp (dollar J N (x,w)); let u:= ( beamA ( weighed pH J hj ) x ).exp; let F1(w):=tiltTaylor k (- dollar J N (x,w))
   have g (φ:(↥J→G.El)→ℝ): (∫w,φ w∂tallL J N x)=(∫w,W w*φ w∂t)/(∫w,W w ∂t):= general_measured t u.meas (fun _=>(Real.exp_pos _).le) _
   have hp:0<∫w,W w∂t:=earnsPositive u (fun _=>Real.exp_pos _) ( (ψI J N x) )
   rw [ g,g,div_div_div_cancel_right₀ hp.ne' ]; change ( ∫w,W w* F1 w* F (x,w) ∂t ) / (∫w,W w* F1 w ∂ t) = ( ∫w,W w* (F1 w * F (x,w)) ∂ t ) /( ∫ w,W w * F1 w ∂ t ); simp_rw [mul_assoc]
lemma initial (F:X×(↥J→G.El)→ℝ)(x:X)(pF:Envelope F)(M:ℝ)(fee:∀ u,|F u|≤ M)(τ:1≤ (H.rep N p (j+1)).p.supportExponent)(ε: τL J N ≤ 1/4):
    let y:= plainL J N F x; let v:=sealL J N F x
    3/4≤ levy1 J N x ∧ watch J N 1 F x=y-v/levy1 J N x ∧ |birth J N F x-(y-v)| ≤12*M*τL J N^2:=by
   intro y v; have h:= tabulated pH J hj 1 F x pF M fee τ ε; letI:= cashout pH J hj x
   let t:=tallL J N x; let Z':=(∫w,(1-dollar J N (x,w))*F (x,w)∂t) / levy1 J N x; have he:watch J N 1 F x=Z':= by rw [ transferred pH J hj 1 F x ]; simp_rw [ unit_thermal ]; rfl
   have hz:3/4≤levy1 J N x ∧ Z'=y-v/levy1 J N x ∧ |Z'-(y-v)|≤4*M*τL J N^2:=centered_linear t (fun w=>F (x,w)) (fun w=>dollar J N (x,w)) (beamA pF x) (beamA ( weighed pH J hj ) x) M _ (fun i=>fee _) (fun w=>plated pH J hj (x,w) τ) ε
   rw [ ← he ] at hz; exact ⟨hz.1,hz.2.1, (abs_sub_le _ (watch J N 1 F x) _ ).trans ( ( add_le_add ((abs_sub_comm ..).trans_le h.2 ) hz.2.2 ).trans_eq (by ring) )⟩
lemma honored (k:ℕ)(τ:1≤ (H.rep N p (j+1)).p.supportExponent)(ε: τL J N ≤ 1/4): Envelope ( mintW J N k ):=by
    let eu:=τL J N; constructor
    · unfold mintW; exact (weighed pH J hj).exp.meas.mul ((show Continuous (tiltTaylor k) by unfold tiltTaylor; fun_prop).measurable.comp (weighed pH J hj).neg.meas)
    refine ⟨1+2*eu^(k+1), fun x=>?_⟩; rw [Real.norm_of_nonneg ( mintedPositive pH J hj k x τ ε ).le]; have u : |mintW J N k x-1|≤ 2*eu^(k+1):= (scalar_ratio k _ _ ε (plated pH J hj x τ)).2.2; linarith only [(abs_le.mp u).2]
lemma projected (k:ℕ)(F:X×(↥J→G.El)→ℝ)(pF:Envelope F)(τ:1≤ (H.rep N p (j+1)).p.supportExponent)(ε: τL J N ≤ 1/4): Envelope (watch J N k F):=by
    let s:= honored pH J hj k τ ε; let u:= born pH J hj F pF; let y:= (born pH J hj _ s)
    refine ⟨( ( born pH J hj _ (s.mul pF) ).meas ).div y.meas,u.cost.choose+8*pF.cost.choose*τL J N^(k+1), fun i=>( norm_le_insert' _ ( birth J N F i ) ).trans ( add_le_add ( u.cost.choose_spec i ) ?_ )⟩; exact (tabulated pH J hj k F i pF pF.cost.choose pF.cost.choose_spec τ ε).2
end YM.Integration.Logwood.Vintage
