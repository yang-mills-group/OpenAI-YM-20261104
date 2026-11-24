import YM.SignedWilsonExpansion.Chron.Impulse
/-!
 # F6 §II-b, extra conditioning version on the SAME election.
 
  Save all unedited links off J _and_ the previous field (add both to X).
 The full positivity per-fibre makes for particularly straightforward tilt. No
 outside replacement, no inference about relative densities from different
 conditionings: we compute disintegrating exactly on the K walk's own
 effective action and predictor kernel (`StepData.density` sums tags with noise).

 Working at `j+1=K`: see elsewhere for estimator bill/tape. Scalar full (joint) measure
 acts on its true X×patch density. `scene` at j+1 as fine marginal.
-/
set_option autoImplicit false
set_option maxHeartbeats 760000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.Logwood.Vintage
open Set Function MeasureTheory Lattice RG Wilson OPE.Therm
open FVA1Physical.Exchange FVA1Physical.Exchange.F6Regular FVA1Physical.Exchange.RoseCut
open private split_patch external off_filling from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6OriginalMoments
open private fillPatch_meas from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6OriginalExterior
open private joined general_measured from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6MeasuredExterior
open private fibre_prob from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionNormalizedConnected
open scoped ENNReal Topology ContDiff Classical BigOperators
section
variable {U V W X E:Type*} [MeasurableSpace X] [MeasurableSpace V][Norm E][MeasurableSpace E]
variable {f:X→E}{g:V→X}
lemma stocked (x: Envelope f)(p:Measurable g): Envelope (f∘g):=⟨x.meas.comp p,x.cost.choose,fun i=>x.cost.choose_spec (g i)⟩
lemma passInt {x:X×V→ℝ} (hp:Envelope x) (μ:Measure V) [IsProbabilityMeasure μ]: Envelope fun y:X=>∫ z,x (y,z)∂μ:=by
    refine ⟨hp.meas.stronglyMeasurable.integral_prod_right'.measurable,hp.cost.choose,fun i=>?_⟩; simpa only [mul_one,probReal_univ] using norm_integral_le_of_norm_le_const (f:= fun z=> x (i,z)) (μ:=μ) ( Filter.Eventually.of_forall fun j=> hp.cost.choose_spec (i,j) )
lemma earnsPositive {x:X→ℝ}(hp:Envelope x)(p:∀ i,0<x i) (μ:Measure X)[IsProbabilityMeasure μ] : 0<∫i,x i ∂μ:=by
    refine (integral_pos_iff_support_of_nonneg (fun i=>(p i).le) (hp.integrable μ)).mpr ?_; rw [show Function.support x=Set.univ from Set.eq_univ_of_forall (fun i=> (p i).ne')]; simp
end
variable {G:Gauge}{c:Side}{H:History G}{j N p:ℕ}
local notation "πj" => ( prior G (H.S.side j p) )
local notation "C₀" => (H.S.side (j+1) p)
local notation "κ₀" => Config G (H.S.side j p)
local notation "π" => prior G C₀
local notation "ζ" => (scene H N p (j+1))
variable (pH:H.Selected)(J:Finset (Edge (Site (H.S.side (j+1) p))))
abbrev XU (H:History G)(j p) (J:Finset (Edge (Site (H.S.side (j+1) p)))) := Config G (H.S.side j p) × (({e:Edge (Site (H.S.side (j+1) p))//e∉J}→G.El))
local notation "X" => XU H j p J
abbrev coarse_haar : Measure X:= (πj).prod ( Measure.pi fun _:{e: Edge (Site C₀)//e∉J}=> G.probHaar )
abbrev patch_haar :Measure (↥J→G.El):=Measure.pi fun _:↥J=>G.probHaar
local notation "I" => ↥J→G.El
local notation "μ" => coarse_haar J
local notation "ρ" => patch_haar J
local notation "op" => ( H.levels.clock.op j p )
local notation "K" => (op).density ( H.β N p (j+1) )
def tintL (N:ℕ) (b: κ₀ × Config G C₀):ℝ:= dose (H:=H) (p:=p) (j+1) b.2 N * ( (op).density ( H.β N p (j+1) ) b.2 b.1 ) -- J unused
abbrev plumeL (x: X×(↥J→G.El)) : Config G C₀:= fillPatch J x.1.2 x.2
abbrev color (N:ℕ)(x:X×(↥J→G.El)):ℝ:= tintL N (x.1.1,plumeL J x)
def sale (N:ℕ)(x:X):ℝ:=∫w,color J N (x,w)∂ρ
abbrev φI (N:ℕ):= fibreLaw μ (sale J N)
abbrev ψI (N:ℕ)(x:X):= fibreLaw ρ (fun w=>color J N (x,w))
lemma kernel_positive (D:StepData c C₀) (k:D.patch.Branches D.kernel G) (σ:ℝ)(U:Config G C₀) (V:Config G c):0< D.density σ U V:=by
    have he: ∃ x:D.Choices,0 < D.likelihood U x:=by by_contra! h; have u: ∑ x, D.likelihood U x=0:= Finset.sum_eq_zero (fun i _=> le_antisymm (h i) (D.likelihood_pos U i)); rw [D.chosen k] at u; exact one_ne_zero u
    have hn q: 0< D.noise σ q V:= Finset.prod_pos fun i _=> mul_pos (inv_pos.mpr (D.penaltyZ_pos σ)) (Real.exp_pos _); obtain ⟨x,hx⟩:=he; exact Finset.sum_pos' (fun x _=> mul_nonneg ( D.likelihood_pos U x ) ( hn _ ).le) ⟨ x,Finset.mem_univ _,mul_pos hx ( hn _ )⟩
variable (hj:j<N)
lemma cloud_meas : Measurable (plumeL J):=(joined J).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
include pH hj
lemma tint_env : Envelope ( tintL (j:=j) (p:=p) (H:=H) N ):=by
    let S:= H.levels.clock.op j p; let β:= H.β N p (j+1)
    -- literal component function first on Config pair (kernel), only then flip
    have lum (G:Gauge) (c f:Side)(D:StepData c f)(β:ℝ)(hu:D.IsKernel β G): Envelope (fun y:Config G c×Config G f=> D.density β y.2 y.1) := by
       let Lum (x:Config G f×Config G c):=D.density β x.1 x.2; have hp: Envelope Lum:= by
          obtain ⟨C,hC⟩:= hu.bound; exact ⟨hu.meas,C,fun x=> (Real.norm_of_nonneg (hu.positive (x.1) (x.2)) ).trans_le (hC _ _)⟩
       exact (stocked (g:=fun y:Config G c × Config G f=>Prod.swap y) (f:=Lum) hp measurable_swap)
    have u: S.IsKernel β G:=(op).isKernel ( H.levels.blocks j p|>.branches ) β
    exact (stocked ( dose_env pH (p:=p) hj ) ( measurable_snd )).mul (lum G _ _ S β u)
lemma tint_pos (t: κ₀ × Config G C₀):0< tintL (j:=j) (p:=p) (H:=H) N t:=mul_pos (dose_positive pH hj _) (kernel_positive (op) (( H.levels.blocks j p ).branches) _ _ _) -- parse op
lemma color_env : Envelope (color J N):= stocked ( tint_env (p:=p) pH hj ) ( ( measurable_fst.comp measurable_fst ).prodMk (cloud_meas J) )
lemma color_pos (x:X)(w:I) : 0< color J N (x,w):= tint_pos pH hj _
lemma sale_env : Envelope (sale J N):= passInt (color_env pH J hj) ρ
lemma sale_pos (x:X): 0< sale J N x:= earnsPositive (x:=fun w=>color J N (x,w)) (stocked (color_env pH J hj) ( measurable_const.prodMk measurable_id )) (color_pos pH J hj x) ρ
lemma worth : IsProbabilityMeasure (φI J N):= fibre_prob μ ((sale_env pH J hj).integrable μ) (fun x=>(sale_pos pH J hj x).le) (earnsPositive (sale_env pH J hj) (sale_pos pH J hj) μ)
lemma minted (x:X): IsProbabilityMeasure (ψI J N x):= fibre_prob ρ ( Envelope.integrable (f:= fun w=> color J N (x,w)) ( stocked ( color_env pH J hj ) (measurable_const.prodMk measurable_id) ) _ ) (fun w=>(color_pos pH J hj x w).le) (sale_pos pH J hj x)
lemma weight {b:κ₀×Config G C₀→ℝ} (he:Envelope b):
   ( ∫x,∫w,color J N (x,w)*b (x.1, plumeL J (x,w))∂ρ∂μ )=
   ( ∫x,tintL (j:=j) (p:=p) (H:=H) N x*b x∂ (πj).prod π):=by
    let f:=fun x=> tintL (j:=j) (p:=p) (H:=H) N x*b x; have h:= ( tint_env (p:=p) pH hj ).mul he; let F(x:X×(↥J→G.El)):= f (x.1.1, plumeL J x); have hz: Envelope F:= stocked h ((measurable_fst.comp measurable_fst).prodMk (cloud_meas J))
    rw [ integral_prod _ (( passInt hz ρ ).integrable _), integral_prod _ (h.integrable _) ]; apply integral_congr_ae; exact Filter.Eventually.of_forall fun x=> (split_patch J ( fun U=> f (x,U)) (stocked h (measurable_const.prodMk measurable_id)) ).symm
lemma notices {x:Config G C₀→ℝ}(he:Envelope x):
   ( ∫y,tintL (j:=j) (p:=p) (H:=H) N y*x y.2∂(πj).prod π )= ∫i,x i ∂ζ:=by
    rw [integral_prod_symm _ (((tint_env (p:=p) pH hj).mul ( show Envelope ( fun y:κ₀ × Config G C₀=> x y.2 ) from stocked he measurable_snd )).integrable _),account pH hj]; apply integral_congr_ae; filter_upwards with i; unfold tintL; dsimp only; rw [integral_mul_const,integral_const_mul,(op).density_total ( H.levels.blocks j p|>.branches ),mul_one]; rfl
lemma sold1 : (∫i,sale J N i∂μ)=1:=by let _:=probability (p:=p) pH hj; simpa only [sale,mul_one,integral_const,probReal_univ,one_smul] using ( (weight pH J hj (Envelope.const 1)).trans (notices pH hj (Envelope.const 1)) ) -- need p
lemma measured {x:κ₀×Config G C₀→ℝ}(he:Envelope x):
    (∫y,∫w,x ( y.1 , plumeL J (y,w) )∂( ψI J N y )∂( φI J N ))= ∫i,tintL N i*x i∂(πj).prod π:=by
    rw [general_measured μ (sale_env pH J hj).meas (fun i=>(sale_pos pH J hj i).le), sold1 pH J hj, div_one, ← weight pH J hj he ]; apply integral_congr_ae; filter_upwards with i; let v:Envelope (fun w=>color J N (i,w)):= stocked (color_env pH J hj) (measurable_const.prodMk measurable_id); rw [general_measured ρ v.meas (fun w=>(color_pos pH J hj i w).le),mul_comm]; exact div_mul_cancel₀ _ (sale_pos pH J hj i).ne' -- denominator delta
end YM.Integration.Logwood.Vintage
