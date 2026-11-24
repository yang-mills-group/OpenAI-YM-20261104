import YM.SignedWilsonExpansion.Chron.Lamp
/-!
# Complex conditional F6 in the (previous field V,exterior links saved)
variant. Charge bounds INCLUDE normalization of the denominator, and treat
foregound in the WHOLE edit. Distinguish the thermal Taylor
index k from the Wilson polynomial index. No use here of independent
XSpace data. Propagate estimates on joint law and confirm inherited field's
true marginal.
-/
set_option autoImplicit false
set_option maxHeartbeats 790000
noncomputable section
set_option quotPrecheck false
namespace YM.Integration.Logwood.Vintage
open MeasureTheory Lattice RG Wilson OPE.Therm
open FVA1Physical.Exchange FVA1Physical.Exchange.F6Regular FVA1Physical.Marked.Inherited
open private general_measured from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6MeasuredExterior
open private subenv from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6RegularCovariance
open scoped ENNReal Topology ContDiff Classical BigOperators
variable {G:Gauge}{H:History G}{j N p k:ℕ}
-- no local notation used in variable declarations
variable (pH:H.Selected) (J:Finset (Edge (Site (H.S.side (j+1) p)))) (hj:j<N)
local notation "X" => (XU H j p J)
local notation "ρ" => (φI J N)
local notation "U" => ( X×(↥J→G.El) )
local notation "Γ" => (Config G (H.S.side (j+1) p))
local notation "Ω" => (τL J N)
include pH hj
/-- confirmation: the coarser-field marginal in Inter is real, before separating patch. -/
lemma marginal (F:Config G (H.S.side j p)→ℝ)(v:Envelope F):
    (∫y,tintL (j:=j) (H:=H) (p:=p) N y*F y.1∂(prior G (H.S.side j p)).prod (prior G (H.S.side (j+1) p)))=∫i,F i∂scene H N p j:=by
   let W:= H.levels.clock.op j p
   rw [integral_prod _ ((( tint_env (p:=p) pH hj ).mul ( show Envelope (fun y:Config G (H.S.side j p) × Config G (H.S.side (j+1) p) => F y.1) from stocked v measurable_fst )).integrable _),account pH hj.le F]; apply integral_congr_ae; filter_upwards with i
   unfold tintL; rw [integral_mul_const]; let Z₀:= Wilson.partition G (H.S.side N p) (H.β N p N); unfold dose; simp_rw [div_mul_eq_mul_div, integral_div]; rw [( pH.steps N p j hj ).1]; change (∫w,(H.rep N p (j+1)).eval w*W.density ( H.β N p (j+1) ) w i ∂ _ )/Z₀* F i=( ∫w,W.density ( H.β N p (j+1) ) w i* (H.rep N p (j+1)).eval w ∂ _ )/Z₀ * F i; have h (w): W.density ( H.β N p (j+1) ) w i* ( H.rep N p (j+1) ).eval w=(H.rep N p (j+1)).eval w * W.density ( H.β N p (j+1) ) w i:=mul_comm ..
   simp only [h]
/-- inherited marginal after separating patch. -/
lemma φI_true (F:Config G (H.S.side j p)→ℝ)(v:Envelope F): (∫i,F i.1∂φI J N)=∫i,F i∂scene H N p j:=by
   let u : Envelope (fun y:Config G (H.S.side j p)× Config G (H.S.side (j+1) p)=> F y.1 ):= stocked v measurable_fst
   have h i: (∫w:(↥J→G.El),F i.1∂ψI J N i)= F i.1:=by letI:=minted pH J hj i; simp
   have p:= ( measured pH J hj u ).trans ( marginal pH hj F v ); simp only [h] at p; exact p
lemma seals (F:U→ℝ)(z:Envelope F) : Envelope (plainL J N F) ∧ Envelope (sealL J N F) ∧ ∀ i, sealL J N F i= plainL J N ( F* dollar J N ) i- plainL J N F i* plainL J N ( dollar J N ) i:=by
   let u:= weighed pH J hj
   have hT(F:U→ℝ)(v:Envelope F): Envelope (plainL J N F):= by
      let g :=(Real.exp ∘ dollar J N); have hz: plainL J N F=fun x=>birth J N (g*F) x /birth J N g x:=funext fun i=> general_measured (ψI J N i) (beamA u.exp i).meas (fun _=>(Real.exp_pos _).le) _
      refine ⟨ hz ▸ (( born pH J hj _ (u.exp.mul v) ).meas.div ( born pH J hj _ u.exp).meas),v.cost.choose,fun i=>?_⟩ -- rewrite orientation?
      unfold plainL; letI:=cashout pH J hj i; simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:= tallL J N i) ( Filter.Eventually.of_forall fun w=> v.cost.choose_spec (i,w) )
   have h i: sealL J N F i= plainL J N ( F* dollar J N ) i-plainL J N F i* plainL J N ( dollar J N ) i:=by letI:=cashout pH J hj i; simpa only [sub_zero,sealL,plainL,Pi.mul_apply] using first_is_covariance (tallL J N i) (fun w=>F (i,w)) (fun w=> dollar J N (i,w)) ( beamA z i ) ( beamA u i ) 0
   exact ⟨ hT F z,( show sealL J N F= ( plainL J N ( F*dollar J N ) )- plainL J N F* plainL J N ( dollar J N ) from funext h ) ▸ subenv ( hT _ (z.mul u) ) (( hT _ z ).mul ( hT _ u ) ),h⟩
lemma denomPositive (k:ℕ)(x:X)(τ:1≤(H.rep N p (j+1)).p.supportExponent)(z: Ω≤1/4) : ( 0<levy J N k x ) ∧ 0<∫w,tiltTaylor k (- dollar J N (x,w)) ∂tallL J N x:=by
   have hx:= ( tabulated pH J hj k (fun _=> (1:ℝ)) x (Envelope.const _) 1 (fun w=>abs_one.le) τ z ).1; let μ:=ψI J N x; letI:= minted pH J hj x; let W(w):= Real.exp ( dollar J N (x,w) ); let u:= ( beamA ( weighed pH J hj ) x ).exp; let K(w):= tiltTaylor k (- dollar J N (x,w)); unfold tallL; rw [general_measured (ψI J N x) u.meas (fun _=>(Real.exp_pos _).le) K]; exact ⟨hx,div_pos hx (earnsPositive u (fun _=>Real.exp_pos _) _)⟩
section
-- equivalent to treating complex integrals, here sign conventions via split.
omit pH hj
abbrev duplex (L:(U→ℝ)→ X→ℝ)(F:U→ℂ)(x:X):ℂ:=⟨ L (Complex.re ∘ F) x, L (Complex.im ∘ F) x ⟩
def paths (N k:ℕ) := duplex J ( watch J N k )
abbrev primary (N:ℕ):= duplex J ( birth J N )
abbrev baseL (N:ℕ) := duplex J ( plainL J N )
abbrev sealB (N:ℕ) := duplex J ( sealL J N )
def tableR (N e:ℕ) (F:U→ℂ):= Slate ( φI J N ) ( paths J N e F )
def abacus (N:ℕ)(F:U→ℂ):= baseL J N F-sealB J N F
def excessL (N e:ℕ)(F:U→ℂ):= Slate ( φI J N ) ( paths J N e F-abacus J N F )
include pH hj
lemma fits_tally (F:U→ℂ)(v:Envelope F)(x:X): Slate (ψI J N x) (fun w=>F (x,w))=primary J N F x:=by
   letI:=minted pH J hj x; apply Complex.ext
   · exact ( integral_re (intE ( beamA v x ) ( ψI J N x )) ).symm
   exact ( integral_im (intE ( beamA v x ) ( ψI J N x )) ).symm
lemma optimistic : Mood (scene H N p (j+1)) (φI J N) (fun F=> primary J N ( F∘plumeL J )):=by
   let L:=fun F:Γ→ℂ=> primary J N ( F∘plumeL J ); have he F (t:Envelope ( F:Γ→ℂ )): Envelope ( L F ):=env_join ( born pH J hj _ (splitRe ( stocked t ( cloud_meas J ) )) ) (born pH J hj _ ( splitIm ( stocked t ( cloud_meas J ) ) ) ); refine ⟨he,?_,?_⟩
   · intro F hp; letI:= OPE.Therm.probability (p:=p) pH hj; letI:= worth pH J hj
     have hw(A:Γ→ℝ)(pA:Envelope A): ( ∫i,birth J N ( A∘plumeL J ) i∂φI J N )=∫i,A i∂ scene H N p (j+1):=( measured pH J hj (stocked pA measurable_snd) ).trans ( notices pH hj pA )
     apply Complex.ext
     · change RCLike.re ( Slate (φI J N) ( L F ) )=RCLike.re (Slate (scene H N p (j+1)) F); unfold Slate; rw [← integral_re ( intE ( he F hp ) _ ), ← integral_re ( intE hp _ ) ]; exact hw _ ( splitRe hp )
     change RCLike.im ( Slate (φI J N) ( L F ) )=RCLike.im ( Slate (scene H N p (j+1)) F ); unfold Slate; rw [← integral_im ( intE ( he F hp ) _ ), ← integral_im ( intE hp _ ) ]; exact hw _ (splitIm hp)
   intro z; funext i; letI:= minted pH J hj i; rw [ ← fits_tally pH J hj _ ( stocked ( show Envelope (fun _ : Γ=>z) from ⟨ measurable_const,_,fun x=> le_rfl⟩ ) ( cloud_meas J ) ) i ]; simp [Slate]
variable {b:ℝ}
local notation "A1" => (τL J N)
structure Bronze (J:Finset (Edge (Site (H.S.side (j+1) p))))(F:Config G (H.S.side (j+1) p)→ℂ)(N:ℕ)(b:ℝ) : Prop where -- explicit binders
    previous : j<N
    toll : τL J N ≤ 1/4
    funded : Envelope F ∧ ∀u, ‖F u‖≤ b
    radiant : Mood (scene H N p (j+1)) (φI J N) (fun A=> primary J N (A∘plumeL J))
    marg : ∀ F:Config G (H.S.side j p)→ℝ,Envelope F→(∫i,F i.1 ∂φI J N)=∫i,F i∂scene H N p j
    hereditary : IsProbabilityMeasure (φI J N)
    exterior : ∀x,IsProbabilityMeasure (ψI J N x) ∧ IsProbabilityMeasure (tallL J N x)
    solvent : ∀ k x,0< levy J N k x ∧ 0<∫w,tiltTaylor k (- dollar J N (x,w)) ∂tallL J N x
    receipts : ∀x,3/4≤ levy1 J N x ∧
        -- FIRST kept - T/Q term
        paths J N 1 ( F∘plumeL J ) x= baseL J N ( F∘plumeL J ) x-(levy1 J N x)⁻¹ • sealB J N ( F∘plumeL J ) x ∧
        ‖primary J N ( F∘plumeL J ) x-abacus J N ( F∘plumeL J ) x‖≤24*b*τL J N^2
    tiltAction : ∀ A: XU H j p J × (↥J→G.El)→ℝ, Envelope A→ ∀ x, sealL J N A x= plainL J N ( A* dollar J N ) x- plainL J N A x* plainL J N ( dollar J N ) x
    registers : Envelope (baseL J N ( F∘plumeL J )) ∧ Envelope (sealB J N ( F∘plumeL J ))
    around : ∀k, Envelope ( paths J N k ( F∘plumeL J ) ) ∧ ∀x,‖paths J N k ( F∘plumeL J ) x-primary J N ( F∘plumeL J ) x‖ ≤ 16*b*τL J N^(k+1)
    computes : ∀d, tableR J N d ( F∘plumeL J )= Slate (φI J N) ( baseL J N ( F∘plumeL J ) )- Slate (φI J N) ( sealB J N ( F∘plumeL J ) ) + excessL J N d ( F∘plumeL J )
    prices : ∀d:ℕ,0<d→ ‖excessL J N d ( F∘plumeL J )‖ ≤40*b*τL J N^2
    restores : ∀k, ‖tableR J N k ( F∘plumeL J )- Slate (scene H N p (j+1)) F‖≤16*b*τL J N^(k+1)
lemma flavored (F:Γ→ℂ)(hp:Envelope F)(hb:∀u,‖F u‖≤ b)(τ:1≤(H.rep N p (j+1)).p.supportExponent) (z: ( τL J N ) ≤1/4) : Bronze J F N b:=by
   let A:= F∘plumeL J; let pA:=stocked hp ( cloud_meas J ); let F₁:= Complex.re∘ A; let F₂:= Complex.im∘ A; let x:= splitRe pA; let y:= splitIm pA; have px u: |F₁ u|≤ b:=( Complex.abs_re_le_norm _ ).trans ( hb _ ); have py u: |F₂ u|≤ b:=( Complex.abs_im_le_norm _ ).trans ( hb _ ); let xB:=seals pH J hj F₁ x; let yB:=seals pH J hj F₂ y; have hB: Envelope ( baseL J N A ):= env_join xB.1 yB.1; have hF: Envelope ( sealB J N A ):= env_join xB.2.1 yB.2.1; let P:=primary J N A; let Q:=baseL J N A; let T:=sealB J N A; let L:=paths J N; let Y(i:ℕ):= paths J N i A; let μ:=φI J N; let t:= ( τL J N ); letI:=worth pH J hj
   have hx:= fun i=> initial pH J hj F₁ i x b px τ z; have hy:= fun i=> initial pH J hj F₂ i y b py τ z
   have push (i): ‖P i-(Q-T) i‖≤24*b*t^2:= (Complex.norm_le_abs_re_add_abs_im _ ).trans (( add_le_add (hx i).2.2 ( hy i ).2.2 ).trans_eq (by unfold t; ring)) -- via defeq
   have hr (k i): ‖Y k i-P i‖≤16*b*t^(k+1):=( Complex.norm_le_abs_re_add_abs_im _ ).trans (( add_le_add ( tabulated pH J hj k F₁ i x b px τ z ).2 (tabulated pH J hj k F₂ i y b py τ z).2 ).trans_eq (by unfold t; ring))
   have hu (k):Envelope (Y k):=env_join ( projected pH J hj k F₁ x τ z ) ( projected pH J hj k F₂ y τ z ); let B:=optimistic pH J hj; refine ⟨ hj,z,⟨hp,hb⟩,B,φI_true pH J hj,worth pH J hj,fun x=>⟨minted pH J hj x,cashout pH J hj x⟩, fun k i=> denomPositive pH J hj k i τ z,?_,fun F h=>(seals pH J hj F h).2.2,⟨hB,hF⟩,fun k=> ⟨hu k,hr k⟩,?_,?_,?_⟩
   · intro i; refine ⟨(hx i).1,?_,push i⟩; have a p: p / levy1 J N i=(levy1 J N i)⁻¹*p:=by rw [div_eq_mul_inv,mul_comm]
     apply Complex.ext
     · rw [ Complex.sub_re,Complex.real_smul ]; simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; exact (hx i).2.1.trans (congr_arg _ ( a _ ))
     rw [Complex.sub_im,Complex.real_smul]; simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]; exact (hy i).2.1.trans ( congr_arg _ ( a _ ) )
   · intro k; have m {f g}(w:Envelope f)(v:Envelope g): Slate μ ( f-g )= Slate μ f-Slate μ g:= integral_sub ( intE w μ ) ( intE v μ ); change Slate μ (Y k)=Slate μ Q-Slate μ T+Slate μ (Y k-(Q-T)); rw [m (hu k) (envN hB hF), m hB hF]; abel
   · intro d hd; apply ( norm_integral_le_of_norm_le_const (μ:=μ) (C:=40*b*t^2) (?_)).trans (by simp [t])
     filter_upwards with i; change ‖Y d i-(Q-T) i‖≤_; refine ( norm_sub_le_norm_sub_add_norm_sub _ (P i) _ ).trans ( ( add_le_add (hr d i) ( push i ) ).trans ?_ ); have b₀:= ( norm_nonneg _ ).trans ( hb 1 ); have hw:0 ≤t:= ( abs_nonneg _ ).trans ( plated pH J hj (i,1) τ ); nlinarith only [mul_le_mul_of_nonneg_left ( pow_le_pow_of_le_one hw ( z.trans (by norm_num) ) (show 2≤d+1 by omega) ) b₀]
   intro k; unfold tableR; rw [ ← B.salary F hp ]; unfold Slate; rw [ ← integral_sub ( intE ( hu k ) μ ) ( intE ( B.around F hp ) μ ) ]; exact ( norm_integral_le_of_norm_le_const (μ:=μ) (C:=16*b*t^(k+1)) (Filter.Eventually.of_forall fun i=> hr k i) ).trans_eq (by simp [t])
end
end YM.Integration.Logwood.Vintage
