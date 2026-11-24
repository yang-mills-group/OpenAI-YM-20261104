import YM.FVAAlt2.Mass.Lengths
import YM.Pert.Scale.Engineering
import YM.FormalOPE.RG10.Position.Polys
/-! # Smearing scale-homogeneity bound.Two-sided costs. Free exact.G. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Mass
open Function Finset Filter MeasureTheory Topology Set Metric
open Labels Precision Extra.FD Maxwell Extraction FormalOPE FormalOPE.RG10 RG10.Position.Grade
open PertExtension PertExtension.LatticePT PertExtension.Position PertExtension.Position.Triangle RG10.Position RG10.Gazebo RG10.Carryon RG10.InversionTop
open MS MS.Koszul MS.Menus MS.Book MS.Local.Physical MS.Land MS.FVA.Currency
open PowerSeries (C coeff constantCoeff)
open Home Home.Report Matrix Home.Profiles Convert Next.UVStress
open Real
open scoped Topology BigOperators PowerSeries ContDiff Classical Matrix
variable {G:Gauge} {F: Frames G}{B: MS.Local.Physical.Deck G}{M: Land.Booked B}{d m n:ℕ}
local notation "E" d=> RG10.Position.Deck F d
local notation "P0"=> price -- ambiguous?
-- geometric root weight. use any spaces.
abbrev tallyW {I:Type*}(w:I→ℕ)(v:Datum I): ℕ:= ∑ i:Fin v.1.n,w ( v.2 i )
local notation "lX"=> Deck.price F d
abbrev scaleT (s:ℝ) (v:Test m): Test m:= Next.UVStress.dilate (exp_pos s) v
-- opposite counter-dial of fields scheme.$Street
abbrev nearD {I:Type*}(s:ℝ)(p:Datum I) : Datum I:= ⟨⟨p.1.n,scaleT s p.1.test⟩,p.2⟩
lemma near_op {I:Type*}(s:ℝ)(p:Datum I): nearD s p=RG10.Position.dial (-s) p:= by
 change nearD s p=nearD (- -s) p; rw [neg_neg]
lemma near_app {I:Type*}(f:Test m)(x: Fin m→ I)(s:ℝ): nearD s ⟨⟨m,f⟩,x⟩= ⟨⟨m,scaleT s f⟩,x⟩:=rfl
variable (F)
def style (v:Datum (RG10.Position.Deck F d)):ℕ:= tallyW (Deck.price F d) v
local notation "g"=> style F
lemma weight_freeT (p:Datum ( E d )) (x:Points p.1.n) (hx:x∈ conf p.1.n)(s:ℝ): moving (g p) s • wickB F ( Position.deck F d ) p.2 (exp s • x)= wickB F ( Position.deck F d ) p.2 x:= by
 let X i:= writes F d (deck F d (p.2 i)); let f(i:Fin p.1.n):= Deck.price F d (p.2 i); have he(i): Exact ( X i ) ( f i ):= by unfold X; rw [RG10.Position.deckAt]; exact leaf_cost F d (p.2 i)
 obtain h:= Pert.Scale.rising_moment hx he ( exp_pos s|>.ne' ); rw [ MultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum ] at h
 unfold moving; rw [ Complex.real_smul, Complex.ofReal_pow ]; exact h
lemma free_tally (p:Datum ( E d ))(s:ℝ): moving (style F p) s * RG10.Gazebo.raw F d (nearD s p)=RG10.Gazebo.raw F d p := by
 classical obtain ⟨⟨j,f⟩,u⟩:=p; rw [near_app]; unfold RG10.Gazebo.raw; simp_rw [freeσ F]; let p:Datum ( E d ):= ⟨⟨j,f⟩,u⟩; let H(v:Points j):=wickB F ( Position.deck F d ) u v; let c:=moving (style F p) s; let a:= (exp_pos s)
 change c*((dilate a f).applyTo H).re=( f.applyTo H ).re; rw [zoom_integral]; refine Eq.trans (Complex.smul_re c (f.applyTo (fun x => H (exp s • x))) ).symm ?_; apply congr_arg Complex.re; unfold Test.applyTo; rw [ ← integral_smul ]; apply integral_congr_ae; filter_upwards with x; by_cases hx:x∈ conf j; · rw [ ← mul_smul_comm, show c • H ( exp s • x )= _ from ( weight_freeT F p x hx s ) ]
 simp only [f.vanishes hx,zero_mul,smul_zero]
variable {F}
def EvenCost {I:Type*}(w:I→ℕ)(p:Datum I→fps): Prop:=∀ (v:Datum I) (i:ℕ), Polys (fun s:ℝ=> moving (tallyW w v) s * coeff i (p (nearD s v)))
variable (X:MS_Data G M)(μ:ℝ)
section
variable {D:ChartRatio G}(h:LocalRatio D){H:Source.Hol G}{L:Frames G}(R: Lobby.Registry L H)(hg:G.Simple)
lemma send_r {x:Points n}(s:ℝ): realize (exp s • x)= exp s • realize x:= by funext i; rw [realize, PiLp.smul_apply, map_smul]; rfl
lemma for_profile (s:ℝ)(j:ℕ)(f:Test n)(p:Fin n→Rake.Label B) : Integrable (fun x=> f x*area X p μ j (exp s • x)):= f.smearing fun x h=> ContinuousAt.continuousWithinAt (ContinuousAt.comp (f:=fun v=> realize ( exp s • v )) ( Dial.contin X p _ (realize_one (Next.UVStress.enlarged ( exp_pos s ) x |>.1 h)) Finset.univ j μ|>.1) ((realize_s.comp (continuous_const_smul ..)).continuousAt)) -- backlog
include h R hg
lemma extent (j:ℕ)(f:Test n)(p:Fin n→ Rake.Label B) : Polys (fun s:ℝ=> moving (Lobby.wt p) s * coeff j (forecast X p μ (Subspace.pcanon ( scaleT s f )))):=by
 let K:= tsupport f; let F (s:ℝ)(x:Points n):= area X p μ j (exp s • x)
 let A(s:ℝ):= moving (Lobby.wt p) s; obtain ⟨c,hc,k,hW⟩:= sizedA X μ p (K:=tsupport f) f.hasCompactSupport f.tsupport_subset Finset.univ j
 have Hx(s:ℝ)(x:Points n)(hx:x∈tsupport f): ‖A s • F s x‖ ≤ c*(1+|μ+s|)^k:=by unfold F area; rw [ send_r s ]; exact hW ⟨s,x,hx⟩
 let y:= fun s:ℝ=>c*(1+|μ+s|)^k; have hf : Integrable (fun x=> f x):= f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport; let b:= ∫ x:Points n, ‖f x‖; have hb:0≤b:= integral_nonneg fun _=> norm_nonneg _
 have hx(s:ℝ): ‖A s*coeff j (forecast X p μ (Subspace.pcanon (scaleT s f)))‖ ≤ b*y s:= by
      rw [ Subspace.forecastR (q:=2) μ h X p hg (by decide) ( scaleT s f ) R ]; change ‖A s *( (Next.UVStress.dilate (exp_pos s) f ).applyTo _ ).re‖ ≤ _
      rw [zoom_integral]; change ‖A s*( ∫ x:Points n, f x*F s x ).re‖ ≤_; rw [Real.norm_eq_abs, show A s*_=( A s • ( ∫ x:Points n, f x*F s x ) ).re from (Complex.smul_re (A s) (∫ x:Points n, f x*F s x)).symm ]; apply le_trans ( Complex.abs_re_le_norm _ ); rw [ ← integral_smul ]; apply norm_integral_le_integral_norm _ |>.trans; unfold b; rw [ ← integral_mul_const ]; apply integral_mono ((for_profile X μ s j f p).smul (A s) ).norm (hf.norm.mul_const _); intro x; change ‖A s • (f x * F s x)‖ ≤ ‖f x‖ * y s; by_cases H:x∈tsupport f; · rw [ ← mul_smul_comm,norm_mul ]; exact mul_le_mul_of_nonneg_left (Hx s x H) (norm_nonneg _)
      simp only [ image_eq_zero_of_notMem_tsupport H, zero_mul, norm_zero, smul_zero,le_refl ]
 refine ⟨k,b*(c*(1+|μ|)^k),by positivity,fun s=> ( hx s ).trans ?_⟩; rw [mul_assoc b]; apply mul_le_mul_of_nonneg_left _ hb; unfold y; rw [ mul_assoc c, ← mul_pow ]; gcongr; nlinarith [ abs_nonneg s, abs_nonneg μ,abs_add_le μ s ]
lemma science_cost : EvenCost ( Deck.price F d ) (science μ X F d):=by
 intro b k; obtain ⟨⟨m,f⟩,p⟩:=b; let w(j:Fin m):= Deck.price F d (p j); let Q:=∑ j:Fin m,w j; let Y: Matrix _ _ ℝ:=dout F B d
 let X₀(i:Fin m→Glyph B d)(s:ℝ):= currentM μ X ( ⟨⟨m,scaleT s f⟩,i⟩:Datum ( Glyph B d ) )
 let Y₀(i:Fin m→Glyph B d):ℝ:= ∏ j: Fin m, Y (p j) (i j)
 have ht(s:ℝ): science μ X F d (⟨⟨m,scaleT s f⟩,p⟩:Datum ( E d )) =∑ i:Fin m→Glyph B d,X₀ i s*C ( Y₀ i ):= by
    unfold science mix; refine Finset.sum_congr rfl fun i _=>?_ ; unfold Y₀; rw [map_prod C]; rfl
 change Polys (fun s:ℝ=> moving Q s * coeff k (science μ X F d ⟨⟨m,scaleT s f⟩,p⟩ )); simp_rw [ht, map_sum,Finset.mul_sum, PowerSeries.coeff_mul_C,←mul_assoc]; apply Polys.sum (fun i s=> (moving Q s *coeff k (X₀ i s))*Y₀ i); intro i hi; by_cases H: ∃ j:Fin m,w j≠ Glyph.size (i j)
 · obtain ⟨j,hj⟩:=H; obtain he:Y (p j) ( i j )=0:=( higher0 F B d _ _ hj ).1; simp_rw [show Y₀ i=0 from Finset.prod_eq_zero ( mem_univ j ) (f:=fun x:Fin m=>Y (p x) (i x)) he,mul_zero]; exact Polys.const _
 push Not at H; have he : Q=Lobby.wt ( Lobby.owner ∘ i ):= by unfold Q; rw [ funext H ]; rfl
 rw [ he ]; exact Polys.muls ( extent X μ h R hg k f (Lobby.owner∘i)) (Polys.const ( Y₀ i ))
end
end YM.FVAAlt2.Mass
