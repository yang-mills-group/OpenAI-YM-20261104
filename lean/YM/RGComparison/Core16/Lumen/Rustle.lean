import YM.RGComparison.Core16.Lumen.Burst

/-! # Uniform local Taylor observation with word, all periods/tags
Proof pays coefficient and test-coordinate costs (public estimates eventually include C(n-and-derivatives)).
Estimator at stencil/κ/separation, internal MM receipts needed elsewhere (not assuming any here).
Swing n=0 provides zeroth growth estimate needed later. Also differentiating payloads can choose
N appropriately enlarged INCLUDING every needed mask location; API `Visible`. Does not certify
incomplete support footprints by the Reader label-equations. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Push.Uniform Forge
open Planet Finset
open PertExtension PertExtension.Series Tested Radial
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{S:Side}{ι k T A D L:Type}[Fintype ι][Fintype k][Fintype T][Fintype L][Fintype D]
variable {X:Shelf G A D} {P:Planet X S ι k T}

def Error (r:ℕ)(f:Melody G ι)(ψ:(L→G.Color)→ℝ)(p: Stuff G ι L) (g:ℝ)(x:Sky G ι):= f g x-untilB (fun j=>tale p ψ j g x) r g
namespace Error
variable {f: Melody G ι} {ψ:(L→G.Color)→ℝ}{p:Stuff G ι L}{N:ℕ}{c:ℝ}

private lemma promise (Y:Good X) (h:ContDiffAt ℝ ∞ ψ 0)(r:ℕ) (c:ℝ)(hc:0≤c): ∃ z:ℝ,0 ≤ z ∧ ∀ᶠ s:ℝ in atTop,∀ (ι:Type)(f: Melody G ι) p N (hp:Visible X ψ f p N c) x,
    crisp (fare s) hp.stamp.choose x → |Error r f ψ p (dollar s) x| ≤ z*(s^4)^r*dollar s^r :=by
    -- no Fintype ι needed
    cases r with
    | zero=> refine ⟨c,hc,?_⟩; filter_upwards [willing Y] with s he ι f p N hp x hx; simpa only [Error,untilB,pow_zero,range_zero, sum_empty,sub_zero,mul_one] using hp.price _ he x
    | succ r=>
      obtain ⟨δ,C,hd,hc,h⟩:= Radial.deposition ψ r h
      refine ⟨C,hc,?_⟩
      filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop X.Q,fare_falls.eventually (gt_mem_nhds hd),fare_falls.eventually (gt_mem_nhds (half_pos Y.extent.1)),willing Y] with s hs hQ hr ht hv ι f p N hp x hx
      let J:=hp.stamp.choose; obtain ⟨-,he,hH⟩:= hp.stamp.choose_spec; let u:=book p (dollar s) x; let g:=dollar s; have hy : ‖u‖≤ s^4:= dock he (hQ.trans (by calc s = s^1 := by simp
                                                                                                                   _ ≤ s^4:= by gcongr; norm_num)) hx
      have hz: 0<g:= dollar_pos _
      unfold Error; rw [hH g hv hz x (crisp_negligible _ _ (show fare s < X.δ/2 from ht).le (le_refl _) hx)] -- unfold? matches
      have hh:= h u g hz ((mul_le_mul_of_nonneg_left hy hz.le).trans (show fare s<δ from hr).le)
      exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy _) hc) (by positivity))

lemma residents (X:Shelf G A D) : ∀ᶠ s:ℝ in atTop, ∀ (S: Side)(ι k T:Type)(_:Fintype ι)(_:Fintype k)(_:Fintype T)(P:Planet X S ι k T), P.Steady→amen X (dollar s)→ ∀ J:Finset ι,
   (∫ x in {w:Sky G ι|crisp (fare s) J w}ᶜ, P.bureau (dollar s) x ∂ skillet G ι) ≤ J.card*ruin s*P.pot (dollar s) :=by
    filter_upwards [shield X.sector G] with s hs S ι k T _ _ _ P hP hv J
    let V:= {x:Sky G ι| crisp (fare s) J x}; let g:=dollar s; let W:=P.bureau g; let M:=skillet G ι
    refine (union_cost J (fun i=> breach i s) (fun j _=> breach_borel ..) W ((bureau_env hP hv).integrable M) (fun i=>bureau_pos hP hv i|>.le) Vᶜ (crisp_open ..).isClosed_compl.measurableSet ?_).trans ((sum_le_sum (g:= fun _=> ruin s * P.pot g) (fun i _=> hs _ _ _ _ _ _ _ _ (hP.tickets _ hv) i)).trans_eq ?_)
    · intro x hx; change ¬crisp (fare s) J x at hx; unfold crisp at hx; push Not at hx
      have h : 0≤fare s:=by unfold fare; have := dollar_pos s; positivity
      obtain ⟨i,hk,hp⟩:= hx; exact ⟨i,hk,pow_le_pow_left₀ h hp 2⟩
    rw [sum_const,nsmul_eq_mul,mul_assoc]
lemma widening {K : Type*} [MeasurableSpace K]{f g:K→ℝ}(h:Envelope f)(he:Envelope g):Envelope (f-g):=by rw [sub_eq_add_neg]; exact h.add he.neg

-- Expect expanded RHS term-by-term, same denominator. cap property used even at an eventual
-- date AP within δ/Stage, not a prior estimate of future polynomial order.
variable {g:ℝ}(H:P.Steady)(hf:Visible X ψ f p N c)(he:amen X g)
include H hf he
lemma literacy (r:ℕ) : Envelope (Error r f ψ p g):=widening (hf.env _ he) (havenreal (continuous_finsetSum _ fun i _=> continuous_const.mul ((hf.uses H.prices i).cont g)))
lemma tribute (r:ℕ)(w:Rail G ι) : P.expect g (sing w g * Error r f ψ p g) = P.expect g (sing w g * f g) -
     ∑ i∈range r,g^i * P.expect g ((sing w*tale p ψ i) g):=by
    let t i:= (sing w*tale p ψ i) g; let y:= sing w g; have ht i : Envelope (g^i • t i):= (Envelope.const _).mul ((havenreal (sing_cont ..)).mul (havenreal ((hf.uses H.prices i).cont g)))
    rw [show sing w g* _ = y*f g- ∑ i∈range r,g^i • t i from ?_, expect_sub H he (f:=y*f g) (f':=∑ i∈range r,g^i • t i) ((havenreal (sing_cont w g)).mul (hf.env _ he)) (havenreal (show Continuous _ from ?_)), paid H he (range r) (fun i=> g^i • t i) _]
    · simp_rw [Planet.expect_mul]; rfl -- elaboration
    · exact fun i _=> ht i
    · simp_rw [show ∑ i∈range r,g^i • t i= fun x=>∑ i∈range r,(g^i • t i) x from funext (fun i=> Finset.sum_apply ..)]
      exact continuous_finsetSum _ fun i _=> (continuous_const (y:=g^i)|>.smul ((sing_cont ..).mul ((hf.uses H.prices i).cont g)))
    funext x; simp only [Pi.sub_apply,Pi.mul_apply,Finset.sum_apply,Error,untilB, mul_sub, Finset.mul_sum, Pi.smul_apply, smul_eq_mul,y,t]; congr 1; apply sum_congr rfl; intro; intros; ring
omit H hf he
-- deterministic log powers, into any eventually uniformly paid choice
lemma motion (Y:Good X)(ψ:(L→G.Color)→ℝ)(hψ:ContDiffAt ℝ ∞ ψ 0)(r d N:ℕ)(c:ℝ)(hc:0≤ c): ∃ C:ℝ,0≤ C ∧ ∀ᶠ s:ℝ in atTop,∀ (S: Side)(ι k T:Type)(_:Fintype ι)(_:Fintype k)(_:Fintype T)(P:Planet X S ι k T)(_:P.Steady)
    (f:Melody G ι)(p: Stuff G ι L)(_hF:Visible X ψ f p N c) (w:Rail G ι), w.length≤d→
    |P.expect (dollar s) (sing w (dollar s) * Error r f ψ p (dollar s))| ≤ s^(4*(r+d))*dollar s^r*C:=by
    obtain ⟨z,hz,h⟩:= promise Y hψ r c hc
    let y:= c+Visible.capΨ ψ X.Q r; let t:= y*2^d*(↑(N+d):ℝ)
    have ht:0≤y:=add_nonneg hc (Visible.cap_nn _ _ _ Y.thick.1.le)
    refine ⟨z+t,(by unfold t; positivity),?_⟩
    filter_upwards [h,residents X,willing Y,eventually_ge_atTop (1:ℝ),ruin_below (r+d)] with s hh he hU hw hr S ι k T _ _ _ P hP f p hF w hW
    let J:= hF.stamp.choose ∪ bundle w; let V: Set (Sky G ι) := {x| crisp (fare s) J x}
    let g:= dollar s; have hg:0<g:=dollar_pos _; have hx : 0<s:= lt_of_lt_of_le zero_lt_one hw; have h₁:g≤1:= dollar_bound hx.le
    let D:= (↑(N+d):ℝ)
    have hD:J.card≤N+d:= (card_union_le ..).trans (Nat.add_le_add (hF.stamp.choose_spec.1) ((bundle_cap w).trans hW))
    let B := sing w g*Error r f ψ p g
    let x:=s^4; have hp:1≤x:=one_le_pow₀ hw
    refine le_trans (patch_cost hP hU (f:=B) ((havenreal (sing_cont ..)).mul (literacy hP hF hU r)) V (crisp_open ..).measurableSet (Q:= x^d*(z*x^r*g^r)) (Q':=(2/g)^d*y) (by unfold x; positivity) (by positivity) ?_ ?_ (budget:=D*ruin s) ?_) ?_
    · intro u (ha:crisp (fare s) J u); unfold B; rw [Pi.mul_apply,abs_mul]; refine mul_le_mul (sing_area _ _ d hW hp (fun i hi=> ceiling _ _ _ _ hg ?_)) (hh ι f p N hF u (crisp_negligible _ _ le_rfl (subset_union_left) ha)) (abs_nonneg _) (by unfold x; positivity)
      exact (ha i.1 (mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,hi,rfl⟩)))).le
    · intro u _; unfold B; rw [Pi.mul_apply,abs_mul]; exact mul_le_mul (sing_price u hg h₁ hW) (hF.cash Y hU hg h₁ u) (abs_nonneg _) (by positivity)
    · have hr:= he S ι k T _ _ _ P hP hU J; have hO:0 < P.pot (dollar s):=pot_pos hP hU; have hR:0≤ruin s:=Real.exp_pos _|>.le; refine hr.trans ?_; gcongr; exact Nat.cast_le.mpr hD
    have h₂ : 1≤s^(4*(r+d)):=one_le_pow₀ hw
    let b:= (2/g)^d*y; have hb:0≤b:=by unfold b; positivity
    have h : D * ruin s*b ≤ g^r*t:=by
        refine le_trans (b:=D * g^(r+d) * b) ?_ ?_
        · gcongr
        unfold b t D; rw [div_pow,pow_add]; apply le_of_eq; field_simp
    rw [show x^d*(z*x^r*g^r)= s^(4*(r+d))*dollar s^r*z by rw [pow_mul,pow_add]; change x^d*(z*x^r*g^r)=x^r*x^d*g^r*z; ring, mul_add _ z t]
    apply add_le_add (le_refl _) (h.trans ?_); rw [mul_assoc]; exact le_mul_of_one_le_left (by unfold t; positivity) h₂
end Error
end YM.RGComparison.Core16.Lumen
