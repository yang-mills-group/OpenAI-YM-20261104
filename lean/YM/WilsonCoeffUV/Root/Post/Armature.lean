import YM.WilsonCoeffUV.Root.Post.Slogan
/-! # Gate outputs of normalized column including being killed at order e=0 rank <l by horizon. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V E:Type*}{r h D l j e k a m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A X B C δ:ℝ}{I:Bulb G}

structure Wager (W:Tand I e r D)(F: Labels.Frame G h)(A B V S:ℝ)(d:ℕ): Prop where
    pose : Cork Bank.terrain 0 I.exitS (V/I.path.patch.L.val*A+S*W.x^d) (fanfare I.path W.P.P h W.Y e r)
    vale : Cork Bank.terrain 0 I.exitS (V/I.path.patch.L.val*A+S*W.x^d) (fanfare I.path W.P.Q h W.Z e r)
    visit : Cork Bank.terrain 0 I.exitS (V/I.path.patch.L.val*B+ S*W.x^d*(1+A)*W.σ) (fanfare I.path W.P.P h W.Y e r-fanfare I.path W.P.Q h W.Z e r)
    owe i: valence F i=r→ twain (S*W.x^d*(1+A)) W.σ (echoS F (fanfare I.path W.P.P h W.Y e r) i) (echoS F (fanfare I.path W.P.Q h W.Z e r) i)
    -- absolute bounds need independent of A
    fare i: valence F i=r→ ‖echoS F (fanfare I.path W.P.P h W.Y e r) i‖≤ S*W.x^d
    care i: valence F i=r→ ‖echoS F (fanfare I.path W.P.Q h W.Z e r) i‖≤ S*W.x^d
structure Rent (W:Tand I e r D)(Y: Single G D)(F: Labels.Frame G h)(A:ℝ) : Prop where
    stem: Stakes Y
    ask i j : lowerGrade i j e r → Twig 0 I.input A (Y i j)
    title (i:Alma F) :valence F i=r → ‖glean F Y e i‖≤ A
private lemma proof_ribbon (P:A≥0)(h:0≤ B)(u:0≤ C)(hx:1≤ X)(p:0≤ δ)(q:ℝ)(hq:0≤q)(t t':ℝ)(ht:0≤t)(a:ℝ)(hp:0≤a)(c:ℕ):
    let k:= c+1; let v:=X^k; let H:= (t+B)+a*(1+t)+C+q*B+q*t
    0≤H∧ t'+C*X + B*X^c≤ t'+ H*v ∧ -- here t' and replaced resonance terms, a unused
    (t' + C*(X*δ) + t*A*δ)+ B*X^c*δ ≤ t'+H*v*(1+A)*δ∧
    C*X+q*(B*X^c) ≤ H*v ∧C*(X*δ)+q*(t*A*δ)+q*(B*X^c*δ) ≤ H*v*(1+A)*δ:=by
    intro k v H; have hh: X ≤ v:= by unfold v k; rw [pow_succ]; exact le_mul_of_one_le_left (zero_le_one.trans hx) (one_le_pow₀ hx)
    have he:0≤v:=zero_le_one.trans (hx.trans hh); let U:=v*(1+A); have hg:X^c≤ v:= pow_le_pow_right₀ hx (by unfold k; omega)
    have ht' : v ≤ U:= le_mul_of_one_le_right he (by linarith)
    have ha:A ≤ U:=by
       apply le_trans _ (le_mul_of_one_le_left (show 0≤1+A by linarith) (hx.trans hh)); linarith
    have h₁: C+B≤ H:=by unfold H; nlinarith
    have h₂: C+t+B≤ H:=by unfold H; nlinarith
    have h₃: C+q*B ≤ H:=by unfold H; nlinarith
    have h₄: C+q*t+q*B ≤ H:=by unfold H; nlinarith
    refine ⟨(add_nonneg u h).trans h₁,?_,?_,?_,?_⟩
    · rw [add_assoc]; apply add_le_add_right; exact (add_le_add (mul_le_mul_of_nonneg_left hh u) (mul_le_mul_of_nonneg_left hg h)).trans (by rw [← add_mul]; exact mul_le_mul_of_nonneg_right h₁ he)
    · rw [show t'+C*(X*δ)+ t*A*δ+B* X^c*δ=t'+(C*X+t*A+B*X^c)*δ by ring]; apply add_le_add_right; apply mul_le_mul_of_nonneg_right _ p
      refine (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hh.trans ht') u) (mul_le_mul_of_nonneg_left ha ht)) (mul_le_mul_of_nonneg_left (hg.trans ht') h)).trans ?_; simp_rw [← add_mul]; rw [mul_assoc H]; exact mul_le_mul_of_nonneg_right h₂ (he.trans ht')
    · rw [← mul_assoc q]; refine (add_le_add (mul_le_mul_of_nonneg_left hh u) (mul_le_mul_of_nonneg_left hg (by positivity))).trans ?_; rw [← add_mul]; exact mul_le_mul_of_nonneg_right h₃ he
    rw [show C*(X*δ)+q*(t*A*δ)+_= (C*X+q*t*A+q*B*X^c)*δ from by ring]; apply mul_le_mul_of_nonneg_right _ p
    apply (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hh.trans ht') u) (mul_le_mul_of_nonneg_left ha (by positivity))) (mul_le_mul_of_nonneg_left (hg.trans ht') (by positivity))).trans; simp_rw [← add_mul]; rw [mul_assoc H]; exact mul_le_mul_of_nonneg_right h₄ (he.trans ht')

lemma armada (H:Hol G)(F:Frame G h)(e r:ℕ)(ht:h<D): ∃ d:ℕ,∀ T:Cloister G h,∃ S:ℝ,0≤ S∧∀ W:Tand T.lamp e r D,∀ (_g:Courant T W.P.P)(_q: Courant T W.P.Q), T.lamp.dues r→
    Rent W W.Y F W.x→Rent W W.Z F W.x→Rent W (W.Y-W.Z) F (W.x*W.σ)→∀ A B:ℝ, Twig 0 T.lamp.input A (W.Y e r)→Twig 0 T.lamp.input A (W.Z e r)→Twig 0 T.lamp.input B ((W.Y-W.Z) e r)→ Wager W F A B (velo H F ht T.lamp r) S d:=by
    obtain ⟨c,V⟩:= Fabric.resinH (G:=G) e r h D; refine ⟨c+1,fun T=>?_⟩
    let I:=T.lamp; let v:= velo H F ht I r; let L:=I.path.patch.L; let t:= (L.val:ℝ)^h *((r+1:ℕ)*I.path.D^r*Real.exp (8*I.s)*tiePay (Pick I.path) r (I.s-I.exitS))
    have hT:0≤t:=by unfold t; have h:=zero_le_one.trans I.path.bill_nn; have ht:=tie_nn (α:=Pick I.path) (sub_pos.mpr I.vio) r; positivity
    obtain ⟨A,hA,hh⟩:=V I; obtain ⟨B,hB,E⟩:=tower_gain F H T ht e r; obtain ⟨C,hC,R⟩:=paid_echo F I.exitS I.positive r D
    let S:=(t+A)+ (0:ℝ)*(1+t)+B+C*A+C*t; have hs:0≤S:=by unfold S; positivity
    refine ⟨S,hs,?_⟩; intro W g q z Y Z M p Q J K M'
    let x:=W.x; let θ:= W.σ; have hx:1≤ x:= W.P.rich; have hθ:0≤ θ:= W.P.θ; let d:= c+1
    let y:= hall I.path.patch h W.P.P.Q (W.Y e r); let y':=hall I.path.patch h W.P.Q.Q (W.Z e r); let y2:= hall I.path.patch h W.P.P.Q (W.Z e r)
    let τ' s:= v/L.val*s
    let a:= W.P.Υ.mono (I.outlet.trans I.path.holds.le); obtain ⟨h1,b⟩:= E _ g W.Y x p z (zero_le_one.trans hx) Y.stem (fun i v r=>Y.ask i r (Or.inl v)) Y.title a.oneP J
    obtain ⟨h2,t'⟩:= E _ q W.Z x p z (zero_le_one.trans hx) Z.stem (fun i v r=>Z.ask i r (Or.inl v)) Z.title a.otherP K
    obtain ⟨h3,u⟩:= E _ g (W.Y-W.Z) (x*θ) Q z (by positivity) M.stem (fun i v r=> M.ask i r (Or.inl v)) M.title a.oneP M'
    have hg: hall I.path.patch h W.P.P.Q ((W.Y-W.Z) e r)=y-y2:= hall_diff _ _ a.oneP _ _ J K I.anger I.ports h
    rw [hg] at h3 u
    have hb := hh W; let P:=carnival I.path W.P.P h W.Y e r+veering I.path W.P.P h W.Y e r; let P':=carnival I.path W.P.Q h W.Z e r+veering I.path W.P.Q h W.Z e r
    have hv' : fanfare I.path W.P.P h W.Y e r=y+P:= helmet_bows ..; have hw' : fanfare I.path W.P.Q h W.Z e r=y'+P':= helmet_bows ..
    have hw0 := proof_ribbon J.1 hA hB hx hθ C hC t (τ' p) hT 0 le_rfl c; have hw1:=proof_ribbon J.1 hA hB hx hθ C hC t (τ' Q) hT 0 le_rfl c
    have hK :Cork Bank.terrain 0 I.exitS _ (y2-y'):= stride (I:=I) W h K
    have hp: Shelf Bank.terrain 0 I.exitS (A*x^c) θ P P':=hb
    have hD: fanfare I.path W.P.P h W.Y e r-fanfare I.path W.P.Q h W.Z e r=(y-y2)+(y2-y')+(P-P'):=by rw [hv',hw']; abel
    have H0 : Cork Bank.terrain 0 I.exitS (τ' p+S*x^d) (fanfare I.path W.P.P h W.Y e r):= by rw [hv']; exact ((Cork.add h1 hp.wax).cost hw0.2.1)
    have H1 : Cork Bank.terrain 0 I.exitS (τ' p+S*x^d) (fanfare I.path W.P.Q h W.Z e r):= by rw [hw']; exact (Cork.cost (Cork.add h2 hp.wane) hw0.2.1)
    have ht0 (i:Alma F)(v: valence F i=r): ‖echoS F (fanfare I.path W.P.P h W.Y e r) i‖≤ S*x^d :=by
       rw [hv',echo_add i h1 hp.wax I.positive I.positive]; exact (norm_add_le ..).trans ((add_le_add (b.tell i (weigh_cap F i) v) (R i P _ hp.wax)).trans hw0.2.2.2.1)
    have ht1 (i:Alma F)(v: valence F i=r): ‖echoS F (fanfare I.path W.P.Q h W.Z e r) i‖≤ S*x^d :=by
       rw [hw',echo_add i h2 hp.wane I.positive I.positive]; exact (norm_add_le ..).trans ((add_le_add (t'.tell i (weigh_cap F i) v) (R i P' _ hp.wane)).trans hw0.2.2.2.1)
    refine ⟨H0,H1,?_ ,?_,ht0,ht1⟩
    · rw [hD]; exact ((Cork.add (Cork.add h3 hK) hp.toll).cost hw1.2.2.1)
    intro i v; have hp' : S*x^d≤ S*x^d*(1+p):= by have hz:= J.1; exact le_mul_of_one_le_right (by positivity) (by linarith)
    refine ⟨(ht0 i v).trans hp',(ht1 i v).trans hp',?_⟩
    rw [← echo_minus F i H0 H1 I.positive I.positive,hD, echo_add i (Cork.add h3 hK) hp.toll I.positive I.positive, echo_add i h3 hK I.positive I.positive]
    exact (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add (u.tell i (weigh_cap ..) v) (R i _ _ hK))) (R i _ _ hp.toll)).trans hw0.2.2.2.2)
end YM.WilsonCoeffUV.Cosmos
