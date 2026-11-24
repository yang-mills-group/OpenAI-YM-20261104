import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Coffer
/-!
 # Upgrade the arboretum to super-polynomial tail support estimates

 At this point Utopia & by-L thresholds not paid. `apprentice` buys the
 ACTUAL covariance $ChainIndex$ record polynomial small to WILL after
 reserving its exponent as long path. This participates in Captain.log.
 Legitimately beyond Section T:VSTEP budgets. Distinguish E letters not
 incurring this fare. Rather than rerunning HULK roof gaussian convergence
 proofs with stronger requirements, graft it into its Eager estimate
 AFTER paying the requisite growth. Other letters continue paying ordinary
 estimates, including old K, Short Window & Tenn. Alarm extra separate.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Height
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open ConnectedActivityE6.Blaze
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Silica Silica.Clutch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {R : Rep G f}
variable {a W t x v : ℝ} {j n k : ℕ}

lemma aqua {ι:Type*}{f g : ι→ℝ}{X : ι→ Support c}{e : ι→ℕ}{B h:ℝ}
    (p:Sales n h B X f e a) (q:Sales n h B X g e W) : Sales n h B X (f+g) e (a+W):= by
   refine ⟨fun i=>add_nonneg (p.nonneg i) (q.nonneg i),fun i=>?_⟩
   convert budget_plus (p.hit i) (q.hit i) using 1; ext j; by_cases hx:i∈ X j <;> simp [hx,Reserves.tariff,add_mul]

lemma nil {ι:Type*}{X:ι→ Support c}{e:ι→ℕ}{v t : ℝ}: Sales n v t X (fun _=>0) e 0 := by
  refine ⟨fun i=> le_rfl,fun i=>?_⟩; simp [Reserves.tariff,SumBudget]

def bonus (q:ℕ) (c f: Side): LogIndex c f→ ℕ := Sum.elim (fun _=>0) (Sum.elim (fun _=>0) (fun _=>q))
lemma apprentice (P:Teller G)(Q:ConnectedActivityE6.Target G P)(t:ℝ)(ht:-(1/2:ℝ)<t)(he:t<0):∃ m:ℕ, ∀ L:Side,m≤L.val→ ∀ D:Patch,D.Branches P.bind G → ∀ (k i:ℕ)(χ:Chi)(W:ℝ)(o:Target.Order G W)(v w:ℝ→ℝ),
    Rate G L (-(1/2)) v → (∀ᶠ x in atTop,0≤ v x) → Rate G L (-(1/2)) w → ∃ A C, Rate G L 0 A ∧ Rate G L t C ∧ (∀ x,1≤A x) ∧
    ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), Works P L x S T → S.patch=D → Stamp T →
      Tent P L x o.K o.eta o.gap o.ample o.indexPay T → ShellAccess S G x W o.K o.γ → ∀ (R:Rep G f), Intake P T x R →
       ∃ U y, Eager Q o x (A x) i (v x) (w x) (C x) χ T R U y ∧ Sales (radiusB x) Q.relative Q.ε (roadway T R (radiusB x) Q.halo) (fun p=> grow G L x ^ bonus k c f p * y p) (exCharge T R) (C x):=by
  obtain ⟨m,hA⟩:= Clutch.pay_busy P Q ht he
  refine ⟨m,fun L hL D hD k i χ W o v w hv hv' hw=>?_⟩
  obtain ⟨A,C,h0,hT,hX,H⟩ := hA L hL D hD i χ W o v w hv hv' hw
  let p := t-3/8*k; have hp : p<0 := lt_of_le_of_lt (sub_le_self t (by positivity)) he
  have hQ:0≤Q.relative:=by unfold ConnectedActivityE6.Target.relative; linarith only [Q.usable,Q.bound,Q.pos]
  obtain ⟨J,hJ,Ha⟩:= Clutch.waits P L D hD o.K o.γ W o.a χ i hv hv' hw o.indexPay o.f p Q.relative Q.ε hp hQ Q.halo
    (le_trans (by norm_num : 4≤500) Q.buys)
  obtain ⟨u,hu,h_Ψ⟩:= Brush.expands i
  let w (x:ℝ):=grow G L x; let B(x):=w x^k * (u * J x); let ℓ(x):=C x + B x
  have hb : Rate G L t B:= ((Rate.power (G:=G) (L:=L) (a:=3/8)).pow k |>.mul (hJ.mul_left u)).weaken (le_of_eq (by unfold p; ring))
  refine ⟨A,ℓ,h0,hT.add hb,hX,?_ ⟩
  filter_upwards [H,Ha,hJ.below hp 1 zero_lt_one,(Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hx ha hy hz c f S T hT h hΩ he K R hR -- he rebind
  obtain ⟨z,y,hE⟩:= hx c f S T hT h hΩ he K R hR
  obtain ⟨Z,hZ,hP⟩:= ha c f S T h hT K he
  let a:LogIndex c f→ℝ:= Sum.elim (fun i=> y (.inl i)) (Sum.elim (fun i=> y (.inr (.inl i))) (fun j=> u*Z j))
  have hm:1≤w x:= Real.one_le_rpow hz (by norm_num)
  have hXb:0≤ B x:= mul_nonneg (pow_nonneg (zero_le_one.trans hm) _) (mul_nonneg hu (budget_nonneg (hZ.hit 0)))
  have hU:= boost_price (boost_price hZ hu) (pow_nonneg (zero_le_one.trans hm) k)
  let M:LogIndex c f→ℝ:= Sum.elim (fun _=>0) (Sum.elim (fun _=>0) (fun i=> w x^k*(u*Z i)))
  have hM:Sales (radiusB x) Q.relative Q.ε (roadway T R (radiusB x) Q.halo) M (exCharge T R) (B x):=by
    let he:= Sales.together (Bright.nil (X:= Raw.space T Q.halo (radiusB x) R) (e:=Raw.extra T R)) (Sales.together (Bright.nil (X:= Coat.sleeve S (radiusB x) Q.halo) (e:=fun _=>0)) hU)
    rw [zero_add,zero_add] at he; exact he
  have heq:= aqua hE.hair hM
  have hh : Sales (radiusB x) Q.relative Q.ε (roadway T R (radiusB x) Q.halo) (fun p=> w x^bonus k c f p*a p) (exCharge T R) (ℓ x) := by
    refine (one_mul (ℓ x)) ▸ (heq.shift (A:=1) zero_le_one (z:=fun p=> w x^bonus k c f p*a p) (fun h=>?_) (fun i=>?_))
    · rcases h with i|i|i <;> simp only [a,bonus, Sum.elim,pow_zero,one_mul]
      · exact hE.hair.nonneg _
      · exact hE.hair.nonneg _
      exact hM.nonneg (.inr (.inr i))
    rcases i with i|i|i <;> simp only [Pi.add_apply,one_mul,a,M,bonus,Sum.elim,pow_zero,add_zero] <;> try rfl
    exact le_add_of_nonneg_left (hE.hair.nonneg _)
  refine ⟨z,a,⟨hE.first.raise (le_add_of_nonneg_right hXb), Raw.store_price _ hh hm,?_⟩,hh⟩
  intro E _ _ _ F X U d u' b f' hh hk hχ hY hr Hc k
  obtain ⟨hhL,hK⟩:= hE.stamina E F X U d u' b f' hh hk hχ hY hr Hc k
  refine ⟨fun j=> ?_,hK⟩
  rcases j with i'|i'|j
  · exact hhL _ -- infer
  · exact hhL _
  have hg(v:Alphabet c f):1≤twigs R T X.B Q.halo v := le_add_of_nonneg_right (add_nonneg (Nat.cast_nonneg _) (show 0 ≤ lengths T R v from Nat.cast_nonneg _))
  have hx := h_Ψ E _ _ _ _ (hP E F X R U d u' b f' hh hχ hk hY hr Hc hR j) ((hZ.atom hQ Q.usable.le j ?_).trans ((le_abs_self _).trans hy)) -- syntax
  exact hx.climb le_rfl (one_le_mul_of_one_le_of_one_le (hX x) (hg _))
  exact Coat.exChart S T R (radiusB x) Q.halo (.inr (.inr j))
end YM.Juniper.Bright
