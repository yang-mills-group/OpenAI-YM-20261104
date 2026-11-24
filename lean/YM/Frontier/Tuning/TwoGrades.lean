import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Rush
/-! A simultaneous Rush receipt before composing exp and normalization. Strengthening so
 not lacking radius for forced inherits. See Clutch.rushPrices, hearthGrades. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Silica
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a A α β γ d η σ W s b μ r p q v : ℝ} {j n l : ℕ} {Q : YM.ConnectedActivityE6.Target G P}
variable {V : E→ Config G c} {w : E → Directions G f} {u : E→ Air f G}
namespace Clutch

open PhysicalNext.Repeat.Height
private lemma anglesK (P : Teller G) (L:Side) (l : ℕ) {b η:ℝ}(hη:0<η)(hA:0≤b)(he:4*η<P.top.supportExponent)(hj:8*η<P.top.width)(hl:8*η<P.below.width) (hp: L.val ≥ ((Raw.inherit_multi G P l (a:=b) hη hA he hj hl)).choose) (j:ℕ)(χ:Chi)(a r:ℝ){f g:ℝ→ℝ}(h:Rate G L (-(1/2)) f)(hG:Rate G L (-(1/2)) g): ∃ B, Rate G L 0 B ∧ (∀ x,0≤B x) ∧ ∀ᶠ x in atTop, ∀ (c f':Side) (S:StepData c f') (T : Tube G S) (R : Rep G f'),
      S.patch.L=L → Intake P T x R → ∃ (w : ℕ → ℝ), let M:=radiusB x
      Sales M b η (forcedFoot S.ratio l M R) (fun i=>grow G L x^2*w i) (forcedExtra R) (betaF G x L ^ r) ∧
        ∀ (F : Forest S.ratio) (X : Coat T F) (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Config G f')
        (V:E→ Config G c) (Y:E→ Directions G f') (p:E) (W : E→ Air f' G) (t : Air f' G), X.x=x → X.χ=χ → Mode V p j (f x) →
        Clutch X t a R.beta (g x) p j V Y W →
          ∀ i, Brush j (w i) (B x*(coverNumber M (forcedFoot S.ratio l M R i)+(forcedExtra R i:ℝ)))
            (fun y=> sheath (vary X (V y)) a R (Y y) U i) p := by
  have hv := (Raw.inherit_multi G P l (a:=b) hη hA he hj hl).choose_spec L hp 0 (by norm_num) (r-2)
  obtain ⟨Q,hQ,hV,hT⟩:= central G L χ j hG (2*a)
  let d x:=grow G L x^2*betaF G x L^(r-2)
  have hD : ∀ᶠ x in atTop, d x ≤ betaF G x L^r:= (((Rate.power (G:=G) (L:=L) (a:=3/8)).pow 2).mul (Rate.power (a:=r-2)) r (by norm_num;linarith)).mono fun x h=> (le_abs_self _).trans h
  refine ⟨Q,hQ,hV,?_⟩
  filter_upwards [hD,hT,hv] with x hd hx hv c f S T R hs hR
  obtain ⟨_,_,_,w,hw,hW⟩:=hv c f S T R hs hR
  refine ⟨w,((Raw.boost_price hW (sq_nonneg _)).raise hd),?_⟩
  intro F X E _ _ U V Y y Z t hX hχ hv hh i
  let O:=forcedFoot S.ratio 0 X.B R i; let O':=forcedFoot S.ratio l X.B R i
  have hB:= hx _ _ S T F X hX hχ hs (show 0<2*a*X.t by rw [mul_assoc]; exact mul_pos (by norm_num) hh.pulse) E t a R.beta y V Y Z hh O O' (Corona.halo_mono (by omega) (Subset.refl _))
  have hf:=((Brush.certified (d:=0) le_rfl _).climb (hw i U) le_rfl).paints hB
  rw [show radiusB x=X.B from congr_arg radiusB hX.symm]; apply hf.climb (mul_one ..).le; exact ((zero_add _).trans_le (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Nat.cast_nonneg _)) (hV _)))

structure StrongEager (Q : YM.ConnectedActivityE6.Target G P) (o : Target.Order G W) (X a Z : ℝ) (i : ℕ) (v w : ℝ) (C : ℝ)
    (χ : Chi) (T : Tube G S) (R : Rep G f) (k : ℕ→ℝ) (y : LogIndex c f → ℝ) : Prop where
  along : Sales (radiusB X) Q.relative Q.ε (Raw.forcedFoot S.ratio Q.halo (radiusB X) R) (fun i=> Z^2*k i) (Raw.forcedExtra R) C
  logbook : Sales (radiusB X) Q.relative Q.ε (roadway T R (radiusB X) Q.halo) (fun i=>Z^teeth c f i*y i) (exCharge T R) C
  stamina : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F : Forest S.ratio) (Y : Coat T F)
      (U:E→ Config G c) (u:E→ Directions G f) (z : E→ Air f G) (x:E) (t:Air f G), Y.x=X → Y.width=o.K → Y.χ=χ → Y.manifest →
      Mode U x i v → Clutch Y t o.a R.beta w x i U u z →
        (∀ p, Brush i (y p) (a*twigs R T Y.B Q.halo (.inr (.inl p)))
          (fun v=> logMoment (vary Y (U v)) o.a R Q.table (u v) (Y.input (worldZ Y R.beta t)) (z v) p) x) ∧
        (∀ p, Brush i (k p) (a*twigs R T Y.B Q.halo (.inl p))
          (fun v=> sheath (vary Y (U v)) o.a R (u v) (Y.input (worldZ Y R.beta t)) p) x)
-- Port of stamina on concrete weights with price of all optional leg extras.
lemma strongRush (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) {t : ℝ} (h : -(1/2:ℝ)<t) (ht : t<0) :
    ∃ n : ℕ, ∀ (L:Side), n≤L.val → ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ) (o:Target.Order G W) (v w : ℝ→ℝ),
    Rate G L (-(1/2)) v → (∀ᶠ x in atTop,0≤ v x) → Rate G L (-(1/2)) w → ∃ A C, Rate G L 0 A ∧ Rate G L t C ∧ (∀ x,1≤A x) ∧
    ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), Works P L x S T → S.patch=D → Stamp T →
      Tent P L x o.K o.eta o.gap o.ample o.indexPay T → ShellAccess S G x W o.K o.γ → ∀ (R:Rep G f), Intake P T x R →
      ∃ V y, StrongEager Q o x (A x) (grow G L x) i (v x) (w x) (C x) χ T R V y := by
  let a:= Q.relative; have hv : 0≤a := by unfold a Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  obtain ⟨N,hN⟩:= hearthGrades P Q.halo Q.usable Q.grants.1 Q.grants.2.1 Q.grants.2.2 hv
  refine ⟨N+(Raw.inherit_multi G P Q.halo (a:=Q.relative) Q.usable hv Q.grants.1 Q.grants.2.1 Q.grants.2.2).choose,fun L hL D hd i χ W o v w hx H hV=>?_⟩
  obtain ⟨B,hB,hFb,hP⟩:= hN L (by omega) i χ o.a t h v w hx hV
  obtain ⟨Z,hZ,hFZ,hK0⟩:=anglesK P L Q.halo (b:=Q.relative) Q.usable hv Q.grants.1 Q.grants.2.1 Q.grants.2.2 (by omega) i χ o.a t hx hV
  obtain ⟨A,hA,hG⟩:= Clutch.waits P L D hd o.K o.γ W o.a χ i hx H hV o.indexPay o.f (-2) Q.relative Q.ε (by norm_num) hv Q.halo
    ((by have h:=Q.buys; omega))
  obtain ⟨C,U,b,hC,hU,hY,hQ⟩:= Clutch.flick P L D hd o.K o.γ W o.a χ i hx H hV o.indexPay o.f Q.relative Q.ε hv Q.halo
    (by have h:=Q.buys; omega) Q.table_exists
  let V x := B x+(1+U x)+Z x; have h' x:1≤V x := by unfold V; linarith [hFb x,hY x,hFZ x]
  have hs:= (hC.weaken h.le).add (show Rate G L t (fun x=>grow G L x^2*A x) from (((Rate.power (G:=G) (L:=L) (a:=3/8)).pow 2).mul hA).weaken (by push_cast; linarith only [h])); have hT:= (Rate.power (G:=G) (a:=t)).add hs
  refine ⟨V,_,(hB.add ((Rate.const 1).add hU)).add hZ,hT,h',?_⟩
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,hP,hG,hQ,hK0] with x hg hp hZ hA h c f S T H hS hF' hv' hm R' hRZ
  obtain ⟨u,k,hu,hk,hW⟩ := hp _ _ S T R' H.length_eq hRZ
  obtain ⟨y,he,hQ⟩:=hZ _ _ S T hS H hm hv'
  obtain ⟨hX,hY'⟩:= hA _ _ S T hS H hF' hv' hm
  obtain ⟨k',hk',hL'⟩:= h _ _ S T R' H.length_eq hRZ
  let Y := Sum.elim u (Sum.elim (fun (_:Miniature c f)=>b x) y)
  let s:= betaF G x L ^ t
  have hh : Sales (radiusB x) Q.relative Q.ε (roadway T R' (radiusB x) Q.halo) (fun i=>grow G L x^teeth c f i* Y i) (exCharge T R') (s+(C x+grow G L x^2*A x)) := by
    have ht_or:1≤ grow G L x:= Real.one_le_rpow hg (by norm_num)
    have hl := hu.together (hX.together (boost_price he (pow_nonneg (zero_le_one.trans ht_or) 2)))
    convert hl using 1
    · rfl
    · funext i; rcases i with i|i|i <;> simp only [Y, Sum.elim,teeth,pow_zero,one_mul]
    · rfl
  have ht_or:1≤ grow G L x:= Real.one_le_rpow hg (by norm_num)
  refine ⟨k',Y,hk'.raise (le_add_of_nonneg_right (add_nonneg (budget_nonneg (hX.hit 0)) (mul_nonneg (sq_nonneg _) (budget_nonneg (he.hit 0))))),hh,?_⟩
  intro E _ _ _ F Z v u z x' V' hΖ hK hχ hM H'V ht
  let I:=Z.input (worldZ Z R'.beta V'); let f j:=twigs R' T Z.B Q.halo j
  have hBF:= hW F Z E I v u x' z V' hΖ hχ H'V ht
  have hF i:1≤f i := le_add_of_nonneg_right (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hj k (p q : ℕ) (h : F = F) (he : f k=1+(p+(q:ℝ))) : B x*(p+(q:ℝ)) ≤ V x*f k := by
    rw [he]; refine mul_le_mul ((le_add_of_nonneg_right (add_nonneg zero_le_one (hY x))).trans (le_add_of_nonneg_right (hFZ x))) (le_add_of_nonneg_left zero_le_one)
      (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (zero_le_one.trans (h' _))
  let Δ p:= V x*f p
  have hz : radiusB x=Z.B := congr_arg _ hΖ.symm
  constructor
  · intro j
    rcases j with j|j|j
    · have hf:=hBF.1 j
      rw [hz] at hf; exact hf.climb le_rfl (hj _ _ _ rfl rfl)
    · have hp:= hY' E F Z R' v u z x' V' hΖ hχ hK hM H'V ht hRZ j
      apply hp.climb le_rfl
      unfold twigs lengths; simp only [Sum.elim,exCharge,Nat.cast_zero,add_zero]
      refine mul_le_mul_of_nonneg_right (le_trans (b:=1+U x) (le_add_of_nonneg_left zero_le_one) ((le_add_of_nonneg_left (hFb x)).trans (le_add_of_nonneg_right (hFZ x)))) (by positivity)
    exact (hQ E F Z R' v u z x' V' hΖ hχ hK hM H'V ht hRZ j).climb le_rfl (one_le_mul_of_one_le_of_one_le (h' _) (hF _))
  intro j; have hs:= hL' F Z E I v u x' z V' hΖ hχ H'V ht j
  rw [hz] at hs
  apply hs.climb le_rfl
  change _*(coverNumber Z.B _+(_ : ℕ) : ℝ) ≤ V x * f (.inl j)
  dsimp only [f,twigs,footprints,lengths,Sum.elim]
  refine mul_le_mul ?_ (le_add_of_nonneg_left zero_le_one) (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (zero_le_one.trans (h' _))
  apply le_add_of_nonneg_left (add_nonneg (hFb x) (add_nonneg zero_le_one (hY x)))
end Clutch
end YM.ConnectedActivityE6.Blaze.Silica
