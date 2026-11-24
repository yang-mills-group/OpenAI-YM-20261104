import YM.MS.ScaleForest.Degrees
/-!
# Meridian: pole substitution inside MULTI-pin integrals

Vertical and currency-preserving distribution theorems. Needed to see that
all branch *subtractions* give genuine integrals, including when the
root UV integration could have been sensitive to the polar part. This part
on the dimension germ uses no setting IR scale or external momenta to zero
anywhere. Does not assert safety of accidentally taking a `limUnder` on a
part with poles, or of interchanging e.g. the z-limit with deciding the
term to integrate. Transfer estimates to terms with poles via `taper`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I : Type} {X Y F H : Curtain G I} {l : List (Curtain G I)} {m n : ℕ} {R T : ℝ}
   {p q : ℤ} {Z : Curtain G I → Prop}

def Mercurial (Z:Curtain G I→ Prop) (X:Curtain G I) (n:ℕ) : Prop:= ∃ Y, Iris (taper n X) Y∧ Z Y
def Visits (X:Curtain G I) : Prop:= ∀ᶠ z in dotty, ∀ s t, Form0 false (X z s t)
def Fluxible (X:Curtain G I): Prop:= ∀ᶠ z in dotty, ∀ s t, Gather (velocity X z t s) 0
lemma visit_plus (h:Visits X)(he:Visits Y): Visits (X+Y) := by filter_upwards [h,he] with z hz hZ s x; exact (hz s x).add (hZ s x)
lemma visit_zero : Visits (0:Curtain G I) := Eventually.of_forall fun _ _ _=> Form0.zero
lemma visitSum (h:∀ i∈l,Visits i): Visits l.sum := by induction l with| nil=> exact visit_zero| cons i l ih=> exact visit_plus (h i (by simp)) (ih (fun i hi=> h i (List.mem_cons_of_mem _ hi)))
lemma fluxible_plus (h:Fluxible X)(he:Fluxible Y): Fluxible (X+Y) := by filter_upwards [h,he] with z hz hZ s x; intro m l; simp_rw [velocity,Pi.add_apply,← cert,map_add,Pi.add_apply]; exact (hz s x m l).add (hZ s x m l)
lemma fluxible_zero : Fluxible (0:Curtain G I) := by refine Eventually.of_forall fun i s t a l=>?_ ; simp_rw [velocity,Pi.zero_apply,← cert,map_zero,Pi.zero_apply]; exact integrable_zero ..
lemma fluxibleSum (h:∀ i∈l,Fluxible i): Fluxible l.sum := by induction l with| nil=> exact fluxible_zero| cons i l ih=> exact fluxible_plus (h i (by simp)) (ih (fun i hi=> h i (List.mem_cons_of_mem _ hi)))
lemma Mercurial.tide (h:Mercurial Z X n) (hx:∀ F, Z F→Visits F) : Visits X := by
   obtain ⟨Y,h,hY⟩:= h; filter_upwards [ h, hx Y hY, dotty_non] with z hz hv hZ s x; obtain he:=hv s x; rw [ ← hz ] at he; convert! he.smul (z^n)⁻¹ using 1; unfold taper; rw [ Pi.smul_apply, Pi.smul_apply, inv_smul_smul₀ (pow_ne_zero n hZ) ]
lemma Mercurial.quo (h:Mercurial Z X n)(hx:∀ F,Z F→Fluxible F) : Fluxible X := by
   obtain ⟨Y,h,hY⟩:= h; filter_upwards [ h, hx Y hY, dotty_non] with z hz hv hZ s x; intro m l; have he : X z=(z^n)⁻¹ • Y z:= by rw [← hz]; exact (inv_smul_smul₀ (pow_ne_zero n hZ) _).symm;
   simp_rw [velocity,he,Pi.smul_apply,← cert,map_smul,Pi.smul_apply]; exact (hv s x m l).const_mul _
lemma Mercurial.maps (h:Mercurial Z X n) {A:Curtain G I→ Prop} (he:∀ Y,Z Y→ A Y): Mercurial A X n := by obtain ⟨Y,h,hY⟩:= h; exact ⟨ _,h, he Y hY⟩

-- unweighted estimate guard statement
section
variable [TopologicalSpace I]
lemma wide_visit (h : Waves R p X) (he:Enough R): Visits X:= by filter_upwards [dotty_bill he.1] with z hZ s t; exact h.forms _ hZ s t
lemma Crossing.possible (h:Crossing X p): Visits X ∧ Fluxible X := by
   obtain ⟨R,hR,hT,hX⟩:= h (1/2) (by norm_num) (by norm_num); refine ⟨ wide_visit hT hR, ?_⟩; filter_upwards [dotty_bill hR.1] with z hz s t; exact vertical_gather s t (hX 1) hT zero_lt_one (by norm_num) (⟨z,hz⟩:disc R)
lemma Crossing.four (h:Crossing X p) (s:ℝ)(t:I) : Gather (velocity X 0 t s) 0:= by obtain ⟨ R,hR,hT,hX⟩:= h (1/2) (by norm_num) (by norm_num); exact vertical_gather _ _ (hX 1) hT zero_lt_one (by norm_num) ⟨0,hR.top⟩
lemma paceVisits (h : Paces X p) : Visits X := by obtain ⟨R,hR,hT,u,H⟩:=h (1/2) (by norm_num) (by norm_num); exact wide_visit hT hR
lemma hoverVisits (h : Hover X p): Visits X:= by obtain ⟨R,hR,hT,hX⟩:= h 1 zero_lt_one; exact wide_visit hT hR

-- assert Mer integrability on axes & clock. absolute-time version for user.
lemma m_quot_limit (h:Mercurial (fun F=> Crossing F p) X n) : ∀ᶠ z in dotty, ∀ s x,
    Gather (fun t=> backing 0 X z t x) s ∧ Shine.Wind (fun a:ℝ=> fun m w=> ∫ t in a..s, backing 0 X z t x m w) atBot
      (backing 0 (vertical X) z s x) := by
   obtain ⟨Y,hT,hY⟩:= h; obtain ⟨R,hR,hξ,hH⟩:= hY (1/2) (by norm_num) (by norm_num); filter_upwards [hT,dotty_non,dotty_bill hR.1] with z hZ he hP s x; have hv : X z=(z^n)⁻¹ • Y z:= by rw [←hZ]; exact ( inv_smul_smul₀ (pow_ne_zero n he) _).symm;
   have hF: Gather (fun t=> backing 0 X z t x) s:= by
      intro m w; simp_rw [backing,hv,Pi.smul_apply,← cert,map_smul,Pi.smul_apply]; exact (funded s x hξ (hH 1) zero_lt_one (by norm_num) hP m w).const_mul _
   rw [backingVert]; exact ⟨hF,fun m w=> intervalIntegral_tendsto_integral_Iic _ (hF m w) tendsto_id⟩
end

-- pointwise actions enough for Iris. time and mass params untouched. cut gluing respects Laurent z.
lemma close_delivery (h:Iris X Y)(K:LineRule G)(μ:ℝ): Iris (Ufor K μ X) (Ufor K μ Y) := by filter_upwards [h] with z hz; funext s p; unfold Ufor; rw [hz]
lemma pin_delivery (h:Iris X Y)(he:Iris F H)(K:LineRule G)(μ:ℝ)(A:I→QP): Iris (Pfor K μ X F A) (Pfor K μ Y H A) := by filter_upwards [h,he] with z hz ht; funext s p; unfold Pfor; rw [hz,ht]
lemma bridge_delivery (h:Iris X Y)(he:Iris F H)(K:LineRule G): Iris (Bfor K X F) (Bfor K Y H) := by filter_upwards [h,he] with z hz ht; funext s p; unfold Bfor; rw [hz,ht]
lemma recoil (h:Iris X Y): Iris (vertical X) (vertical Y) := by filter_upwards [h] with z hz; funext s x; unfold vertical mend velocity; rw [hz]

lemma keyBarrier {z:ℂ}(hX:∀ s t, Form0 false (X z s t))(K:LineRule G)(μ:ℝ)(m:ℕ): taper m (Ufor K μ X) z=Ufor K μ (taper m X) z := by
   funext s x; simp_rw [ taper,Ufor, closeG_eq, Pi.smul_apply ]; rw [ scaleR (K.ok.forms false) (hX s x) ]; rw [Ufor, closeG_eq, smul_comm]
lemma keyBridge (K:LineRule G)(m n:ℕ): taper (m+n) (Bfor K X Y)=Bfor K (taper m X) (taper n Y) := by
   funext z s x; simp_rw [ taper,Bfor, bridgeG_eq K.ok.rev, ← schedule, Pi.smul_apply,pow_add,map_smul, LinearMap.smul_apply, mul_smul ]; rw [Bfor,bridgeG_eq K.ok.rev, ← schedule,smul_comm]
lemma weave_m (x:ℂ)(F H:Mob G): weave (x • F) H= x • weave F H:= funext fun _=> map_smul ((product (field parity)).flip (H _)) x (F _)
lemma weave_r (x:ℂ)(F H:Mob G): weave F (x • H)= x • weave F H:= funext fun _=> map_smul (product (field parity) (F _)) x (H _)
lemma pin_smul (K: Rip G) {χ:ℂ} {F H:Mob G} (hk:Knot false K)(hp:closedF K false)(hr: reverseF K)(hX:Form0 false F)(hH:Form0 false H)(he:χ∈Town) (μ:ℝ)(A:QP)(x y:ℂ):
    pinned K χ μ A (x • F) (y • H)= (x*y) • pinned K χ μ A F H := by
   obtain hV:= form_rephase hX A; rw [ placedEq hk hp hr (hX.smul x) (hH.smul y) he, placedEq hk hp hr hX hH he, map_smul ];
   unfold sweptRef; rw [weave_m,weave_r, ← mul_smul, scaleR hk (form_weave hV hH), scaleR hk hV, scaleR hk hH];
   simp_rw [ weave_m,weave_r,← mul_smul ]; rw [← smul_sub,← smul_sub,smul_comm]; exact (mul_smul ..).symm
lemma keyPin {z:ℂ}(hX:∀ s t,Form0 false (X z s t))(hY:∀ s t, Form0 false (Y z s t))(h:z∈Town)(A:I→QP)(K:LineRule G)(μ:ℝ)(m n:ℕ): taper (m+n) (Pfor K μ X Y A) z=Pfor K μ (taper m X) (taper n Y) A z:= by
   funext s t; simp_rw [taper,Pfor,Pi.smul_apply,pin_smul _ (K.ok.forms false) K.ok.even K.ok.rev (hX s t) (hY s t) h,pow_add]; rfl
lemma keyV (F:Curtain G I) (m:ℕ): taper m (vertical F)=vertical (taper m F):= by
   funext z s x n l; simp_rw [taper,vertical,mend,velocity,Pi.smul_apply,← cert,map_smul,Pi.smul_apply,integral_smul]; rfl

variable [TopologicalSpace I] [FirstCountableTopology I]
omit [FirstCountableTopology I] in
lemma bridgeMerc (hx:Mercurial (fun X=> Hover X p) X m)(hf:Mercurial (fun X=> MultiFuel X q) F n)(K : LineRule G) : Mercurial (fun u=> Crossing u (p+q-2)) (Bfor K X F) (m+n):= by
   obtain ⟨Y,h,hY⟩:= hx; obtain ⟨W,ht,hW⟩:= hf; refine ⟨ Bfor K Y W,?_,fueledB K hY hW⟩; rw [keyBridge]; exact bridge_delivery h ht K
lemma loopMerc (hx:Mercurial (fun X=> MultiFuel X p) X m)(K:LineRule G)(μ:ℝ): Mercurial (fun F=> Crossing F (p-2)) (Ufor K μ X) m:= by
   have he:= hx.tide fun _ h=> paceVisits (paceFuel h); obtain ⟨V,h,hV⟩:= hx; refine ⟨ Ufor K μ V, EventuallyEq.trans ?_ (close_delivery h K μ), fueledU K μ hV⟩;
   filter_upwards [he] with z hz; exact keyBarrier hz K μ m
lemma pinMerc (hx:Mercurial (fun X=> Paces X p) X m)(hf:Mercurial (fun X=> Paces X q) F n)(K : LineRule G)(μ:ℝ){A:I→QP}(hp:AdmittedGap A) : Mercurial (fun u=> Crossing u (p+q-2)) (Pfor K μ X F A) (m+n):= by
   obtain hu:= hx.tide (fun _ h=> paceVisits h); obtain hv:= hf.tide (fun _ h=> paceVisits h); obtain ⟨Y,h,hY⟩:=hx; obtain ⟨Z,ht,hZ⟩:=hf; refine ⟨ Pfor K μ Y Z A, EventuallyEq.trans ?_ (pin_delivery h ht K μ A), fueledP K μ hp hY hZ⟩;
   filter_upwards [hu,hv,Shine.high0] with z he hh hz; exact keyPin he hh hz A K μ m n
lemma migrate_m (hx:Mercurial (fun F=> Crossing F p) X m) : Mercurial (fun F=> MultiFuel F p ∧ Frontier F) (vertical X) m:= by
   obtain ⟨V,h,hV⟩:=hx; refine ⟨ vertical V,?_,paidVertical hV, Frontier.drivePast hV⟩; rw [keyV]; exact recoil h
end YM.MS.ScaleForest
