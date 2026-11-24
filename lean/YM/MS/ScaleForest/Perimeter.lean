import YM.MS.ScaleForest.Triangle
/-!
# ODE evaluation method for placed sums

Specialize at retained length, only on self-standing already forest-summed
inputs. We prove diagram-by-diagram (here that means our `Planted` diagram
families). For evaluating a particular renormalized family or **D0** of a
regulated complement, it now suffices to compute its push-frame and solve
the linear scale ODE. This is different from just dropping the dimensional
regularization before doing the forest subtraction or the mer integral.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle XSpace XSpace.Chiral Cylinder Planted Quadratic
open scoped Topology ContDiff
namespace Planted
variable {G : Gauge} {I : Type} {m:ℕ} {b c:Bool}{R:ℝ}(μ: ℝ) {V W:Planted G I true}
    {X:Planted G I b} {Y:Planted G I c} {A:I→QP}

def absPush (X: Planted G I true) (s : ℝ) (i : I):= backing 0 (push μ X) 0 s i
def absNom (X: Planted G I b)(s:ℝ)(i:I):= backing 0 (resolve μ X) 0 s i
def absBulk (F:GraphSum G true 4) (s:ℝ)(i:I): Mob G:= backing (-4) (asLeaf F.instructions.renorm μ 0) 0 s i
variable (s:ℝ)(x:I)(l:Legs (Shore G m))
variable [TopologicalSpace I] [FirstCountableTopology I]
lemma pays (hp:V.Stand): Gather (fun t=> absPush μ V t x) s := by
    obtain ⟨R,hR,hT,hV⟩:= pushing μ V hp (1/2) (by norm_num) (by norm_num); exact funded s x hT (hV 1) zero_lt_one (by norm_num) hR.top

lemma abs_sc (hp:V.Stand) : Continuous (fun t=> absPush μ V t x m l) := by
    obtain ⟨R,hR,hT,hV⟩:= pushing μ V hp (1/2) (by norm_num) (by norm_num);
    let q(t:ℝ):Atlas I R:= (⟨0,hR.top⟩,t,x); exact (repaint (repaintPlow (V:=Prod.fst ∘ Prod.snd) (hT.sway) ((hV 1).nearby) 0 (by fun_prop)) q (by unfold q; fun_prop)) m l
omit [TopologicalSpace I] [FirstCountableTopology I] in
lemma deployed : absNom μ V s x=mend (fun t=> absPush μ V t x) s:= by unfold absNom; rw [rooting V μ,backingVert]; rfl
lemma Speed (h:V.Stand) : HasDerivAt (fun t=> absNom μ V t x m l) (absPush μ V s x m l) s:= by
   let f(t:ℝ):= absPush μ V t x m l; let F(t:ℝ):= absNom μ V t x m l;
   have hx (t:ℝ): F t=(∫ t in (0:ℝ)..t,f t)+F 0:= by
      apply sub_eq_iff_eq_add.mp; unfold F; rw [deployed μ t,deployed μ 0]; exact intervalIntegral.integral_Iic_sub_Iic (pays μ 0 x h m l) (pays μ t x h m l)
   obtain hc : Continuous f:= abs_sc μ x l h; change HasDerivAt (fun t=>F t) (f s) s; rw [show (fun t=>F t)=(fun t:ℝ=> (∫ t in (0:ℝ)..t,f t)+F 0) from funext hx]; exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).add_const _
omit [TopologicalSpace I] [FirstCountableTopology I] in
lemma StartZero : Tendsto (fun t:ℝ=> absNom μ V t x m l) atBot (𝓝 0) := by simp_rw [deployed,mend]; exact tendsto_integral_Iic_zero tendsto_id
lemma observer (X:Planted G I b)(ht:X.Stand): ∃ R,Enough R∧Waves R X.slots (resolve μ X):= by obtain ⟨R,hR,hT,hV⟩:= (offers μ X ht).2.1 (1/2) (by norm_num) (by norm_num); exact ⟨ R,hR,hT⟩
lemma observing (X:Planted G I b)(ht:X.Stand): Form0 false (absNom μ X s x) ∧ Goods X.slots (absNom μ X s x):= by obtain ⟨R,hR,hT⟩:= observer μ X ht; exact ⟨ fseed (hT.forms 0 hR.top s x) 0 s, need_rank.walk _ _ (hT.funds _ hR.top s x)⟩

variable (K:LineRule G)
lemma pushedC (h:V.Stand): absPush μ (U K V) s x= closeG (pulse 4 s K.half) 0 μ (absNom μ V s x):= by obtain ⟨R,hR,hT⟩:= observer μ V h; exact behind_u_for K hT hR.top s μ x 0
lemma pushedP (he:X.Stand) (ht:Y.Stand) : absPush μ (P K A X Y) s x = pinned (pulse 4 s K.half) 0 μ (A x) (absNom μ X s x) (absNom μ Y s x):= by
   obtain ⟨ R,hR,hT⟩:= observer μ X he; obtain ⟨r,hr,h⟩:= observer μ Y ht; exact behind_p_for K (hR.pair hr) (hT.shrink (min_le_left R r)) (h.shrink (min_le_right R r)) (hR.pair hr).top _ _ _
omit [TopologicalSpace I] [FirstCountableTopology I] in
lemma pushedB (F:GraphSum G true 4): absPush μ ( B K F V ) s x=bridgeG (pulse 4 s K.half) (absBulk μ F s x) (absNom μ V s x):= behind_b_for ..

omit [TopologicalSpace I] [FirstCountableTopology I] in
lemma initialBudget {p:ℕ}{X:Mob G} (ht:kPrice X): ruby ( Parade (classicalPage X) p μ s ) 0=plow (-(p:ℂ)) s X:= by
    have he : Parade (classicalPage X) p μ s = fun _=> plow (-(p:ℂ)) s X:= funext fun i=> by simp only [classicalPage,collapsed,page_sl,ew,cubic,gNat]; simp
    rw [he]; exact (chosen (n:=0) (show Lift _ _ from (Lift.stays (powder ht _ _)))).symm
omit [TopologicalSpace I] [FirstCountableTopology I] in
lemma before_base {p:ℕ}{V:GraphSum G false p}{H:Mob G}(ht:V.instructions.renorm=classicalPage H): absNom μ (bed V) s x= plow (-(p:ℂ)) s H:= by
    have h := leafValue p p μ _ V.accepted.after.toll s x; rw [sub_self] at h;
    change backing 0 (asLeaf _ μ _) 0 s x=_; rw [h,ht]; exact initialBudget μ s (collapsed_kernel (ht ▸ V.accepted.usable.clock : ClockD false 0 V.slots _)).price
omit [TopologicalSpace I] [FirstCountableTopology I] in
lemma pinnedAtom {p:ℕ}(F:LocalVertex G false p) : absNom μ (bed (vertex F)) s x= F.symbol:= (before_base μ s x (renorm_vertex F)).trans (F.scaling s)
omit [TopologicalSpace I] [FirstCountableTopology I] in
lemma bulkAtom (V:LocalVertex G true 4) : absBulk μ (vertex V) s x= V.symbol:= by obtain h:= leafValue 0 4 μ _ (vertex V|>.accepted.after.toll) s x; push_cast at h; rw [zero_sub] at h; unfold absBulk; rw [ h, renorm_vertex ]; rw [show ruby _ 0=_ from (initialBudget (X:=V.symbol) (p:=4) μ s V.cap.fine.tune.mer.price.exists.choose_spec) ]; exact V.scaling s
end Planted
lemma ode_solver {F H:ℝ→ℂ}{f:ℝ→ℂ}(hx:∀ t, HasDerivAt F (f t) t)(hv:∀ t, HasDerivAt H (f t) t)(h:Tendsto F atBot (𝓝 0))(hp:Tendsto H atBot (𝓝 0)) : F=H := by
    have Hx : ∀ t:ℝ,F t-H t=F 0-H 0:= fun t=> is_const_of_deriv_eq_zero (fun t=> ((hx t).sub (hv t)).differentiableAt) (fun t=> by rw [ ((hx t).sub (hv t)).deriv,sub_self ]) t 0
    have he := Tendsto.congr (fun x=> Hx x) (h.sub hp); rw [sub_zero] at he; have ht:F 0-H 0=0:= tendsto_nhds_unique tendsto_const_nhds he; exact funext fun t=>sub_eq_zero.mp ((Hx t).trans ht)
end YM.MS.ScaleForest
