import YM.MS.Arc.Woods
/-!
# Half-plane pump output is holomorphic with all required derivative prices

Contour on min ε (actually z), blocked hist. Later germs may use not this entire half-plane,
 pump theorem accepts any isotropic open D⊆. Ordered integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real Metric
open scoped Topology ContDiff Interval
variable {I E F G: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℂ F][NormedSpace ℝ F][IsScalarTower ℝ ℂ F][CompleteSpace F] [NormedAddCommGroup G][NormedSpace ℝ G]
variable {c:ℂ}{R:ℝ}{D:Set ℂ}{b:ℕ}{f:ℂ→ Tree E F}
def Town : Set ℂ:= setOf ups
-- re < or >
lemma way : IsOpen Town := by exact isOpen_lt continuous_const (show Continuous (fun z:ℂ=>2*z.re+1) by fun_prop) -- syntax wrong
lemma mag (c:ℂ)(R:ℝ) : ∃ b:ℕ, ∀ z∈closedBall c R, 2*z.re+1 ≤ (b:ℝ):= by
   let L (p:ℂ):=2*p.re+1; have hx: Continuous L:= by unfold L; fun_prop
   obtain ⟨C,hC⟩:= (isCompact_closedBall c R|>.image hx).bddAbove; obtain ⟨b,hb⟩:= exists_nat_ge C; exact ⟨b,fun z hz=> (hC (mem_image_of_mem L hz)).trans hb⟩
-- support estimates at p>0
omit [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
lemma wind_bound (h:Tracks D f)(p:E)(hr:0<R)(ht:closedBall c R⊆D)(hz:D⊆ Town): ∃ w:ℝ→ℝ, Integrable w μhalf ∧ ∀ t:ℝ,0<t→ ∀ z∈closedBall c R, ‖fetchP (cloud z) (f z) t p‖≤w t:= by
   obtain ⟨b,hb⟩:=mag c R; obtain ⟨C,hC,k,hk⟩ := Q.man (h.price c R hr ht) 0 (b+2); let X:=C*(1+‖p‖)^k; let L(t:ℝ):=((1+‖t‖)^2)⁻¹; have hx : (path fun x:Unit=> 0).dust 2 ()=L:= funext fun p:ℝ=>by simp [L,Scale.dust,Scale.weight]
   have he : Integrable L μhalf:= hx ▸ (Reserve.dustInteg (S:=path fun x:Unit=> 0) () (μ:=volume) (E:=ℝ) 2 (by simp)).restrict
   refine ⟨fun t=> X*L t,he.const_mul X,fun t hx z hp=>?_⟩; have hε : ups z:= hz (ht hp)
   obtain hw:= cloud_near hε (hb z hp) hx; have hk:= hk (⟨z,hp⟩:closedBall c R) t p; simp only [norm_iteratedFDeriv_zero,Pi.zero_apply,Pi.one_apply,abs_zero,add_zero,one_mul,mul_one,pow_add] at hk; refine (show ‖fetchP (cloud z) (f z) t p‖= ‖cloud z t‖ * ‖f z (t,p)‖ from norm_smul _ _).le.trans ?_; refine (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans ?_; unfold L; dsimp only; rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]; rw [mul_comm _ ‖f z (t,p)‖,mul_assoc]; exact hk
-- needs ae for cloud z holom almost all t
lemma cloud_hol (t:ℝ)(hp:0<t): Differentiable ℂ fun z=> cloud z t:= by
    unfold cloud; exact Differentiable.const_cpow (by fun_prop) (Or.inl ( Complex.ofReal_ne_zero.mpr hp.ne')) -- inspect
lemma in_hush (h:Tracks D f)(hu:IsOpen D)(hz:D⊆Town) : Plots D (fun z => fetching (f z) (cloud z)) where
   span := by intro c R hc hp; obtain ⟨b,hb⟩:=mag c R; have he:= shade_fin (h.price c R hc hp) (shade_cloud (Z:=fun i=> i.val) (fun i=>hz (hp i.property)) (fun i=>hb _ i.property)); convert! he using 1; ext; simp
   root := by
       intro p c hc; let U z t:= fetchP (cloud z) (f z) t p; have he : borelad μhalf D U:= fun z hp=> cloud_sees.smul (((area_smooth h.plot hu hp).continuous.comp (f:=fun t:ℝ=> (t,p)) (by fun_prop)).aestronglyMeasurable)
       obtain ⟨R,hR,hT⟩:= radius_pay hu hc; obtain ⟨w,hw,hp⟩:= wind_bound h p (show 0<2*R by linarith) hT hz; have h0:=ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=(0:ℝ))); have hi : ∀ᵐ i ∂μhalf,Forest D (fun z=> U z i):= h0.mono fun t ht z hz=> by exact ((cloud_hol t ht z).smul (h.rays (t,p) z hz)) -- lean rfl
       exact (middle hu hi he hR hT hw (h0.mono hp)).differentiableAt
-- carpet hol, real moment integration
variable [MeasurableSpace G][BorelSpace G][FiniteDimensional ℝ G](μ:Measure G)[μ.IsAddHaarMeasure]
variable {X:ℂ→(G×ℝ)× E→ F}
omit [CompleteSpace F] [IsScalarTower ℝ ℂ F] in
lemma bondC (h:Tracks D X)(hp:closedBall c R⊆D) (hr:0<R) (x:ℝ×E): ∃ f:G→ℝ, Integrable f μ∧∀ z∈closedBall c R, ∀ y:G,‖X z ((y,x.1),x.2)‖≤f y:= by
    let L:= Q.trees (h.price c R hr hp); let S:=(path (0:UScale (closedBall c R))) ; let n:=Module.finrank ℝ G+1; let W:closedBall c R:=⟨c,mem_closedBall_self hr.le⟩; have he: ∀ y,S.weight y=(S.weight W: G→ℝ) := fun y=>rfl
    obtain ⟨C,hC,b,hb⟩:= L.dominates 0 n; let D:= C*(S.full.cheap W x)^b
    refine ⟨fun t=> D*S.dust n W t,(Reserve.dustInteg (μ:=μ) (S:=S) W n (by unfold n; omega)).const_mul D,fun y hp p=>?_⟩; specialize hb (⟨y,hp⟩:closedBall c R) p x (mem_univ _); simp only [Pi.one_apply,norm_iteratedFDeriv_zero,pow_zero, mul_one] at hb; convert hb using 1 <;> rfl
omit [IsScalarTower ℝ ℂ F] in
lemma Tracks.C (h:Tracks D X)(hD:IsOpen D): Tracks D (fun z=>carpet μ (X z)):= by
   refine ⟨fun c R hr hp=>Q.Gquiet μ (h.price c R hr hp),?_⟩; intro p c hc; let V(z:ℂ)(x:G):= X z ((x,p.1),p.2); have he : borelad μ D V:= by
       intro x hx; obtain ⟨R,hR,h⟩:= radius_pay hD hx; exact ((Q.Gmajor μ ((‹Tracks D X›).price x (2*R) (by linarith) h) (⟨x,mem_closedBall_self (by positivity)⟩:closedBall x (2*R))).values p).aestronglyMeasurable
   obtain ⟨R,hR,hV⟩:= radius_pay hD hc; obtain ⟨L,hL,hx⟩:= bondC μ h hV (show 0<2*R by linarith) p; exact (middle hD (Eventually.of_forall (fun i=> h.rays ((i,p.1),p.2))) he hR hV hL (Eventually.of_forall fun t p hp=>hx p hp t)).differentiableAt
-- pump hol stability
lemma Tracks.p (h:Tracks D X)(hD:IsOpen D)(hp:∀ i∈D,mirror (X i))(hz:D⊆Town)(m:ℕ): Plots D (fun z=> swoop z μ m (X z)):= by
   let Fx(z:ℂ):= fetching (pruning (m+1) (carpet μ (X z))) (cloud z); obtain H:= in_hush ((h.C μ hD).pr hD (fun i hi=>mirror_r μ (hp i hi)) (m+1)).1 hD hz
   refine ⟨fun c R hR hQ=> (H.span c R hR hQ).L ((gage m) • ContinuousLinearMap.id ℝ F),fun p c hc=> (H.root p c hc).const_smul (gage m)⟩ -- F shadows type
end YM.MS.Arc
