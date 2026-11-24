import YM.Trace.Fock.Germ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace YM.Trace.Shell
open scoped Topology ContDiff FourierTransform InnerProductSpace BigOperators Pointwise
open YM Filter Function Complex Set MeasureTheory Boundary LineDeriv
open SchwartzMap
abbrev polySlot (m : ℕ) := Σ n : Fin (m+1), multi_slots n.1
def axisSymbol (d p : Mom) := (2*(Real.pi:ℂ)*I) * ↑(inner ℝ (Probe.collapse p) d)
def jetPolynomial {n : ℕ} (k : Fin n → Mom) (p : Mom) := ∏ i, axisSymbol (k i) p
def slotPolynomial {d : ℕ} (k : polySlot d) (p : Mom) := jetPolynomial (fun i => axis (k.2 i)) p
@[fun_prop] lemma slotPolynomial_cont {m} (k: polySlot m) : Continuous (slotPolynomial k) := by unfold slotPolynomial jetPolynomial axisSymbol; fun_prop
lemma slotPolynomial_dilate {n : ℕ} (k : polySlot n) (p : Mom) (t : ℝ) : slotPolynomial k (t • p) = ↑(t^k.1.val) * slotPolynomial k p := by
  unfold slotPolynomial jetPolynomial axisSymbol
  simp only [map_smul, real_inner_smul_left, ofReal_mul, ← mul_assoc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast; ring
lemma jet_hat (f : Probe Mom) : ∀ n (k : Fin n → Mom) (p), Probe.hat (∂^{k} f) p = jetPolynomial k p * Probe.hat f p := by
  intro n; induction n with
  | zero => intro k p; simp [jetPolynomial]
  | succ n IH =>
      intro k p
      rw [iteratedLineDerivOp_succ_left,jetPolynomial,Fin.prod_univ_succ,show (∏ i : Fin n, axisSymbol (k i.succ) p) = jetPolynomial (Fin.tail k) p from rfl]
      rw [mul_assoc, ← IH]
      let g := ∂^{Fin.tail k} f
      let u := k 0
      change 𝓕 (∂_{u} g) (Probe.collapse p) = _ * 𝓕 g (Probe.collapse p)
      have h : (inner ℝ · u).HasTemperateGrowth := ((innerSL ℝ).flip u).hasTemperateGrowth
      rw [fourier_lineDerivOp_eq, smul_apply, smulLeftCLM_apply_apply h,smul_eq_mul,real_smul]
      dsimp [axisSymbol]; ring
lemma jet_integrable {m : ℕ} (k : polySlot m) (f : Probe Mom) : Integrable (fun p => slotPolynomial k p * Probe.hat f p) volume := by
  have h := (Probe.hat (∂^{fun t => axis (k.2 t)} f)).integrable (μ:=volume)
  change Integrable (fun p => Probe.hat (_) p) volume at h
  simp_rw [jet_hat] at h; exact h
lemma jet_focus (f : Probe Mom) {m : ℕ} (k : polySlot m) :
       monomialJet k.1.val k.2 0 f = (Probe.pref Mom : ℂ)⁻¹ * ∫ p : Mom, slotPolynomial k p * Probe.hat f p := by
  unfold monomialJet
  rw [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  rw [eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast Probe.prepos.ne' : (Probe.pref Mom : ℂ) ≠ 0)]
  simpa [Probe.plane_zero,jet_hat,real_smul,slotPolynomial] using (Probe.positiveFourier (∂^{fun t=>axis (k.2 t)} f) 0).symm

def stampJet (m : ℕ) : Probe Mom →ₗ[ℂ] (polySlot m → ℂ) where
 toFun f i := ∂^{(fun k=> axis (i.2 k))} f 0
 map_add' f g := by funext; simp [iteratedLineDerivOp_add,add_apply]
 map_smul' c f := by funext; simp [iteratedLineDerivOp_smul,smul_apply]
def slotPacket {m : ℕ} (a : polySlot m → ℂ) (p : Mom) := ∑ i, a i * slotPolynomial i p
lemma slotPacket_integrable {m : ℕ} (a : polySlot m → ℂ) (f : Probe Mom) : Integrable (fun p=> slotPacket a p * Probe.hat f p) volume := by
 simp_rw [slotPacket,Finset.sum_mul,mul_assoc]; exact integrable_finsetSum Finset.univ fun i _ => (jet_integrable i f).const_mul _
@[fun_prop] lemma slotPacket_cont {m} (a : polySlot m → ℂ) : Continuous (slotPacket a) := continuous_finsetSum _ (fun i _=> continuous_const.mul (slotPolynomial_cont ..))

lemma stamp_flat {f : Probe Mom} {m} (h : f ∈ LinearMap.ker (stampJet m)): FlatAns m 0 f := by
  intro j hj i; unfold monomialJet
  simpa only [stampJet,LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, ← iteratedLineDerivOp_eq_iteratedFDeriv] using congrFun (LinearMap.mem_ker.mp h) (⟨⟨j,Nat.lt_succ_of_le hj⟩,i⟩ : polySlot m)
lemma exists_transfer (L : Distn Mom) (m : ℕ) (hL : ∀ f, FlatAns m 0 f → L f=0) : ∃ a: polySlot m → ℂ, ∀ f,
   L f= ∫ p, slotPacket a p * Probe.hat f p := by
 classical
 let T := stampJet m
 let p := LinearMap.ker T
 let v := p.liftQ T (le_refl _)
 let u := p.liftQ L.toLinearMap (fun f hf=> LinearMap.mem_ker.mpr (hL f (stamp_flat hf)))
 let A := u.comp v.leftInverse
 have hE (f : Probe Mom) : A (T f) = L f := by
    have h := v.leftInverse_apply_of_inj (Submodule.ker_liftQ_eq_bot _ _ _ (le_refl _)) (p.mkQ f)
    exact congrArg u h
 refine ⟨fun k=> A (Pi.single k 1) * (Probe.pref Mom : ℂ)⁻¹, fun f=> ?_⟩
 rw [← hE f,show T f=(∑ k, (T f k) • Pi.single k 1) by ext j; simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; symm; apply Eq.trans (Finset.sum_eq_single j ?_ (by simp)) (by simp); intro b hb h; simp [Pi.single_eq_of_ne h.symm], map_sum]
 have heA k : T f k = (Probe.pref Mom:ℂ)⁻¹ * ∫ p, slotPolynomial k p * Probe.hat f p := by
   dsimp only [T,stampJet]; change ∂^{(fun j=> axis (k.2 j))} f 0 = _
   erw [iteratedLineDerivOp_eq_iteratedFDeriv]
   exact jet_focus f k
 simp_rw [A.map_smul, smul_eq_mul,slotPacket, Finset.sum_mul]
 rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _=>by simpa only [mul_assoc] using ((jet_integrable i f).const_mul ((Probe.pref Mom : ℂ)⁻¹)).const_mul (A (Pi.single i 1)))]; congr! 2 with k
 simp_rw [heA,mul_assoc,MeasureTheory.integral_const_mul]; ring


lemma locally_testable_integrable (g : Mom→ℂ) (h : ∀ f: Probe Mom, Integrable (fun x=>f x*g x) volume) : LocallyIntegrable g volume := by
 intro x
 have hi := h (Probe.ahead x (ruler Mom))
 refine ⟨Metric.ball x 1, Metric.ball_mem_nhds _ (by norm_num), hi.integrableOn.congr_fun (fun y hy=> ?_) Metric.isOpen_ball.measurableSet⟩
 have h : ‖y-x‖ ≤ 1 := (show ‖y-x‖ < 1 from by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hy).le
 exact (rfl.trans rfl : (Probe.ahead x (ruler Mom) y*g y = _)).trans (show ruler Mom (y-x)*g y=g y by rw [ruler_one h,one_mul])
lemma packet_unique {A : Mom→ℂ} {m : ℕ} (b : polySlot m→ℂ) (h : ∀ f: Probe Mom, ∫ x, A x * f x = ∫ x, slotPacket b x * f x) (he : ∀ f:Probe Mom, Integrable (fun x=>f x*A x) volume) : A =ᶠ[ae volume] slotPacket b := by
 apply ae_eq_of_integral_contDiff_smul_eq (locally_testable_integrable A he) (slotPacket_cont b).locallyIntegrable
 intro g hg hG
 let G := (hG.comp_left ofReal_zero |>.toSchwartzMap (ofRealCLM.contDiff.comp hg))
 have he:= h G
 exact (integral_congr_ae (ae_of_all _ fun x => by change g x• A x = A x*(g x:ℂ); rw [real_smul,mul_comm])).trans (he.trans (integral_congr_ae (ae_of_all _ fun x=> by change slotPacket _ _ * (g x:ℂ)=g x • _; rw [real_smul,mul_comm])))

lemma bounded_two_bare_packets (N : ℕ) : ∃ m : ℕ, ∀ (A D : Mom→ℂ), Control N A → Control N D → Rule A D → ∀ k : Fin 2, ∃ b: polySlot m→ℂ, bare A D k=ᶠ[ae volume] slotPacket b := by
 obtain ⟨s,c,hc⟩:= finite_price (N+2) Probe.hat
 refine ⟨2*s.sup Prod.snd+1, fun A D hA hD h=> ?_⟩
 have hb (k : Fin 2) (f) (hf : FlatAns (2*s.sup Prod.snd+1) 0 f) := supported_bound f (cauchyCLM hA hD k) (fun f hT hx=>cauchy_support hA hD h f hT hx k) s
   ((2:ℝ)^(N+2)*bareCost N A D*(c:ℝ)) (by have h : 0≤bareCost N A D := bareCost_nonneg; have : 0≤(c:ℝ) := c.coe_nonneg; positivity) (fun t=>by rw [mul_assoc _ (c:ℝ)]; exact (cauchy_bound hA hD k t).trans (mul_le_mul_of_nonneg_left (hc _) (by change 0 ≤ _; apply mul_nonneg (by positivity) bareCost_nonneg))) hf
 have hm k : ∃ a : polySlot (2*s.sup Prod.snd+1)→ℂ, bare A D k=ᶠ[ae volume] (slotPacket a) := by
    obtain ⟨a,ha⟩ := exists_transfer _ _ (hb k)
    refine ⟨a, packet_unique a (fun t=> ?_) (bare_integrable hA hD k)⟩
    rw [← Probe.travels t]; conv_lhs => rhs; intro; rw [mul_comm]
    exact ha _
 exact hm
lemma bounded_bare_packets (N : ℕ) : ∃ m : ℕ, ∀ (A D : Mom→ℂ), Control N A → Control N D → Rule A D → ∃ a b : polySlot m→ℂ, ∀ᵐ p ∂ν,
     A p = (‖p‖ : ℂ)*slotPacket a p + slotPacket b p := by
 obtain ⟨m,h⟩:=bounded_two_bare_packets N
 refine ⟨m,fun A D hA hD hx=> ?_⟩
 have hm := h A D hA hD hx
 obtain ⟨a,ha⟩:=hm 0
 obtain ⟨b,hb⟩:=hm 1
 refine ⟨a,b,?_⟩; refine (MeasureTheory.withDensity_absolutelyContinuous _ _ ?_) -- wrong name and direct ae
 filter_upwards [ha,hb, (ae_iff.mpr (by simp) : ∀ᵐ p ∂(volume:Measure Mom),p ≠ 0)] with p ha hb hp
 have ht : (‖p‖:ℂ) ≠0 := by norm_cast; exact norm_ne_zero_iff.mpr hp
 rw [← ha, ← hb]; simp [bare]; field_simp; ring
end YM.Trace.Shell
