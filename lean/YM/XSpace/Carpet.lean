import YM.XSpace.Aura
import YM.XSpace.BareProfiles
/-!
# Uniform mesh smearing of genuinely continuous limiting output obtained from a portrait

Includes choosing any test f with specified compact support, estimate in `Bound` for arbitrary accuracy across such f. Uses joint `Mesh.Fits` and centers inside Box.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Cirrus
open Filter Set Function Metric Lattice TestBudget Expense MeasureTheory
open scoped Topology BigOperators ContDiff Classical
variable {n:ℕ} (m:Mesh) (f:Test n)
abbrev Centered (Y:Sample n→ℂ) := ∀ m:Mesh,∀ (v:pack n)(c:Four ℝ), Y ⟨m,v,c⟩=Y ⟨m,v,0⟩
-- finite formula and multilinearity by abbreviation with ∫ c included
abbrev Deposit (m:Mesh)(Y:Sample n→ℂ)(f:Test n):= (m.spacing:ℂ)^(4*n)*∑ x:m.Tuple,m.smear (Mesh.back m x) f * Y ⟨m,m.back x, 0⟩
variable (Y:Sample n→ℂ)
def board (c:Four ℝ)(x:m.Tuple (n:=n)):= f (m.rel (m.back x) c)*Y ⟨m,m.back x,0⟩
def paths (c: Four ℝ):=∫ z,m.levels c (board m f Y c) z
lemma stroll (c:Four ℝ): paths m f Y c= (m.spacing:ℂ)^(4*n)*∑ x:m.Tuple (n:=n),f (m.rel (m.back x) c)*Y ⟨m,m.back x,0⟩:= m.stair_exact c _
lemma on_board : IntegrableOn (paths m f Y) m.Box:= by simp_rw [show paths m f Y=_ from funext (stroll m f Y)]; apply Integrable.const_mul; exact integrable_finsetSum _ fun i _=> (m.term_integrable ..).mul_const _
lemma homeward : Deposit m Y f=(m.vol:ℂ)⁻¹ * ∫ c in m.Box, paths m f Y c:=by
  unfold Deposit; simp_rw [stroll, integral_const_mul,mul_left_comm ((m.vol:ℂ)⁻¹) ((m.spacing:ℂ)^(4*n))]; congr 1
  change _= (m.vol:ℂ)⁻¹ * ∫ c in m.Box, ∑ x:m.Tuple,m.termView f (m.back x) c*Y ⟨m,m.back x,0⟩
  rw [integral_finsetSum _ (fun i _ => (m.term_integrable f (m.back i)).mul_const _)]
  simp_rw [Finset.mul_sum,Mesh.smear,LinearMap.coe_mk,AddHom.coe_mk,Complex.real_smul, Complex.ofReal_inv,integral_mul_const, mul_assoc]
lemma homeward_price (z:ℂ)(b:ℝ)(h:∀ c∈m.Box, ‖paths m f Y c-z‖≤b): ‖Deposit m Y f-z‖≤b:=by
  have ha : 0<m.vol:=m.vol_pos; rw [homeward, show ((m.vol:ℂ)⁻¹ * ∫ c in m.Box,_)-z= (m.vol:ℂ)⁻¹ * ∫ c in m.Box, (paths m f Y c-z) from ?_, norm_mul,norm_inv, Complex.norm_real, Real.norm_of_nonneg ha.le]
  apply (mul_le_mul_of_nonneg_left (norm_setIntegral_le_of_norm_le_const m.compact_box.measure_lt_top h) (by positivity : (0:ℝ) ≤ m.vol⁻¹)).trans_eq; rw [show volume.real m.Box=m.vol from rfl,mul_left_comm m.vol⁻¹,inv_mul_cancel₀ ha.ne',mul_one] -- order n*
  rw [integral_sub (on_board m f Y) (integrableOn_const m.compact_box.measure_ne_top),setIntegral_const, Complex.real_smul, show volume.real m.Box=m.vol from rfl,mul_sub,inv_mul_cancel_left₀ (by exact_mod_cast ha.ne')]

variable {K V:Set (Points n)}(p: Points n→ℂ)(hv: IsOpen V)(hp:ContinuousOn p V) (hk:K⊆V) (hc:IsCompact K){b:ℝ}
include hk hp hv in
lemma can_pay (s:tsupport f⊆K): Integrable (Damp f p):=by
  have he : Continuous (Damp f p):= continuous_iff_continuousAt.mpr (fun i=> by
    by_cases h:i∈tsupport f; exact f.continuous.continuousAt.mul ((hp i (hk (s h))).continuousAt (hv.mem_nhds (hk (s h))))
    have h' : Damp f p =ᶠ[𝓝 i] 0 := Filter.Eventually.mono ((isClosed_tsupport _).isOpen_compl.mem_nhds (show i∈(tsupport f)ᶜ from h)) (fun x hx=> mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport hx) (p x)); exact ContinuousAt.congr (g:=Damp f p) continuousAt_const h'.symm)
  exact he.integrable_of_hasCompactSupport f.hasCompactSupport.mul_right
include hc hp hk in
lemma rests (e:ℝ)(he:0<e): ∃ r:ℝ,0<r∧∀ f:Test n,∀ b:ℝ,tsupport f⊆K → Bound f b→ ∀ x y:Points n,dist x y < r→ ‖f x*p x-f y*p y‖ ≤ b*e:= by
  obtain ⟨C,hC⟩:= (hc.image_of_continuousOn (hp.mono hk).norm).bddAbove; let M:=max C 1; have hu :0<M:=zero_lt_one.trans_le (le_max_right ..); have hM x(h:x∈K) : ‖p x‖≤M:=(hC (mem_image_of_mem _ h)).trans (le_max_left ..)
  obtain ⟨r,hr,H⟩:= Metric.uniformContinuousOn_iff.mp (hc.uniformContinuousOn_of_continuous (hp.mono hk)) (e/2) (by positivity)
  let s:ℝ:= e/(2*M); have hs :0<s:=by unfold s; positivity
  refine ⟨min r s,lt_min hr hs,fun f b hf hb x y h=>?_⟩
  have h0:= bound_nonneg f hb; have hl(a z:Points n)(h: dist a z<s): ‖f a-f z‖ ≤ b*s:=by
    apply le_trans _ (mul_le_mul_of_nonneg_left h.le h0); rw [dist_eq_norm]; exact (convex_univ (𝕜:=ℝ)).norm_image_sub_le_of_norm_fderiv_le (fun _ _=> f.contDiff.differentiable (by simp) _) (fun i _=> (hb i).2) (mem_univ z) (mem_univ a)
  have hg:b*s*M=b*e/2:= by unfold s; field_simp
  have hZ x (h:x∉K):f x=0:=image_eq_zero_of_notMem_tsupport (fun ht=>h (hf ht))
  have hw (x y:Points n)(hx:x∈K)(hy:y∉K)(h:dist x y<s): ‖f x*p x-f y*p y‖ ≤ b*e:=by rw [hZ y hy,zero_mul,sub_zero,norm_mul]; apply (mul_le_mul (le_trans (le_of_eq (by rw [hZ y hy,sub_zero])) (hl x y h)) (hM x hx) (norm_nonneg _) (by positivity : 0≤ b*s)).trans; rw [hg]; linarith [mul_nonneg h0 he.le]
  have h':dist x y<s:=lt_of_lt_of_le h (min_le_right ..); by_cases ha:x∈K; by_cases hY:y∈K; swap; exact hw x y ha hY h'
  · rw [show f x*p x-f y*p y=f x*(p x-p y)+(f x-f y)*p y from by ring]; apply (norm_add_le ..).trans; rw [norm_mul,norm_mul]; apply (add_le_add (mul_le_mul (hb x).1 (le_of_lt (dist_eq_norm (p x) (p y) ▸ H x ha y hY (lt_of_lt_of_le h (min_le_left ..)))) (norm_nonneg _) h0) (mul_le_mul (hl x y h') (hM y hY) (norm_nonneg _) (mul_nonneg h0 hs.le))).trans_eq; rw [hg]; ring
  by_cases hb':y∈K; rw [norm_sub_rev]; exact hw y x hb' ha (dist_comm y x ▸ h'); rw [hZ y hb',hZ x ha,zero_mul, zero_mul,sub_zero,norm_zero]; positivity

variable (S:Senses V Y p)(A:Centered Y)
-- any ε, with room for center cells
include hv hp hc hk S A in
lemma graduate (e:ℝ)(he:0<e) : ∀ᶠ m in Front,∀ f:Test n, tsupport f ⊆ K→∀ b:ℝ,Bound f b→ ‖Deposit m Y f- f.applyTo p‖≤ b*e:=by
  obtain ⟨r,h⟩:= (hc.image continuous_norm).bddAbove
  let U:= closedBall (0: Points n) (r+4*n); let g:= volume.real U; have hg : 0≤g:= ENNReal.toReal_nonneg
  let x:=e/(2*(g+1)); have hx:0<x:=by unfold x; positivity
  obtain ⟨d,hd,H⟩:=rests p hp hk hc x hx
  filter_upwards [S.placed hc hk x hx, frontier.smaller,(frontier.endpt.const_mul (4*n:ℝ)).eventually (gt_mem_nhds (by rw [mul_zero]; exact hd)), Mesh.fits_compact frontier U (isCompact_closedBall ..)] with m hm hm' hτ hs f hf b hb; refine homeward_price m f Y (f.applyTo p) (b*e) (fun c hc'=>?_) ; let Q:=m.levels c (board m f Y c); let w:= Damp f p; have hb' := bound_nonneg f hb; let s:=b*x; have h0: 0≤s:=mul_nonneg hb' hx.le
  have hu : ∀ z:Points n,z∈K→ ‖z‖≤r:=fun z hz=> h (mem_image_of_mem norm hz); have inside (z:Points n)(h:‖z‖≤r+4*n): z∈U:= Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact h); have hI : ∀ z:Points n,z∈K→ z∈U:=fun i hi=>inside i ((hu i hi).trans (by simp)); have hez (i:Points n)(h:i∉K):f i=0:=image_eq_zero_of_notMem_tsupport (fun hg=>h (hf hg)); have hh:m.spacing ≤ 1:=hm'
  have hY (z: Points n): ‖Q z-w z‖ ≤ s+s ∧ (z∉U→Q z-w z=0):=by
    by_cases hx : ∃ i:m.Tuple (n:=n),z∈ m.cell c (m.back i)
    · obtain ⟨i,hi⟩:=hx; let v:=m.rel (m.back i) c; rw [show Q z=f v*Y ⟨m,m.back i,c⟩ from Eq.trans (m.stair_at c z hi) (congr_arg (f v*·) (A m (m.back i) c).symm)]
      have he : dist v z ≤ (4*n:ℝ)*m.spacing:= m.upper_corner c hi; have hp: ‖f v*Y ⟨m,m.back i,c⟩-w v‖ ≤ s:=by
        rw [show w v=f v*p v from rfl, ← mul_sub, norm_mul]; by_cases hq:v∈K; · exact mul_le_mul (hb v).1 (by rw [← dist_eq_norm]; exact hm ⟨m,m.back i,c⟩ rfl hc' hq) (norm_nonneg _) hb'
        rw [hez v hq,norm_zero,zero_mul]; exact h0
      constructor
      · rw [← sub_add_sub_cancel (f v*_) (w v) (w z)]; exact (norm_add_le ..).trans (add_le_add hp (H f b hf hb v z (he.trans_lt hτ)))
      intro hq; rw [show w z=f z*p z from rfl,hez z (fun hk=> hq (hI z hk)),hez v (fun hk=> hq (inside z (Mesh.norm_near hh (hu v hk) (dist_comm z v ▸ he)))),zero_mul, zero_mul,sub_zero]
    rw [show Q z=0 from m.stair_off c z (fun i hi=> hx ⟨i,hi⟩), show w z=f z*p z from rfl,hez z (fun hk=> hx (m.gained c hh hc' hs z (hu z hk))),zero_mul, sub_zero,norm_zero]; exact ⟨add_nonneg h0 h0,fun _=>rfl⟩
  change ‖(∫ z,Q z)-(∫ z,w z)‖ ≤ _; rw [← integral_sub (m.integrable_stair ..) (can_pay f p hv hp hk hf), ← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=U) (fun z=> (hY z).2)]
  apply (norm_setIntegral_le_of_norm_le_const (isCompact_closedBall ..|>.measure_lt_top) (fun x _=> (hY x).1)).trans; change (s+s)*g ≤ _; apply le_trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (zero_le_one)) (add_nonneg h0 h0)) (le_of_eq ?_); unfold s x; field_simp; ring
end YM.XSpace.Cirrus
