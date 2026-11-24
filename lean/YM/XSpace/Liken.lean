import YM.XSpace.Perch
/-!
# Basic time slices staging along any relative distance (plus orientation)

Retains powers of native spacings incl quantitativeness of leakage.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Relief
open Function Set Filter Lattice Trace Chiral Litter Mu Tide Scale Pages Sail Chart2 Finsupp Source Future Asymptotics Playpen
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge} {d r:ℕ} {H:Hol G} (g:G.Simple)(S:Survey G H d)
variable {ι:Type}{a:ι→ℝ}{L:Filter ι}{x y:ι→Cover}
structure Stage (L: Filter ι)(a:ι→ℝ): Prop where
  zero:Tendsto a L (𝓝 0)
  good:∀ᶠ i in L,0<a i
abbrev distance (L: Filter ι)(a:ι→ℝ)(x:ι→Cover)(u:E4):= Tendsto (fun i=> actual (a i) (x i)) L (𝓝 u)
def funds {F: Type*}[Norm F] (L:Filter ι)(a:ι→ℝ)(k:ℕ)(X:ι→F):= X=O[L]fun i=> a i^k
variable (s:Stage L a){u:E4}(h:distance L a x u)(H':u≠0)
abbrev distFee (L:Filter ι)(a:ι→ℝ)(x:ι→Cover): Prop:=∃ C:ℝ,0<C∧∀ᶠ i in L,C≤ a i*Drama.area (x i)
include s h H'
lemma no_cost_zero : ∀ᶠ i in L, x i≠0:= (h.eventually (isOpen_compl_singleton.mem_nhds (show u∈{(0:E4)}ᶜ from H'))).mono fun i hi hx=> hi (mem_singleton_iff.mpr (by change actual _ _=0; rw [hx, actual, show Further.FreeCovariance.KP.rcast 0=0 from ?_, smul_zero]; ext k;simp [Further.FreeCovariance.KP.rcast]))
lemma finite_pay : distFee L a x:=by
  have hp:0<‖u‖:=norm_pos_iff.mpr H'; refine ⟨‖u‖/4,by positivity,?_⟩; filter_upwards [h.norm.eventually (le_mem_nhds (show ‖u‖/2<‖u‖ from half_lt_self hp)), s.good] with i hi hh; let v:= x i; let p:=a i; have he:= (Shade.size_actual (x:= x i) hh).2; change _≤p*Drama.area v; unfold Drama.area; change _≤p*(1+↑(reach v)); linarith
omit h H' in
lemma stage_price (h:distFee L a x)(k:ℕ) : funds L a k (fun i=> carry k (reach (x i))) := by
  obtain ⟨C,hC,H⟩:=h; apply IsBigO.of_bound (C⁻¹^k); filter_upwards [H,s.good] with i hi hp; rw [Real.norm_of_nonneg (carry_pos ..).le, Real.norm_of_nonneg (pow_pos hp k).le]; unfold carry; rw [← mul_pow]; gcongr; unfold Drama.area at hi; field_simp; linarith
omit h H' in
lemma funder {x:ι→Cover} {k:ℕ}(hv:distFee L a x){p: Toe}(h:p∈Terrain k): funds L a k (fun i=> p (x i)):=by
  refine IsBigO.trans ?_ (stage_price s hv k); obtain ⟨C,hC,H⟩:= virgin h; exact IsBigO.of_bound C (Eventually.of_forall fun i=>by rw [Real.norm_of_nonneg (carry_pos ..).le]; apply H)
omit h H' in
lemma pays0 {p:ι→ℝ}(k:ℕ)(H:funds L a (k+1) p): Tendsto (fun i=>(a i)⁻¹^k*p i) L (𝓝 0):=by
  apply IsBigO.trans_tendsto _ s.zero; obtain ⟨C,h⟩:= H.bound; apply IsBigO.of_bound C; filter_upwards [h,s.good] with i hi ht; rw [norm_mul,Real.norm_of_nonneg (pow_nonneg (by positivity) k), Real.norm_of_nonneg ht.le]; rw [Real.norm_of_nonneg (pow_pos ht _).le] at hi; exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by rw [pow_succ, inv_pow]; field_simp)
lemma off_point (T:Survey G H r)(σ:Bool)(p q:P)(hd:2≤d)(hr:2≤r): funds L a 5 (fun i=> surveyed g S σ p (Mn g T σ q) (x i)):=by
  have he:= funder s (finite_pay s h H') (surfaces (slept g S T hd hr σ p q)); exact IsBigO.congr' he (by filter_upwards [no_cost_zero s h H'] with i hi; rw [Pi.sub_apply,trace_at, if_neg (show ¬(_∧_) from fun h=> hi h.2),sub_zero]) (EventuallyEq.refl ..)
omit h H' in
lemma duty {u:E4}(h:distance L a (fun i=>x i-y i) u)(hU:u≠0)(T: Survey G H r)(σ:Bool)(p q:Name G)(hd: 2≤d)(hr:2≤r): funds L a 5 (fun i=> handshake (cable g S σ p (x i)) (cable g T σ q (y i))):= by simp_rw [cup]; exact IsBigO.const_mul_left (off_point g S s h hU T σ p.1 q.1 hd hr) _
end YM.XSpace.Relief
