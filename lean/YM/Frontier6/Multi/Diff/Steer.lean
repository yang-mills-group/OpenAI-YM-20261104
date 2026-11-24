import YM.Frontier6.Multi.Diff.Dials

/-! one-coordinate chain. Includes detectors with moving costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Finset Set MergeProof.Ribbons MergeProof.Acme Fareway Tale Spec
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {I J V X:Type} [TopologicalSpace X][Fintype V][DecidableEq V]{G:Gauge}{C:Family G}{F:Extraction.Order}{S: Table C.book}
variable (K:Final C F S) {T : Fareway I}{a b r:ℝ}
set_option quotPrecheck false
variable (v:V→ S.Tag)(x:V→ E4) (z:V × Axis) (k:ℕ)(p:Probe S)(g:Ortho) (c:E4)
local notation "Y" => diagonal K p c
local notation "w"=> (Sum.inl (β:=Fin p.length) z.1,z.2)
local notation "W"=> gPlan K p
-- These widths depend on Probe's p.length so implicit
lemma steering : gPlan K p (route K v z k) g= route K (W v g) (Sum.inl (β:= Fin p.length) z.1,z.2) k:=by
    unfold gPlan route; ext1 i; rcases i with i|i <;> dsimp only [Sum.elim_inr,Sum.elim_inl]; swap; · rw [update_of_ne (by simp)] ; rfl
    by_cases he:i=z.1; subst i; simp only [update_self,Sum.elim_inl]; rw [update_of_ne he,update_of_ne (Sum.inl_injective.ne he)]; rfl
lemma swap_places {a t:ℝ} : diagonal K p c (wag x a z t) g=wag (Y x g) a (Sum.inl (β:= Fin p.length) z.1,z.2) t:=by
    unfold diagonal wag; ext1 i; rcases i with i|i
    · simp only [Sum.elim_inl]; by_cases h:i=z.1; subst i; simp only [update_self,Sum.elim_inl]; rw [update_of_ne h,update_of_ne (Sum.inl_injective.ne h)]; rfl
    simp only [Sum.elim_inr, update_of_ne (fun e=>Sum.inr_ne_inl e)]
lemma staring (a t:ℝ)(he:snug c r (wag x a z t))(hv:clearC r p.exterior): HasDerivAt
   (fun q=> a^k • (p.roll K g).tip K (written K c (assembly S (wag x a z q) (route K v z k))))
   (a^(k+1) • (p.roll K g).tip K (written K c (assembly S (wag x a z t) (route K v z (k+1))))) t:=by
     simp_rw [← diag_read, steering,swap_places]; have hp:= diagonal_in K p c g hv he.1 (fun i=>(he.2 i).le); rw [swap_places] at hp; exact starter K (Y x g) (W v g) w k a none t hp
-- curvature of bump through snugs
variable (d:ℕ)
def films (n:ℕ)(a t:ℝ): Palette K d:= a^n • album K c d (assembly S (wag x a z t) (route K v z n))
def drivers (n:ℕ)(a t:ℝ): S.Field d:= a^n • absorb K c d (assembly S (wag x a z t) (route K v z n))
lemma snug_open (a:ℝ): IsOpen {t| snug c r (wag x a z t)} := isOpen_iff_mem_nhds.mpr fun t hx=> snug.at (c:=fun _:ℝ=>c) continuousAt_const (wag_cont x a z).continuousAt hx
lemma displayed_path (he:Frontier6.Safe K d r)(a t:ℝ)(hv:snug c r (wag x a z t))(i:Fin (d+1))(p:(hand K i.val).list)(b:Bool)(g:Ortho): films K v x z c d k a t i p b g=a^k • ((p.val.flip K b).roll K g).tip K (written K c (assembly S (wag x a z t) (route K v z k))):= congr_arg (fun x:ℂ=> a^k • x) ((displayed K (snug.apo K c he hv _)).seats i p b g)
lemma film_deriv (he:Frontier6.Safe K d r)(a t:ℝ)(hv:snug c r (wag x a z t)): HasDerivAt (films K v x z c d k a) (films K v x z c d (k+1) a t) t:=by
    apply hasDerivAt_pi.mpr; intro i; apply hasDerivAt_pi.mpr; intro p; apply hasDerivAt_pi.mpr; intro b
    let U: Set ℝ:={t|snug c r (wag x a z t)}; have hu:IsOpen U:= snug_open x z c a; let f(i':ℕ)(t:ℝ):= films K v x z c d i' a t i p b; let F:= p.val.flip K b
    have hh(n:ℕ): ContinuousOn (films K v x z c d n a) U:= ContinuousOn.const_smul (album_continuous K (q:=fun _:ℝ=>c) he hu continuous_const.continuousOn (wag_cont ..|>.continuousOn) (fun _ hu=>hu) (route K v z n)) (a^n) -- route .. eta needs
    have hp(n:ℕ):ContinuousOn (f n) U:=by specialize hh n; unfold films at hh; exact continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_pi.mp hh i) p) b
    refine derives_roll (hp (k+1)|>.continuousAt (hu.mem_nhds hv)) ?_; filter_upwards [show ∀ᶠ u in 𝓝 t,u∈ U from hu.mem_nhds hv] with t ht g
    have hN:= staring K v x z k F g c a t ht (flip_safe K p.val (he i p) b); refine (hN.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [hu.eventually_mem ht] with e hv using displayed_path K _ _ _ _ _ _ he _ _ hv i p b g
    exact (displayed_path K _ _ _ _ _ _ he _ _ ht i p b g).symm
lemma intoField (a t:ℝ) : drivers K v x z c d k a t= detector K d (films K v x z c d k a t):= by unfold drivers absorb capture films album; rw [ContinuousLinearMap.map_smul_of_tower]
lemma driving (he:Frontier6.Safe K d r)(a t:ℝ)(hv:snug c r (wag x a z t)): HasDerivAt (drivers K v x z c d k a) (drivers K v x z c d (k+1) a t) t:=by
   let L:= (detector K d).restrictScalars ℝ; have hK:drivers K v x z c d k a = L ∘ (films K v x z c d k a):= funext fun i=> intoField K v x z k c d a i; rw [hK,intoField]; exact L.hasFDerivAt.comp_hasDerivAt t (film_deriv K v x z k c d he a t hv)
end YM.Frontier6.Road
