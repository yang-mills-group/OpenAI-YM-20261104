import YM.XSpace.Moor

/-!
# Local Ward effect and radial replacement on OpenCaps
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Lows
open Function Filter Set Scale Mu Lattice Finsupp MvPolynomial Next.Rank.Normal Contraction Trace Chart2 Prelude
open scoped Topology BigOperators ContDiff
variable {G:Gauge} {d k:ℕ}

-- hat derivatives. turn $v$ in upgrade readouts at L state. needed structural (independent of the alternate Ward shell resolution).
variable (B Q:Hat G d)
def slide: Module.End ℂ (Cap G d):=(slit (fun i:Index G d=> (((bank G d).repr B i:ℝ):ℂ))).toLinearMap
local instance ticker (G:Gauge)(d:ℕ): SMul ℝ (Hat G d):= Module.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
theorem tilting (p: Cap G d) : HasDerivAt (fun t:ℝ=>view (B+(t • Q : Hat G d)) p) (view B (slide Q p)) 0:=by
  let f(t:ℝ)(i:Index G d):ℂ:= ((bank G d).repr (B+(t • Q : Hat G d)) i:ℝ); change HasDerivAt (fun t=>aeval (f t) p) _ _; have he:= slit_shift f 0 (fun i=> (((bank G d).repr Q i:ℝ):ℂ)) (?_) p
  · dsimp only [f] at he; rw [zero_smul,add_zero] at he; exact he
  intro i; simp only [f,map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]; push_cast; simpa only [zero_add,Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using! (hasDerivAt_const (0:ℝ) ((((bank G d).repr B) i:ℝ):ℂ)).add (((Complex.ofRealCLM).hasDerivAt (x:=(0:ℝ))).mul_const ((((bank G d).repr Q) i:ℝ):ℂ))
lemma elevated (P:Stamp G)(a:ℝ): view B (slide Q (scale a (overture d P)))= pit (scenic d (orchestra d a B)) (D (scenic d (orchestra d a Q)) P):=by
  have ht:= tilting B Q (scale a (overture d P)); simp_rw [scaled,music_at,map_add,map_smul] at ht; exact ht.unique (Chart2.directional ..)

-- maps acting diagonally on letter grades, with polynomial actions preserving weight. use even for some convergence at moving scales (but not changing basis per order)
variable {B Q}
def day (L:∀ i:Fin (d+1), Module.End ℝ (Tune i.val G.Color)): Module.End ℝ (Hat G d):= LinearMap.pi fun i=> (L i) ∘ₗ LinearMap.proj i
def cross (L:Module.End ℝ (Hat G d)) : Cap G d→ₐ[ℂ] Cap G d:= MvPolynomial.aeval fun i=> Audio ((bank G d).coord i ∘ₗ L)
lemma crossing (p:Cap G d)(L:Module.End ℝ (Hat G d))(v:Hat G d): view v (cross L p)=view (L v) p :=by
  suffices h: (view v).comp (cross L)=view (L v) from DFunLike.congr_fun h p; ext1 i; rw [AlgHom.comp_apply,cross,aeval_X,audio_at,view,aeval_X]; rfl
-- grade by commutation with all c::d. criterion recurs.
lemma unique_height (p:Cap G d)(h:∀ c:ℝ,c≠0→ scale c p=(c:ℂ)^k • p): IsWeightedHomogeneous coin p k:=by
  have he (n:ℕ): (scale (2:ℝ) p)= (2:ℂ)^k • p:=by simpa using h 2 (by norm_num)
  have hp:∀ i:ℕ,i≠k→ Cut coin i p=0:=by
    intro i hi
    have hx: (2:ℂ)^k≠ (2:ℂ)^i := by
      intro he; have he: (2:ℝ)^k=(2:ℝ)^i:= by exact_mod_cast he
      exact hi (((pow_right_strictMono₀ (show (1:ℝ)<2 by norm_num)).injective he).symm)
    have ht:= scale_saves 2 p i; rw [he 0,map_smul] at ht; norm_num at ht; exact (smul_eq_zero.mp (show ((2:ℂ)^k-(2:ℂ)^i) • Cut coin i p=0 by rw [sub_smul,ht,sub_self])).resolve_left (sub_ne_zero.mpr hx)
  obtain ⟨n,H⟩:=cap_known coin p; have he':= trunc_eq (w:=coin) (n:=max n k) (p:=p) (higher coin (le_max_left _ _) H)
  suffices h: Cut coin k p=p by rw [← h]; exact weightedHomogeneousComponent_mem ..
  unfold trunc at he'; rw [LinearMap.sum_apply, Finset.sum_eq_single k (fun x hx h=>hp x h) (by intro h; rw [Finset.mem_range] at h; omega)] at he'; exact he'
lemma budgets (L: Module.End ℝ (Hat G d))(h:∀ c:ℝ,∀ v:Hat G d,L (orchestra d c v)=orchestra d c (L v))(p:Cap G d)(s:ℕ):Cut coin s (cross L p)=cross L (Cut coin s p):=by
  apply Maxwell.Free.commuting; intro i; apply unique_height; intro c hv; apply sameCap; intro X; rw [scaled,crossing,h, currency,map_smul,crossing];rfl
variable (G d) in
def radial: Module.End ℝ (Hat G d):= day (G:=G) fun i=> Scale.assay i.val
lemma radial_saves (a:ℝ)(v:Hat G d):radial G d (orchestra d a v)= orchestra d a (radial G d v):= by ext1 i; exact map_smul (Scale.assay _) _ _
lemma radial_keeps (p:Cap G d)(k):cross (radial G d) (trunc coin k p)=trunc coin k (cross (radial G d) p):=by unfold trunc; rw [LinearMap.sum_apply,_root_.map_sum,LinearMap.sum_apply]; exact Finset.sum_congr rfl fun _ _=> (budgets (radial G d) radial_saves p _).symm
lemma scale_trunc (p:Cap G d)(a:ℝ)(k:ℕ): scale a (trunc coin k p)=trunc coin k (scale a p):=by unfold trunc; rw [LinearMap.sum_apply, _root_.map_sum,LinearMap.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; change _=Cut coin i _; rw [scale_saves, scalable a (weightedHomogeneousComponent_mem coin p i)]

abbrev gen (v:Fin (d+1)) (L:Litter.Stamp (v.val+1) G.Color) : Hat G d:= Pi.single v (pipes L)
lemma echoes (p: Fin (d+1))(v:Litter.Stamp (p.val+1) G.Color)(a:ℝ) : scenic d (orchestra d a (gen p v))=grad (blast v a):=by
  rw [Drama.scenic_break]; rw [Finset.sum_eq_single p]
  · change _ • release (gen p v p).val= _; rw [gen,Pi.single_eq_same]; unfold blast; rw [← notated,map_smul,show release (pipes v).val= _ from blown v,Nat.add_comm 1]
  · intro i _ h; rw [gen,Pi.single_eq_of_ne h]; change _ • release (0: Vase i.val G.Color)= _; simp
  simp
lemma gen_rotate (p: Fin (d+1))(v:Litter.Stamp (p.val+1) G.Color) : radial G d (gen p v)=0:=by
  have he (n:ℕ)(L : Litter.Stamp (n+1) G.Color): Scale.assay n (pipes L)=0:=by cases n <;> unfold assay; simp; rw [LinearMap.comp_apply, Scale.quiet,map_zero]
  ext1 i; change assay i.val _=_; rw [LinearMap.proj_apply,gen]; by_cases h:i=p; subst i; rw [Pi.single_eq_same]; apply he
  rw [Pi.single_eq_of_ne h,map_zero]; rfl

lemma fade (p:Cap G d)(h:∀ X:Hat G d,∀ i (U:Litter.Stamp (i.val+1) G.Color), view X (slide (gen i U) p)=0): cross (radial G d) p=p:=by
  apply sameCap; intro A; rw [crossing]; let v:= radial G d A
  have hh (i:Fin (d+1)) (U:Litter.Stamp (i.val+1) G.Color)(B:Hat G d): view B p=view (B+gen i U) p:=by
    let f (s:ℝ):= view (B+(s • gen i U: Hat G d)) p
    have he(x:ℝ): HasDerivAt f 0 x:=by
      have he:= tilting (B+(x • gen i U:Hat G d)) (gen i U) p; rw [h] at he; have ht:= he.scomp_of_eq x ((hasDerivAt_id' x).sub_const x) (sub_self x).symm
      rw [one_smul] at ht; rw [show f=((fun t:ℝ=> view (B+x • gen i U+t • gen i U) p) ∘ fun y => y-x) from ?_]; exact ht; funext t; unfold f; apply congr_arg (fun x=>view x p); rw [show ∀ t:ℝ,((t-x) • gen i U:Hat G d)=t • gen i U-x • gen i U from fun t=> sub_smul t x (gen i U)]; abel
    have hz:= is_const_of_deriv_eq_zero (fun x=>(he x).differentiableAt) (fun x=>(he x).deriv) 0 1; simpa only [f,zero_smul,one_smul,add_zero] using hz
  choose B hB using fun i:Fin (d+1)=>assayed (A i); have he: A=v+∑ i,gen i (B i):=by funext i; simp only [Pi.add_apply,Finset.sum_apply]; rw [Finset.sum_eq_single i]; rw [gen, Pi.single_eq_same]; exact hB i; intro j _ h; exact Pi.single_eq_of_ne (Ne.symm h) _; simp
  have hp (s:Finset (Fin (d+1))): view v p=view (v+∑ i∈s,gen i (B i)) p:=by induction s using Finset.induction_on with | empty=>simp | insert i s hi ih=> rw [ih,Finset.sum_insert hi,add_left_comm,add_comm (gen i (B i)), ← hh]
  change view v p=_; rw [hp Finset.univ,← he]
end YM.XSpace.Lows
