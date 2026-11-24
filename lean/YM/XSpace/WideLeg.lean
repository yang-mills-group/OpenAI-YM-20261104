import YM.XSpace.ResiduePole
import YM.Next.RANK.GaussLeg
import YM.Next.RANK.GaussTags
/-!
# Globally posted Maxwell Wick vertices. Derivation calculus
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal Maxwell Maxwell.Free ProbeLine MvPolynomial
open scoped Topology BigOperators InnerProductSpace ContDiff Classical Polynomial
variable {G : Gauge}

abbrev WebKey (G : Gauge):= E4× Slot G
abbrev Web (G : Gauge):= poly (WebKey G)
def net (G: Gauge): Normal.Symmetric (WebKey G):= ⟨fun i j=> if i.1=j.1 then 0 else Maxwell.Wick.entry i.2 j.2 i.1 j.1, fun i j=> by
  by_cases h:i.1=j.1; · rw [if_pos h,if_pos h.symm]
  rw [if_neg h,if_neg (Ne.symm h)]; exact Maxwell.Wick.entry_symmetric _ _ h⟩

abbrev WW (G:Gauge):= Normal.blend (net G) 0

def factors (x:E4) {n:ℕ} (p:Probe G n) := post x (Maxwell.symbol n p)
def singleF (x:E4)(a:Flavor 0)(i:G.ColorIndex):= factors x (flavor (G:=G) 0 i a)
def signFor (x y:E4)(a b:Flavor 0) (G:Gauge) := ∑ i:G.ColorIndex, singleF x a i*singleF y b i
lemma signTeam (x:E4)(a b:Flavor 0)(G:Gauge): signFor x x a b G=post x (team G a b):= by unfold signFor team; simp only [map_sum,map_mul]; rfl
lemma singleLin (x:E4) (c:G.ColorIndex):∃ F: Flavor 0→ₗ[ℝ] Web G, (fun p=> F p)=(fun p=>singleF x p c):= by
  obtain ⟨L,H⟩:= symbol_linear (G:=G) 0; refine ⟨((post x).toLinearMap.restrictScalars ℝ).comp (L.comp (flavor 0 c)),?_⟩; funext p; unfold singleF factors; rw [← H]; rfl
lemma signForms (x y:E4)(G:Gauge): ∃ F: Flavor 0→ₗ[ℝ] Flavor 0 →ₗ[ℝ] Web G, ∀ p q,F p q= signFor x y p q G:= by
  choose L h using fun c:G.ColorIndex=> singleLin x c
  choose J v using fun c:G.ColorIndex=> singleLin y c
  let Y (c:G.ColorIndex) := (LinearMap.mul ℝ (Web G)).compl₁₂ (L c) (J c)
  refine ⟨∑ c,Y c,fun p q=>?_⟩; unfold signFor
  rw [LinearMap.sum_apply, LinearMap.sum_apply]; exact Finset.sum_congr rfl fun i _=> congr_arg₂ (·*·) (congr_fun (h i) p) (congr_fun (v i) q)

lemma identify_leg {x y:E4} {j k : ℕ} (hx:x≠y) (a:Probe G j)(b:Probe G k):
    ∑ i, ∑ v, a (Maxwell.frame G j i)*b (Maxwell.frame G k v)*legKernel (coordinateLeg ⟨j,i⟩) (coordinateLeg ⟨k,v⟩) (x-y)=legKernel a b (x-y):= by
  let L:= pairing (j:=j) (l:=k) (G:=G) (show x-y∈away from sub_ne_zero.mpr hx)
  have he (n:ℕ)(a:Probe G n) : a= ∑ i, a (Maxwell.frame G n i) • coordinateLeg ⟨n,i⟩ := by
    apply (Maxwell.frame G n).ext; intro v; simp [coordinateLeg]
  change _= L a b; conv_rhs=> rw [he j a,he k b, map_sum (L)]
  rw [LinearMap.sum_apply]; apply Finset.sum_congr rfl; intro i _; rw [map_sum]; apply Finset.sum_congr rfl; intro t _; simp only [map_smul, LinearMap.smul_apply,smul_eq_mul]; rw [mul_assoc]; exact mul_left_comm ..

-- actual mark derivative due to edge from posting x

def limbs (x:E4){j :ℕ}(p:Probe G j):WebKey G →₀ ℂ := ∑ i:Fin (legDim G j), Finsupp.single (x,⟨j,i⟩) (↑(p (Maxwell.frame G j i)):ℂ)
lemma strokes (x:E4){j:ℕ}(p:Probe G j): factors x p=glyph (limbs x p):= by
  unfold factors Maxwell.symbol; simp only [glyph,limbs,map_sum,Finsupp.linearCombination_single,map_smul, post_X,C_mul']

def form (x:E4){j:ℕ}(p:Probe G j):= Finsupp.linearCombination ℂ (net G).cov (limbs x p)
def scrape (x:E4) (p:Flavor 0) (i:G.ColorIndex):= Normal.slit (form x (flavor 0 i p))

lemma remainder_eqn {x y:E4}{j k:ℕ}(p:Probe G j)(q:Probe G k): slit (form x p) (factors y q)= MvPolynomial.C (if x=y then 0 else (↑(legKernel p q (x-y)):ℂ)):= by
  rw [strokes]; have he (z : WebKey G →₀ ℂ) : slit (form x p) (glyph z) = C (Finsupp.linearCombination ℂ (form x p) z) := by
    simp only [glyph,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,(slit (form x p)).map_smul,slit_X,smul_eq_mul,map_mul,C_mul']
  rw [he]; apply congr_arg; simp only [form,limbs,map_sum,Finsupp.linearCombination_single,Finset.sum_apply,Pi.smul_apply,net,smul_eq_mul]
  by_cases h:x=y; · simp [h]
  simp only [if_neg h,Wick.entry]
  rw [← identify_leg h p q]; simp only [Complex.ofReal_sum,Complex.ofReal_mul]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
lemma through_eqn {x y:E4}(hx:x≠y){k:ℕ}(p:Flavor 0)(q:Flavor k)(c i v:G.ColorIndex):
    scrape x p i (factors (G:=G) y (flavor k v q))= MvPolynomial.C (if v=i then (fare c p q (x-y):ℂ) else (0:ℂ)) := by rw [scrape, remainder_eqn,if_neg hx, any_ink c p q _ _ (sub_ne_zero.mpr hx)]; by_cases h:v=i <;> simp [*,Ne.symm]

lemma WW_scalar {V:Type*}(K:Normal.Symmetric V) (p:poly V)(x:ℂ): Normal.blend K 0 (MvPolynomial.C x*p)=x*Normal.blend K 0 p:=by rw [C_mul',map_smul];rfl
lemma WW_leg (x:E4){n:ℕ}(p:Probe G n)(v:Web G): WW G (factors x p*v)= WW G (slit (form x p) v):=by
  unfold WW; rw [blend_components,strokes,Normal.refresh]; simp only [map_add,map_mul]
  rw [show aeval (0:WebKey G→ℂ) (glyph (limbs x p))=0 by simp [limbs],zero_mul,zero_add,Normal.skims];rfl
lemma WW_double (x:E4)(p:Flavor 0)(v:Web G): WW G (post x (team G p p)*v)= ∑ i:G.ColorIndex,WW G (scrape x p i (scrape x p i v)):=by
  unfold team; rw [map_sum,Finset.sum_mul,map_sum]; apply Finset.sum_congr rfl; intro i _
  rw [_root_.map_mul (post x)]; change WW G (factors x _* factors x _*v)= _; rw [mul_assoc,WW_leg, Derivation.leibniz (slit _) (factors ..) v, smul_eq_mul,remainder_eqn,if_pos rfl,map_zero,smul_zero,add_zero,WW_leg]; rfl

lemma readings {n:ℕ}(x:Points n)(hx:x∈conf _)(p:Fin n→ WickPol G): Wick.moment G x p= WW G (∏ i, post (x i) (p i)):=by
  let m (i:Fin n×Slot G) := (x i.1,i.2)
  have he : rename m (∏ i, post i (p i))=∏ i, post (x i) (p i):= by
    rw [map_prod]; unfold post; exact Finset.prod_congr rfl fun i _=> by rw [rename_rename]; rfl
  rw [← he,labelled,WW,wets]; rw [Wick_reads]
  rw [show scope _ (net G)=frameX hx from ?_, show Normal.reads (fun i=> Finsupp.single (m i) 1) 0=0 from _root_.funext fun i=> Finsupp.linearCombination_zero_apply ..]; rfl
  apply Normal.Symmetric.ext; funext i j; rw [Normal.match_name]; simp only [net,frameX,m,(show Injective x.ofLp from hx).eq_iff]
end YM.XSpace.Stab
