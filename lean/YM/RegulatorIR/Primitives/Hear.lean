import YM.RegulatorIR.Primitives.Polar
import YM.RegulatorIR.Primitives.Earth
import YM.RegulatorIR.Quadratic.Chute

/-!
Read an infinite-alphabet (locally supported) chart event, curve symmetry and
extensionality including on orbit. Needs genuine germ as a rooted VERTEX,
not a story of connected reports. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Prim
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory MvPolynomial Cluster Diagram Quadratic
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff
variable {I J:Type}{k a b r:ℕ}

def noodle (v:I→ℝ)(z:Tuple I r):=∏ i,v (z i)
def strum (T:Packet I r)(v:I→ℝ):= ∑' z:Tuple I r,T z*noodle v z
def drums (T:Ranked I)(k:ℕ)(v:I→ℝ) := ∑ i∈Finset.range (k+1),strum (T i) v
variable (v:I→ℝ)(w:J→ℝ) (T: Packet I r)(F:J↪I)
lemma pluck [Fintype I] : strum T v=MvPolynomial.eval v (render T):=by unfold strum; rw [tsum_fintype];exact play ..
lemma speaking [Fintype I] (T:Ranked I)(k:ℕ): drums T k v= MvPolynomial.eval v (packed T k):=by unfold drums packed; rw [map_sum]; simp_rw [pluck]
lemma ample (T:Packet J r) : strum (offer F T) v= strum T (v ∘ F):=by
 unfold strum; rw [← (injectT F).tsum_eq]
 · simp_rw [offer_eq];rfl
 intro i h; by_contra hx; apply h; change offer F T i*_=0; rw [offer_zero _ hx,zero_mul] -- rw h?
lemma flute [Fintype J] (Q:Ranked J): drums (fun r=>offer F (Q r)) k v=MvPolynomial.eval (v ∘ F) (packed Q k):=by unfold drums; simp_rw [ample];exact speaking ..

lemma crops (T:Packet I r) : strum T (dilute F w)= strum (crop F T) w:=by
 unfold strum; rw [← (injectT F).tsum_eq]; apply tsum_congr; intro z; exact congr_arg (fun h:ℝ=>T (acrossT F z)*h) (Finset.prod_congr rfl fun i _=>dilute_here ..)
 intro i h; have hp (k:Fin r):∃ j:J,F j=i k:=by
    by_contra! hx;apply h; change T i*_=0; apply mul_eq_zero_of_right; exact Finset.prod_eq_zero (Finset.mem_univ k) (dilute_miss F w (i k) (fun hh=> by obtain ⟨z,hz⟩:=hh;exact hx _ hz))
 choose g hg using hp; exact ⟨g,funext hg⟩
lemma cheap [Fintype J] (T:Ranked I)(k:ℕ): drums T k (dilute F w)= MvPolynomial.eval w (packed (fun r=>crop F (T r)) k):=by unfold drums; simp_rw [crops]; exact speaking ..

-- even for nonlocal T. ext if all linear responses on arbitrary finitely-supported fields.
lemma guessed {T U:Ranked I}(h:Within k T)(hh:Within k U)(ht:Satin T)(hu:Satin U)(he:∀ i:I→ℝ,drums T k i=drums U k i) : T=U :=by
 ext1 r; by_cases hp:k<r
 · rw [show T r=0 from Classical.not_not.mp (fun hv=>(not_le.mpr hp) (h r hv)),show U r=0 from Classical.not_not.mp (fun hv=>(not_le.mpr hp) (hh r hv))]
 ext1 i; let R: Finset I:= Finset.univ.image i; let f: (↥R) ↪ I := Function.Embedding.subtype (· ∈ R)
 let A:=fun r=> crop f (T r);let B:=fun r=>crop f (U r)
 have hx : packed A k= packed B k:= MvPolynomial.funext (fun v=> by unfold A B;rw [← cheap,← cheap]; exact he _)
 have hm:r∈Finset.range (k+1):=Finset.mem_range.mpr (by omega)
 have ha:= identified (A r) (B r) (crop_symm f _ (ht r)) (crop_symm f _ (hu r)) ((Diagram.isolate A hm).symm.trans ((congr_arg (homogeneousComponent r) hx).trans (Diagram.isolate B hm)))
 exact congr_fun ha (fun j:Fin r=>⟨i j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _, rfl⟩⟩)

lemma starts (T:Ranked I): drums T k (0:I→ℝ)=T 0 Fin.elim0:=by
 unfold drums; rw [Finset.sum_eq_single_of_mem 0 (by simp)];
 · unfold strum; rw [tsum_eq_single Fin.elim0]; simp [noodle]; intro i hi; exact (hi (Subsingleton.elim ..)).elim
 intro i _ he; cases i
 · contradiction
 simp [strum,noodle]

-- support and act

def Bounded (T:Packet I r):Prop:= (Function.support T).Finite
lemma bound_offer [Fintype J] (T:Packet J r): Bounded (offer F T):=by refine (Set.finite_range (acrossT (r:=r) F)).subset (fun x hx=> Classical.not_not.mp fun hv=> hx (offer_zero _ hv))
lemma bound_cost {T:Packet I r}(h:Bounded T) : quota T 1≠⊤:=by rw [quota_base, tsum_enorm_ne_top_iff_summable_norm]; exact (summable_of_hasFiniteSupport h).norm
lemma strum_zero : strum (0:Packet I r) v=0:=by simp [strum]
lemma strum_tilt (c:ℝ): strum (c • T) v=c*strum T v:=by unfold strum; change (∑'z:Tuple I r, c*T z *_ )= _;simp_rw [mul_assoc,tsum_mul_left]
lemma strum_v (c:ℝ):strum T (c • v)=c^r* strum T v:=by
 unfold strum; rw [← tsum_mul_left]; apply tsum_congr;intro x; simp [noodle,smul_eq_mul,Finset.prod_mul_distrib];ring
lemma strum_perm (D:I≃J) (T:Packet J r):strum T w = strum (fun z=>T (D ∘ z)) (w ∘ D):=by
 unfold strum; rw [← (Equiv.piCongrRight (fun _:Fin r=>D)).tsum_eq]; rfl

section Historic
variable {P:ℝ} (A:Deck P I J)
variable [Fintype J]
-- orbit pick is one tensorial argument. any direct source, no invariance.
omit [Fintype J] in
lemma helix {T:Packet I r}(h:Bounded T):strum (A.scroll T) w=strum T (bridge A w):=by
 let U (x:Tuple I r):= T x*noodle (bridge A w) x
 have hs:Summable U:= summable_of_hasFiniteSupport (Set.Finite.subset h (by intro x hx; contrapose! hx; change ¬U x≠0; simp only [not_not]; unfold U; rw [Function.notMem_support.mp hx];ring))
 unfold strum; change _=∑'x,U x;rw [← Stalk.collected_sum A.project hs];apply tsum_congr;intro x;unfold scroll Stalk.collect;rw [← tsum_mul_right];apply tsum_congr;intro i
 change _=T i.val*noodle (bridge A w) _
 rw [← show noodle w (A.project i.val)=noodle w x from congr_arg (noodle w) i.property] -- type depends?
 unfold dyed noodle bridge; simp_rw [Finset.prod_mul_distrib]; rw [mul_assoc]; rfl
lemma high_ink (W:Ranked I) (h:∀ i,Bounded (W i)) : MvPolynomial.eval w (packed (fun i=>A.scroll (W i)) k)=drums W k (bridge A w):=by rw [← speaking];unfold drums;simp_rw [fun i=> helix w A (h i)]
end Historic
end YM.RegulatorIR.Prim
