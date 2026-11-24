import YM.RegulatorIR.Halo.Wall
import YM.RegulatorIR.Cluster.Many

/-!
# Top symbol and horizon algebra

Uses real markings (including any real mixing coefficients), no engineering
rescaling or subtractions imposed here. `support` is genuinely finite per
symbol here. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Profiles
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim Finset PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Halo
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{I J X:Type}{r n m p q a b e:ℕ}

abbrev integralPose (V: Orders X) := ∀ i r, Bounded (V i r)
private lemma bound_sum (s:Finset J)(f:J→Packet X r)(h: ∀ i∈s, Bounded (f i)): Bounded (∑ i∈s,f i):=by
 apply Set.Finite.subset (s.finite_toSet.biUnion h); intro z hz; obtain ⟨i,hi,hp⟩:= exists_ne_zero_of_sum_ne_zero (f:=fun i=> f i z) (by simpa only [mem_support, ← Finset.sum_apply] using hz : ∑ i∈s,f i z≠0);exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hp⟩⟩
private lemma bound_untied (A:Packet X p)(B:Packet X q)(h:Bounded A)(H:Bounded B): Bounded (untied A B):=by
 apply ((h.prod H).image (fun z: Tuple X p×Tuple X q=>Fin.append z.1 z.2)).subset; intro x hx; change _*_≠0 at hx; refine ⟨(cutLeft x, cutRight x), ?_, recombine ..⟩; exact ⟨left_ne_zero_of_mul hx,right_ne_zero_of_mul hx⟩
private lemma bound_symmetry (A:Packet X p)(h:Bounded A): Bounded (symmetry A):=by
 have hx (x:Equiv.Perm (Fin p)): Set.Finite (support (A ∘ Tuple.perm _ x)) := Set.Finite.preimage (f:=Tuple.perm _ x) (PermB x) h
 apply Set.Finite.subset (Set.finite_iUnion hx); intro z hz; rw [mem_iUnion]; rw [mem_support, symmetry_at] at hz; obtain ⟨i,_,hp⟩:= Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hz); exact ⟨i,hp⟩
where
 PermB (x:Equiv.Perm (Fin p)) : Set.InjOn (Tuple.perm X x) (Tuple.perm X x ⁻¹' (support A)) := (Tuple.perm X x).injective.injOn

lemma crisp_bounds (V U: Ranked X) (h: ∀ i,Bounded (V i))(H:∀ i,Bounded (U i))(i:ℕ): Bounded (crisp V U i):=bound_sum _ _ (fun z he=> by rw [← Finset.mem_antidiagonal.mp he,pie,dif_pos rfl]; exact bound_symmetry _ (bound_untied _ _ (h _) (H _)))
lemma accord_bounds {V T:Orders X}(h:integralPose V)(H:integralPose T): integralPose (accord V T):=fun _ _=> bound_sum _ _ (fun z _=>crisp_bounds (V z.1) (T z.2) (h z.1) (H z.2) _)
-- lift at arbitrary v (not just bounded v) via a finite carrier
private lemma container {A:Packet X r}(h:Bounded A) : ∃ c: Finset X,∀ L:Finset X,c⊆L→∀ v:X→ℝ,strum A v=strum A (dilute (placeFin L) (v ∘ placeFin L)):=by
 let s:=h.toFinset;let g(t:Tuple X r):= Finset.univ.image t; let C:=s.biUnion g
 refine ⟨C,fun i hi v=>?_⟩; apply tsum_congr; intro z; by_cases hc: A z=0
 · simp [hc]
 apply congr_arg; apply Finset.prod_congr rfl; intro j _
 have hh:z j∈i:= hi (Finset.mem_biUnion.mpr ⟨z,h.mem_toFinset.mpr hc,Finset.mem_image.mpr ⟨_, Finset.mem_univ j,rfl⟩⟩); exact (fill_eq i _ hh v).symm
private lemma contains {V: Ranked X} (h:∀ j,Bounded (V j)) (k:ℕ): ∃ c:Finset X, ∀ L:Finset X,c⊆L→∀ v:X→ℝ,drums V k v=MvPolynomial.eval (v ∘ placeFin L) (packed (fun r=>crop (placeFin L) (V r)) k):=by
 choose S H using fun i=>container (h i); refine ⟨(Finset.range (k+1)).biUnion S,fun L h v=>?_⟩
 apply Eq.trans _ (cheap (v ∘ placeFin L) (placeFin L) V k); apply Finset.sum_congr rfl; intro i hi; exact H i L (Finset.Subset.trans (subset_biUnion_of_mem S hi) h) v

lemma drums_pair {T V:Ranked X}(h: ∀ k,Bounded (T k))(H:∀ k,Bounded (V k))(x:X→ℝ)(ht: Within a T)(hz:Within b V): drums (crisp T V) (a+b) x=drums T a x*drums V b x:=by
 obtain ⟨L,hL⟩:= contains h a; obtain ⟨M,hM⟩:= contains H b; obtain ⟨R,hR⟩:= contains (crisp_bounds T V h H) (a+b)
 let U:Finset X:= L∪M∪R;let F:= placeFin U
 rw [hL U (Finset.Subset.trans (subset_union_left ..) (subset_union_left ..)), hM U (Finset.Subset.trans (subset_union_right ..) (subset_union_left ..)), hR U (subset_union_right ..)]
 rw [show (fun r=> crop F (crisp T V r))=crisp (fun r=>crop F (T r)) (fun r=>crop F (V r)) from funext (fun i=>crop_crisp F T V i),crisp_packed _ _, MvPolynomial.eval_mul]
 · intro i hi; exact ht i (fun h'=> hi (by dsimp only; rw [h'];rfl))
 intro i hi; exact hz i (fun h'=> hi (by dsimp only; rw [h'];rfl))

private lemma drums_sum (s: Finset I)(T:I→Ranked X) (h:∀ i∈s,∀ j, Bounded (T i j))(x:X→ℝ)(k:ℕ): drums (∑ i∈s,T i) k x= ∑ i∈s,drums (T i) k x:=by
 unfold drums; rw [sum_comm (s:=s)]; apply sum_congr rfl; intro j _; unfold strum; simp_rw [Finset.sum_apply,sum_mul]; exact Summable.tsum_finsetSum (fun i hi => summable_of_hasFiniteSupport (show (support (fun z:Tuple X j=>T i j z*noodle x z)).Finite from (h i hi j).subset (fun z hz=>left_ne_zero_of_mul hz)))

lemma shelter_pair {V U:Orders (Foot G)} (x:Foot G→ℝ)(h:integralPose V)(H:integralPose U)(hp:Ranks a V)(hx:Ranks b U): shelter (a+b) (accord V U) x=shelter a V x*shelter b U x:=by
 ext i; rw [coeff_mul,shelter,coeff_mk,accord_order, drums_sum]; swap; exact fun p hp j=> crisp_bounds (V p.1) (U p.2) (h p.1) (H p.2) _
 apply sum_congr rfl; intro z he; rw [shelter,shelter, coeff_mk,coeff_mk]; have hh:= mem_antidiagonal.mp he; change drums (crisp _ _) _ _= _; rw [show i+(a+b)=(z.1+a)+(z.2+b) by omega]; exact drums_pair (h _) (H _) x (hp _) (hx _)

variable {A B: Portrait G}
lemma joint (h:Person A)(H: Person B): Person (A*B) :=⟨h.cap.mul H.cap, fun t U g=> congr_arg₂ (·*·) (h.guise t U g) (H.guise t U g), fun b U hh hb hv hu=> (h.neat b U hh hb hv hu).mul (H.neat b U hh hb hv hu)⟩
attribute [local instance] Gauge.frobInner
lemma Person.live (h:Halo.Person A)(v:Foot G→ℝ) : ContDiffAt ℝ ∞ (outing G A v) 0:=by
 refine h.neat (fun i=>i) (fun i:ℝ=>win G (i • v)) ?_ contDiffAt_id rfl ?_
 · intro i; unfold win; simp_rw [timbers,Pi.smul_apply]; exact (G.exp_jet.contDiffAt.of_le le_top).comp _ (contDiffAt_id.smul contDiffAt_const)
 rw [zero_smul]; ext1 i; change G.lieExp (0:G.Color)=1; simp
lemma BasisT.united {T V:Orders (Foot G)} (h:Halo.BasisT a p A T)(H:Halo.BasisT b q B V)(hv:Ranks a T)(hp:Ranks b V): Halo.BasisT (a+b) (p+q) (A*B) (accord T V):=by
 refine ⟨joint h.origin H.origin, accord_bounds h.canopy H.canopy,accord_sym _ _,fun w=>?_⟩
 rw [show outing G (A*B) w=outing G A w *outing G B w from rfl,tale_mul (Person.live h.origin w) (Person.live H.origin w), h.pose,H.pose,pow_add, shelter_pair w h.canopy H.canopy hv hp]; ring
variable (K:Composite I)(B:I→ Portrait G) {m s: I→ℕ} {T:I→Orders (Foot G)}
def Gather (K:Composite I)(B:I→ Portrait G) : Portrait G:=match K with
 | .atom i=>B i
 | .pair a b=>Gather a B*Gather b B
lemma Person.compound (hv:∀ i,K.In i→ Halo.Person (B i)): Halo.Person (Gather K B):=by induction K with
 | atom i=> exact hv i rfl
 | pair a b ih ih'=> exact joint (ih (fun i hi=> hv i (Or.inl hi))) (ih' (fun i hi=> hv i (Or.inr hi)))
lemma BasisT.given (h:∀ i,K.In i→Halo.BasisT (m i) (s i) (B i) (T i))(he:∀ i,K.In i→Ranks (m i) (T i)): Halo.BasisT (K.accounts m) (K.accounts s) (Gather K B) (K.product T):=by
 induction K with
 | atom i=> exact h i rfl
 | pair a b ih ih'=>
    have hh:= ih (fun i hi=>h i (Or.inl hi)) (fun i hi=>he i (Or.inl hi)); have hx:= ih' (fun i hi=>h i (Or.inr hi)) (fun i hi=>he i (Or.inr hi)); exact BasisT.united hh hx (a.ranks T (fun i hi=>he i (Or.inl hi))) (b.ranks T (fun i hi=>he i (Or.inr hi)))
end YM.RegulatorIR.Profiles
