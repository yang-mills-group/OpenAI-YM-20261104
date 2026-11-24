import YM.XSpace.Nebula
/-!
# Flat costs and literal lattice-side point input
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Cirrus
open Filter Set Function Metric Lattice Expense Stall Structure1 Normalize Asymptotics PowerSeries Comets Probes Foundation Future
open scoped Topology BigOperators Classical
variable {G:Gauge} (W:Initialize G){n:ℕ}(d:ℕ)(i:Sample n)(z:Points n){j:Fin n→ℕ}
abbrev chartV (q: Sample n) := wrap q.F.p.side ∘ q.layout
-- arbitrary locations are priced but later Gate sense, always θ lifts

def litP (p:Mesh)(x:Fin n→p.Sites)(k:ℕ): Point G d n := ∑ r:Fin n→ Fin (d+1), (PowerSeries.coeff k).compMultilinearMap ((W.atTuple p (fun i=>(r i).val) x).compLinearMap fun i=> Normalize.part d (r i))
abbrev live (k:ℕ) := litP W d i.F (chartV i) k
lemma lite (k:ℕ)(p:Mesh)(x: Fin n → p.Sites)(t:Tags G d n) : litP W d p x k t=∑ r:Fin n→ Fin (d+1), coeff k (W.atTuple p (fun i=>(r i).val) x (fun i=> Normalize.part d (r i) (t i))) :=by simp only [litP,sum_apply]; rfl
variable (p: ∀ i,HP G (j i))(h:∀ i,j i ≤ d)
lemma lives (k:ℕ): live W d i k (shells j p h)= coeff k (W.atTuple i.F j (chartV i) p):=by
  let u (a:Fin n):Fin (d+1):= ⟨j a,Nat.lt_add_one_iff.mpr (h a)⟩; rw [live,lite, Finset.sum_eq_single_of_mem u (Finset.mem_univ _)]; change coeff k (W.atTuple i.F j _ (fun i=> Normalize.part d (j i) (en _ _)))=_; simp_rw [part_same]; intro b _ hb; obtain ⟨x,hx⟩:=Function.ne_iff.mp hb; rw [MultilinearMap.map_coord_zero (i:=x) _ (part_other _ (fun h=>hx (Fin.ext h)) _), map_zero]
lemma around (p:Mesh)(x: Fin n→ p.Sites)(f:∀ i, HP G (j i)) : PowerSeries.constantCoeff (W.atTuple p j x f)= (p.spacing:ℂ)⁻¹ ^ degree j * PowerSeries.constantCoeff (Bare.normalized (W.tree p.p) G (∏ i,Bare.raw (W.tree p.p) (sections W j i) (x i) (resetV W j f i).val)):=by
  rw [W.atTuple_eq]; let F (i:Fin n):= Bare.column (W.tree p.p) (sections W j i) (x i) (Price.preparedL (f i)); let z:ℂ:=(p.spacing:ℂ)⁻¹
  have hs (s:Finset (Fin n)): (∏ i∈s,W.atSite p _ (x i) (f i))=z^(∑ i∈s,j i) • ∏ i∈s,F i :=by
    induction s using Finset.induction_on with
    | empty=> simp
    | insert i s hi ih=> rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.sum_insert hi,pow_add, mul_smul,ih, show W.atSite p _ (x i) (f i)=z^(j i) • F i from ?_,smul_mul_assoc,mul_smul_comm]
                         rw [Initialize.atSite,LinearMap.smul_apply,inv_pow]; rfl
  rw [hs,map_smul]; unfold F; simp_rw [Bare.column_formula]; simp_rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, map_smul]; rfl

abbrev Bloom (f:Sample n→ℂ):= Cross.Blank (Gate z) grab f
omit p h in
lemma Bloom.room {v:Sample n→ℂ}(h:Bloom z v)(u:ℕ): Bloom z (fun i=> (unit i:ℂ)⁻¹ ^ u * v i):=by
  intro k; obtain ⟨C,hC⟩:= (h (u+k)).bound; -- API
  apply IsBigO.of_bound C; filter_upwards [hC] with i hi; rw [norm_mul,norm_pow,norm_inv,Complex.norm_real, Real.norm_of_nonneg (unit_pos i).le, Real.norm_of_nonneg (pow_pos (actual ..) _).le]; rw [Real.norm_of_nonneg (pow_pos (actual ..) _).le] at hi
  apply (mul_le_mul_of_nonneg_left hi (by positivity [unit_pos i])).trans_eq; change (unit i)⁻¹^u * (C*unit i^(u+k))= C*unit i^k; have hx:=unit_pos i; rw [pow_add,inv_pow]; field_simp
lemma grade_initial : Bloom z fun i=> (live W d i 0-blossom0 W d (unit i) i.layout) (shells j p h):=by
  let U i:= (resetV W j p i).val; let o:= Sample.layout (n:=n); let r:= (fun i:Sample n=>border i); have he:= Encore.zeroFlat (sections W j) U Finset.univ _ (sprawl z) o home ?_ (fun i=> W.tree i.F.p); swap
  · refine ⟨1,r,(foundation z).mono fun i hi=> ⟨hi,fun j=> Finset.le_sup (s:=Finset.univ) (f:=fun j=> Sail.reach (charts i j)) (Finset.mem_univ j)⟩,?_⟩; obtain ⟨C,hC,H⟩:= bordered z; simp_rw [pow_one]; exact IsBigO.of_bound C (H.mono fun i hi=> by rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity [actual grab i])]; exact hi)
  simp_rw [sub_apply,lives W d _ _ h, PowerSeries.coeff_zero_eq_constantCoeff_apply,blossoms, around,stage_book]; intro w
  exact ((Bloom.room z he (degree j)) w).congr_left fun i=> (mul_sub ..)
lemma grade_positive : Bloom z fun i=> (live W d i 1-replied W (unit i) i.layout d) (shells j p h):=by simp_rw [sub_apply, lives W d _ _ h,raw1]; exact Probes.blank W j p Sample.layout (sprawl z) home (overhang z)
lemma assemble_blank (V: Sample n → Point G d n) (h:∀ (j:Fin n→ℕ) p (h:∀ i,j i≤d), Bloom z (fun i=>V i (shells j p h)))(p:Tags G d n): Bloom z fun i=>V i p:=by simp_rw [calls (V _) p]; intro k; exact IsBigO.sum (fun j _=> h _ _ _ k)
theorem landscape0 (t:Tags G d n): Bloom z fun i=> (live W d i 0-blossom0 W d (unit i) i.layout) t:=assemble_blank d z _ (fun _=> grade_initial W d z) t
theorem landscape1 (t:Tags G d n): Bloom z fun i=> (live W d i 1-replied W (unit i) i.layout d) t:=assemble_blank d z _ (fun _=> grade_positive W d z) t
lemma Bloom.spends {v:Sample n→ℂ}(h:Bloom z v): Tendsto v (Gate z) (𝓝 0):=by have hh:=h 1; simp_rw [pow_one] at hh; exact hh.trans_tendsto (sprawl z).endpt
end YM.XSpace.Cirrus
