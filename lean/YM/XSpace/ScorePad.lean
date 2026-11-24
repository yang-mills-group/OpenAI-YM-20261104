import YM.XSpace.Keyway

/-!
# Smooth (to finite or many orders) lattice supplies on moving areas

Cost auto-constrained by normalization at remote marks; proofs obtaining at e.g.
first-order correlator assembly in a separate file. Work coefficientwise; Studio
records eventual controls on all fixed differences with genuine radii.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Scale
open Lattice Sail Tensor Litter Function Filter Set
open scoped Topology ContDiff BigOperators
variable {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F]{d:ℕ}{G:Gauge}
abbrev Organ (d:ℕ)(F:Type*)[NormedAddCommGroup F][NormedSpace ℝ F]:=(i:Fin (d+1))→Tune i.val F
def packets (d:ℕ)(n:Axis): Folder d F →ₗ[ℝ] Series d F:=LinearMap.pi fun i:Fin (d+1)=> (LinearMap.proj n) ∘ₗ LinearMap.proj i
lemma casts (i:Axis)(u: Folder d F):twig i (castBlaze u)=act (half i) (packets d i u):=by unfold castBlaze act; rw [LinearMap.sum_apply,LinearMap.sum_apply,map_sum]; rfl

def rawPack : Organ d F →ₗ[ℝ] Folder d F:=LinearMap.pi fun i:Fin (d+1)=> (motif i.val F).subtype ∘ₗ LinearMap.proj i
def scenic (d:ℕ): Organ d F→ₗ[ℝ] Tape F:= castBlaze ∘ₗ rawPack
lemma scenes (d:ℕ)(u:Organ d F): press (scenic d u)=0 := (similar _).2 fun i=>(u i).property
lemma seen (d:ℕ)(u: Organ d F)(i:Axis):twig i (scenic d u)=act (half i) (fun j=>(u j).val i):= casts i (rawPack u)
lemma past (d:ℕ): Injective (scenic d (F:=F)):=by
  intro x y h; funext i; apply Subtype.ext; funext j; apply congr_fun (punch (half j) (by rw [← seen d x j, ← seen d y j,h]) ) i

def project (n:ℕ) : Vase n F →ₗ[ℝ] Tune n F:= by
  exact LinearMap.leftInverse (K:=ℝ) (V:=Tune n F) (V':=Vase n F) (motif n F).subtype
lemma projects (n:ℕ)(u:Tune n F):project n u.val=u:=by
  change LinearMap.leftInverse (K:=ℝ) (V:=Tune n F) (V':=Vase n F) (motif n F).subtype _=_; exact LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _)) _
def collect: Folder d F →ₗ[ℝ] Organ d F:=LinearMap.pi fun i:Fin (d+1)=>project i.val ∘ₗ LinearMap.proj i
lemma center (u:Folder d F)(h: press (castBlaze u)=0): rawPack (collect u)=u:= by funext i; exact congr_arg Subtype.val (projects i.val ⟨u i,(similar u).1 h i⟩)

def meter (d:ℕ)(c:ℝ): Module.End ℝ (Folder d F):= LinearMap.pi fun i:Fin (d+1)=> (c^(1+i.val)) • LinearMap.proj i
def orchestra (d:ℕ)(c:ℝ): Module.End ℝ (Organ d F):= LinearMap.pi fun i:Fin (d+1)=> (c^(1+i.val)) • LinearMap.proj i
lemma orchestra_at (u:Organ d F)(c:ℝ)(i:Fin (d+1)): orchestra d c u i= c^(1+i.val) • u i:=rfl
lemma inverse_meter (d:ℕ)(c:ℝ)(h:c≠0)(u: Organ d F): orchestra d c (orchestra d c⁻¹ u)=u:= by funext j; rw [orchestra_at,orchestra_at,inv_pow, smul_inv_smul₀ (pow_ne_zero _ h)]
lemma projected (u:Folder d F)(c:ℝ):collect (meter d c u)=orchestra d c (collect u):=funext fun i=> map_smul (project i.val (F:=F)) _ _
lemma amounted (u:Folder d F)(c:ℝ)(i:Axis): packets d i (meter d c u)= invest c 1 (packets d i u):= rfl
variable [FiniteDimensional ℝ F]

def extract (d:ℕ): Tape F →ₗ[ℝ] Folder d F:= LinearMap.pi fun i:Fin (d+1)=> LinearMap.pi fun j:Axis => LinearMap.proj i ∘ₗ showTime (half j) d ∘ₗ twig j
lemma pack (d:ℕ)(i:Axis)(u:Tape F): packets d i (extract d u)=showTime (half i) d (twig i u):= rfl
def gather (d:ℕ): Tape F→ₗ[ℝ] Organ d F:= collect ∘ₗ extract d

open Asymptotics
variable {ι:Type*} {L:Filter ι} {w a:ι→ℝ} {r:ι→ℕ}

-- ker comparison, since cost specified pointwise at arbitrarily many but fixed addresses
private lemma known {Z X E:Type*} [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ X]
    (W: X→ₗ[ℝ] (Z→F))(D:X→ₗ[ℝ] E) (H:∀ x,W x=0→D x=0)(u:ι→X)(h:∀ z:Z,(fun i=> W (u i) z)=O[L] w) : (fun i=> D (u i))=O[L]w:=by
  classical
  let V (s: Finset Z): X→ₗ[ℝ] (s→F):=LinearMap.pi fun i:s=> (LinearMap.proj i.val) ∘ₗ W
  let K (s: Finset Z):= LinearMap.ker (V s)
  let p (n:ℕ):= ∃ s: Finset Z,Module.finrank ℝ (K s)=n
  have ht :∃ n,p n:= ⟨_,∅,rfl⟩
  obtain ⟨s,hs⟩ := (show p (Nat.find ht) from Nat.find_spec ht)
  have he (i:Z) : K (insert i s) = K s:= by
    apply Submodule.eq_of_le_of_finrank_le
    · intro x h; apply (show V s x=0→ _ from id); funext z; exact congr_fun (show V (insert i s) x=0 from h) ⟨z,Finset.mem_insert_of_mem z.property⟩
    rw [hs]; exact Nat.find_min' ht (show p _ from ⟨(insert i s),rfl⟩)
  let Q:= V s; have hx (x:X)(h:Q x=0): D x=0:= H x (funext fun i=> congr_fun (show V (insert i s) x=0 from (show x∈ K (insert i s) from (he i).symm ▸ (show x∈ K s from h))) ⟨i,Finset.mem_insert_self ..⟩)
  obtain ⟨P,hP⟩ := Q.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr (LinearMap.surjective_rangeRestrict _))
  let R:=Q.rangeRestrict; have hh(x:X): D x=(D ∘ₗ P) (R x):= sub_eq_zero.mp ((map_sub D x (P (R x))).symm.trans (hx _ (by rw [map_sub]; exact sub_eq_zero.mpr (congr_arg Subtype.val (LinearMap.congr_fun hP (R x))).symm)))
  simp_rw [hh]; exact ((LinearMap.toContinuousLinearMap (D ∘ₗ P)).isBigO_comp (fun i=>R (u i)) L).trans (IsBigO.of_norm_left (show (fun i=>Q (u i))=O[L]w from isBigO_pi.mpr fun i:s=> h i.val).norm_left)

/-- k derivatives cost `1+k` potential units (ordzero physical length). -/
structure Studio (L:Filter ι)(a:ι→ℝ)(r:ι→ℕ)(A:ι→Tape F): Prop where
  lives : Tendsto r L atTop
  ground : ∀ x:Edge Cover, ∀ᶠ i in L, press (A i) x=0
  loans (k:ℕ) : ∃ C:ℝ,0≤C∧∀ᶠ i in L,∀ x:Cover, reach x≤r i→∀ l:List Axis,l.length=k→∀ j:Axis, ‖crack l (twig j (A i)) x‖ ≤ C*(a i)^(1+k)

namespace Studio
variable {A:ι→Tape F} (K:Studio L a r A) (he:∀ᶠ i in L, 0≤a i)
include he K
private lemma fixes (k:ℕ)(j:Axis)(x:Cover): (fun i=> twig j (A i-castBlaze (extract k (A i))) x) =O[L] fun i=>a i^(k+2):=by
  obtain ⟨C,hC,H⟩:=K.loans (k+1); apply IsBigO.of_bound ((4*(reach x:ℝ))^(k+1)*C)
  filter_upwards [H, he,K.lives.eventually_ge_atTop (reach x)] with i hi hv hh
  rw [map_sub,casts,pack]; have hs:=sole_price (half j) (twig j (A i)) (C*(a i)^(1+(k+1))) (by positivity) (r i) (fun l h x hx=>hi x hx l h j) [] (Nat.zero_le _) x hh; change ‖_‖ ≤ (4*(reach x:ℝ))^(k+1)*C*‖_‖; apply le_trans hs; rw [Real.norm_of_nonneg (pow_nonneg hv _), List.length_nil, Nat.sub_zero, mul_assoc, show 1+(k+1)=k+2 by omega]
private lemma press_price (k:ℕ)(x:Edge Cover): (fun i=> press (castBlaze (extract k (A i))) x)=O[L] fun i=> a i^(k+2):=by
  let D i := A i-castBlaze (extract k (A i)); let t i := a i^(k+2); let w:=x.1; let j:= x.2
  have hu (p:Edge Cover):(fun i=> D i p)=O[L]t:= K.fixes he k p.2 p.1
  have hx (y:Cover)(l:Axis): (fun i=> crackle l j (D i) y)=O[L]t:= ((hu (y+step l,j)).sub (hu (y,j))).sub ((hu (y+step j,l)).sub (hu (y,l)))
  have hv : (fun i=> -press (D i) x) =O[L] t:= IsBigO.neg_left (by
    simp_rw [show ∀ i,press (D i) x= ∑ l:Axis,rat l (crackle l j (D i)) w from fun i=>(congr_fun (job (D i) j) w).trans (Finset.sum_apply ..)]
    exact IsBigO.sum (fun l _=> (hx (w-step l) l).sub (hx w l)))
  apply hv.congr' _ (EventuallyEq.refl ..); filter_upwards [K.ground x] with i hi; show -press (D i) x=_; unfold D; rw [map_sub,Pi.sub_apply,hi]; abel
lemma bill (k:ℕ): (fun i=>extract k (A i)-rawPack (collect (extract k (A i)))) =O[L] fun i=>a i^(k+2):= known ((press (F:=F)) ∘ₗ castBlaze) ((LinearMap.id (R:=ℝ) (M:=Folder k F)) - rawPack ∘ₗ collect) (fun x h=> sub_eq_zero.mpr (center x h).symm) (fun i=>extract k (A i)) (K.press_price he k)
lemma rehearsed (l:List Axis)(j:Axis)(h:l.length≤d+1): ∃ C:ℝ, 0≤C∧∀ᶠ i in L, ∀ x:Cover, reach x ≤ r i →
    ‖crack l (twig j (A i-scenic d (gather d (A i)))) x‖ ≤ C*a i^(d+2)*(1+(reach x:ℝ))^(d+1-l.length):=by
  let R i:= packets d j (extract d (A i)-rawPack (collect (extract d (A i))))
  obtain ⟨P,hP,H⟩:= K.loans (d+1); obtain ⟨Q,hQ,V⟩:= (((LinearMap.toContinuousLinearMap (packets (F:=F) d j)).isBigO_comp _ L).trans (K.bill he d)).exists_pos
  obtain ⟨B,hB,G⟩:= sole_walk (F:=F) (half j) d l; let m:=d+1-l.length
  refine ⟨4^m*P+B*Q,by positivity,?_⟩; filter_upwards [he,H,V.bound] with i hi hv hx; let a':=a i; intro x hx'; let b:ℝ:= reach x; have hz:0≤b:=Nat.cast_nonneg _; change ‖R i‖ ≤ Q*‖a'^(d+2)‖ at hx; rw [Real.norm_of_nonneg (pow_nonneg hi _)] at hx
  have hy: twig j (A i-scenic d (gather d (A i)))=twig j (A i)-act (half j) (showTime (half j) d (twig j (A i))) + act (half j) (R i):=by rw [map_sub]; unfold R; rw [map_sub,map_sub,pack]; rw [show scenic d _= castBlaze _ from rfl,casts]; unfold gather; rw [LinearMap.comp_apply]; abel
  have hp:= sole_price (half j) (twig j (A i)) (P*a'^(1+(d+1))) (by have ht:0≤a':=hi; positivity) (r i) (fun l h x hx=>hv x hx l h j) l h x hx'; rw [show 1+(d+1)=d+2 by omega] at hp
  rw [hy, ← peaked,map_add,Pi.add_apply,peaked,peaked]; apply le_trans ((norm_add_le ..).trans (add_le_add hp (G (R i) x))); rw [add_mul,add_mul]; apply add_le_add
  · calc
      _ ≤ (4*(1+b))^m*(P*a'^(d+2)):=by
        gcongr (4*?_)^_ * _; exact le_add_of_nonneg_left zero_le_one
      _ = _ :=by rw [mul_pow]; unfold m b a'; ring
  change B*‖R i‖*(1+b)^(d-l.length) ≤ _; calc
    _ ≤ B*(Q*a'^(d+2))*(1+b)^m:= by
      gcongr B*?_ * _ ^ ?_ ; · linarith
      unfold m; omega
    _ = _ :=by unfold m b a'; ring
end Studio
end YM.XSpace.Scale
