import YM.FVA2.Stencil

/-!
# Coupling and external operator powers

Scalar formal parameters use `Book.Convolve`, as in MS. A lower cap on the rank
allows unambiguous coupling substitution *after* dividing by the external
Laurent power. A finite join/merit calculation will thus need k+d rows to give
k orders if no such division has yet been made. -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2
open Function Set Filter Lattice MS MS.Koszul MS.Swirl MS.Native MS.Orbit MS.Orbit.Cog
open MS.Orbit.LogReal MS.Bare MS.Cylinder MS.Cylinder.Taylor MS.Puff MS.Puff.Mom MS.Book
open MS.Book.Convolve MS.Swirl.Near MS.Cylinder.Lab MS.Native.Wilsonian MS.Book.Program
open MS.Puff.Engine MS.Puff.Actors MS.Puff.SplitP MS.Book.Program
open PertExtension PertExtension.Orb Substitute Matrix
open scoped Classical Topology ContDiff
namespace Coupling
variable {A Q : Type}[AddCommGroup A][Module ℂ A]
-- scalar actions, comm with any Wick.Include unit.
abbrev Sc := T ℂ
abbrev multiple : Sc→ₗ[ℂ] T A →ₗ[ℂ] T A:= pairW (LinearMap.lsmul ℂ A)
local infixr:70 " •𝕡 " => multiple
local infixl:60 " ♠ " => Trunk.core
local notation "T0" => Trunk.unit
lemma waveRight (F:Sc)(X:T A)(i:ℕ): (F •𝕡 X) i=∑ j∈Finset.antidiagonal i, F j.1 • X j.2:= rfl
lemma waveS (F:Sc)(X:Sc): F •𝕡 X= F ♠ X := rfl
lemma multipleK (F:T A) : T0 •𝕡 F=F:= by
    funext i; rw [waveRight,Finset.sum_eq_single_of_mem (0,i) (by simp), show (T0) (0,i).1 = 1 from if_pos rfl,one_smul]
    intro j hj hx; rw [show (T0) j.1=0 from if_neg (fun h=>hx (Prod.ext (show j.1=0 from h) (by have : j.1=0:=h; obtain hh:=Finset.mem_antidiagonal.mp hj; dsimp; omega))),zero_smul]
lemma filter_m (F:Sc)(X:T A)(V:A→ₗ[ℂ] A) : promote V (F •𝕡 X)=F •𝕡 (promote V X):= by funext i; simp_rw [promised,waveRight,map_sum,map_smul,promised]
lemma filter_r {B:Type}[AddCommGroup B][Module ℂ B] (F:Sc)(X:T A)(V:A→ₗ[ℂ] B) : promote V (F •𝕡 X)=F •𝕡 (promote V X):= by funext i; simp only [promised,waveRight,map_sum,map_smul]
lemma starTrunk (a b : Sc) : a ♠ b=b ♠ a := by funext i; exact useN.also (fun j k=> a j*b k) i|>.trans (Finset.sum_congr rfl (fun j _=>mul_comm ..))
lemma via {A B C:Type}[AddCommGroup A][Module ℂ A][AddCommGroup B][Module ℂ B][AddCommGroup C][Module ℂ C]
    (L:A→ₗ[ℂ] B→ₗ[ℂ] C)(p:T A)(q:T B)(X:Sc) : pairW L p (X •𝕡 q)= X •𝕡 (pairW L p q):= by
    funext i; rw [paired, waveRight]; simp only [LinearMap.lsmul_apply,map_sum,paired,Finset.smul_sum,map_smul]
    rw [associate (fun k u v=> X u • L (p k) (q v)), associate (fun u k v => X u • L (p k) (q v))]; apply Finset.sum_congr rfl; intro j hj; exact useN.also (fun a b => X b • L (p a) (q j.2)) j.1
lemma viaL {A B C:Type}[AddCommGroup A][Module ℂ A][AddCommGroup B][Module ℂ B][AddCommGroup C][Module ℂ C]
    (L:A→ₗ[ℂ] B→ₗ[ℂ] C)(p:T A)(q:T B)(X:Sc) : pairW L (X •𝕡 p) q= X •𝕡 (pairW L p q):= by rw [flips,via, ← flips L]
lemma repeatedS (p q:Sc)(X:T A) : p •𝕡 (q •𝕡 X)= (p ♠ q) •𝕡 X:= by
    funext i; simp_rw [waveRight,Finset.smul_sum,← waveS, waveRight,Finset.sum_smul]
    simp_rw [smul_smul]; exact associate (fun i j k=> (p i * q j) • X k) i

-- g^d operations represented by shifted rows. needed to compare to Orb.
omit [Module ℂ A] in
def liftg (x:ℕ) (F:T A) (i:ℕ):= if x ≤ i then F (i-x) else 0
omit [Module ℂ A] in
lemma undo (x:ℕ): Injective (liftg (A:=A) x):= by
    intro f g h; funext i; simpa [liftg] using congr_fun h (i+x)

def powerg (d:ℕ) : Sc:= fun i=> if d=i then 1 else 0
lemma rolls_g (x:ℕ)(F:T A): powerg x •𝕡 F=liftg x F:= by
    funext i; rw [waveRight]
    unfold powerg liftg; split
    next he=>
       rw [Finset.sum_eq_single_of_mem (x,i-x) (by simp [he]), if_pos rfl,one_smul]
       intro j hj hp; rw [if_neg (show x≠j.1 from fun h=>hp (Prod.ext h.symm (by obtain hh:=Finset.mem_antidiagonal.mp hj; dsimp; omega))),zero_smul]
    next he=> refine Finset.sum_eq_zero fun j hj=> ?_; rw [ if_neg (show x≠j.1 from fun h=>by obtain hh:=Finset.mem_antidiagonal.mp hj; omega),zero_smul]
lemma powers_mask (F:Raw Q ℂ)(r:ℕ)(h:From F r): liftg r (rankLevel r F)=rankLevel 0 F:= by
    funext i; unfold liftg rankLevel; split
    next he=> congr 2; omega
    next he=> funext l; by_cases ht:(l.length:ℤ)=(i:ℤ)+0; rw [enough _ ht,h l (by omega)]; rfl; exact (strange l ht).symm
omit [Module ℂ A] in
def cutg (d:ℕ)(F:T A)(i:ℕ):= F (i+d)
omit [Module ℂ A] in
lemma lift_low {F:T A}{d:ℕ}(h : ∀ i,i<d→ F i=0) : liftg d (cutg d F)=F:= by funext i; unfold liftg cutg; split_ifs with he; rw [Nat.sub_add_cancel he]; exact (h i (Nat.lt_of_not_ge he)).symm

-- dividing normalization through cutoff
lemma supplied_zero (F X : Sc) (hx:F 0=1) {b:ℕ} {P:T ℂ} (hp:F ♠ X=liftg b P) : ∀ i,i<b→ X i=0:= by
    intro i; induction i using Nat.strong_induction_on with
    | h i IH=>
       intro ht; have hk:=congr_fun hp i
       rw [liftg,if_neg (by omega)] at hk; change ∑ j ∈ Finset.antidiagonal i,F j.1*X j.2=0 at hk
       rw [Finset.sum_eq_single_of_mem (0,i) (by simp)] at hk; simpa [hx] using hk
       intro j hj hz; rw [ IH j.2 ?_ ?_,mul_zero] <;> obtain hh:= Finset.mem_antidiagonal.mp hj
       · have hu : j.1≠0:= fun h=> hz (Prod.ext h (by dsimp; omega)); omega
       omega
section Wick
variable [Fintype Q] (K:Matrix Q Q ℂ) (p : Sector Q)
set_option quotPrecheck false
local infixl:70 " ⋄ "=> (PermV p).core
local notation "E"=> exp0 p
local notation "C"=> ℶV K

omit [Fintype Q] in
lemma act_q (F:Sc)(V P:SpecB Q): P ⋄ (F •𝕡 V)= F •𝕡 (P ⋄ V):= via (product p) ..
omit [Fintype Q] in
lemma act_l (F:Sc)(V P:SpecB Q): (F •𝕡 P) ⋄ V= F •𝕡 (P ⋄ V):= viaL (product p) ..
lemma meanS (F:Sc)(V:SpecB Q): C (F •𝕡 V)= F ♠ (C V):= filter_r F V (View K)
lemma buys {G F:SpecB Q} {Y:Sc}(X:Sc)(he:Endμ K p G F Y): Endμ K p G (X •𝕡 F) (X ♠ Y):= by unfold Endμ; rw [act_q p X,meanS]; change _ = C (E G) ♠ (X ♠ Y); rw [he, ← Trunk.star_a,starTrunk X, Trunk.star_a]
lemma divide_E {G F:SpecB Q}{Y:Sc}(d:ℕ)(h:G 0=0)(hp:Endμ K p G (liftg d F) Y):
    (∀ i,i<d → Y i=0) ∧ Endμ K p G F (cutg d Y) := by
    have hu : C (E G) ♠ Y = liftg d ( C ( E G ⋄ F )) := by
       rw [← hp, ← rolls_g, ← rolls_g, act_q, meanS, waveS]
    have hv:= supplied_zero _ _ (yetB h) hu; refine ⟨hv, Eq.symm ( undo d ?_ )⟩; change liftg d ( C (E G) ♠ cutg d Y)= _
    calc
       _ = C (E G) ♠ Y := by rw [ ←rolls_g,waveS, ← Trunk.star_a,starTrunk (powerg d), Trunk.star_a, ← waveS (powerg d), rolls_g,lift_low hv]
       _ = _ := hu
end Wick

-- coupling substitution is *the same* in vertices and external powers.
variable (φ:Cn) (hφ: Rooted φ)
local notation "τ"=> substitute φ
lemma start_T (M:Actors A) : (τ) ((M.stack useN).unit)=(M.stack useN).unit := by
    let U: T A:= (M.stack useN).unit
    have ht(i:ℕ)(hp:i≠0): U i=0:= if_neg hp
    funext i; by_cases he:i=0
    · subst i; exact pay0 ..
    rw [rules,Finset.sum_eq_single_of_mem 0 (by simp), cut, pow_zero,PowerSeries.coeff_one, if_neg]; change _= U i; rw [zero_smul,ht i he]; exact he -- sign
    intro j _ hh; rw [show (M.stack useN).unit j=0 from ht j hh,smul_zero]
include hφ
lemma functorG (M:Actors A) : Puff.Tether τ (M.stack useN) (M.stack useN):= ⟨ start_T φ M,fun f g=> (substitute_pair hφ f g M.core).symm⟩
lemma reindex (p:Sector Q)(F: SpecB Q)(h:F 0=0): τ (exp0 p F)=exp0 p (τ F) := by
    funext i; let M:= actor p; let S:=M.stack useN;
    have ht (j:ℕ)(hj:j∈ Finset.Iic i): exp0 p F j= S.cheers F i j:= (M.overbook useN F h (show useN.grade j ≤ i from Finset.mem_Iic.mp hj)).symm
    rw [rules]; rw [Finset.sum_congr rfl (fun j hj=> congr_arg (cut φ j i • ·) (ht j hj))]
    change τ (S.cheers F i) i=S.cheers (τ F) i i
    rw [(functorG φ hφ M).cheersV]
lemma γη [Fintype Q](p:Sector Q)(K:Matrix Q Q ℂ){G F:SpecB Q}(h:G 0=0){Y:Sc} (hp:Endμ K p G F Y): Endμ K p (τ G) (τ F) (τ Y):= by
    unfold Endμ
    rw [← reindex φ hφ p G h,← (functorG φ hφ (actor p)).craft]; -- defeq
    have he(X:SpecB Q): ℶV K (τ X)=τ (ℶV K X):= Program.comm φ X (View K)
    rw [he,he,hp,(functorG φ hφ Toy).craft]
end Coupling
end YM.FVA2
