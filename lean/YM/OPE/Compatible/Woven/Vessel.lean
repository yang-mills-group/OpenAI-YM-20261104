import YM.OPE.Compatible.Woven.Tint
/-!
# Every trip exposed. diameter of common root chosen independently of amplitudes. Use all ancestors offsets in `co`; for a single-flight volume grant choose up to full lattice residue. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG Finset Tree Next.Free Bloch Exterior Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier Planned.PrimaryIntegral295.Trellis
open scoped Topology BigOperators Classical
variable {r:ℕ}{L:Side}{η B:ℝ}
def trances (r:ℕ) (i:Fin r): List (Keys r) → List Axis
| []=>[]
| (j,a)::l=>if i=j then a :: trances r i l else trances r i l
lemma tram (l:List (Keys r)): ∑ j,(trances r j l).length=l.length:=by
   induction l with
   | nil=>simp [trances]
   | cons j l ih=>
     rcases j with ⟨j,a⟩; have hx i : (trances r i ((j,a)::l)).length=(trances r i l).length+(if i=j then 1 else 0):= by by_cases hi:i=j<;> simp [trances,hi]
     simp_rw [hx]; rw [sum_add_distrib,ih]; simp
lemma trackPetal (A:Fin r→ Lines L)(a b: Fin r→Axis)(c:Fin r→ Cover)(l:List (Keys r))(ho: Odd L.val):
    dvol l (parcelK A a b c)=parcelK (fun i=> advanceC L (A i) (trances r i l)) a b c:=by
   induction l with
   | nil=>rfl
   | cons i l ih=>
     rcases i with ⟨i,s⟩; rw [dvol,ih]; let P:= (fun i=>advanceC L (A i) (trances r i l)); let Q:= update P i (forwardC L (P i) s); have he: Q=(fun j=> advanceC L (A j) (trances r j ((i,s)::l))) := by
        ext1 j; by_cases hg:j=i<;> simp [Q,P,trances,hg,advanceC]
     ext1 x; ext1 y; exact (petal P _ _ ho i s c x y).trans (congr_arg (fun u=> parcelK u _ _ _ _ _) he)
def horn (η B:ℝ)(n:ℕ)(v:Lines L):= ∀ l:List Axis,l.length ≤ n→(advanceC L v l).strip η (B/(L.val:ℝ)^(1+l.length))
lemma horns (k:ℝ)(hk:0<k) (j t:ℕ) (hj:4 ≤ j)(ht:4 ≤ t) : ∃ σ B : ℝ,0<σ ∧ 0<B∧ ∀ P:Flight j t,horn σ B (j-2) (linesOf P k):= priced k hk hj ht
lemma parcelT {A:Fin r→ Lines L} (a b:Fin r→Axis)(c:Fin r→Cover)(j m:ℕ)(l:List (Keys r))(h:∀ i,horn η B j (A i))(hu:l.length≤j)(ho:Odd L.val)(he:0<η)(x:Bin r): Sack (fun y=> poise m (y-parcelY c L x)) (dvol l (parcelK A a b c) x) ((widthCost η m*B)^r/(L.val:ℝ)^(r+l.length)):=by
    have hp(i:Fin r): (trances r i l).length ≤ j:= (single_le_sum (fun _ _=> Nat.zero_le _) (mem_univ i)).trans ((tram l).trans_le hu)
    rw [trackPetal _ _ _ _ _ ho]; apply (parcel_budget (fun i=> h i (trances r i l) (hp i)) he a b m c x).tips; apply le_of_eq
    simp_rw [← mul_div_assoc]; rw [prod_div_distrib,prod_const, card_univ, Fintype.card_fin,prod_pow_eq_pow_sum];rw [sum_add_distrib,tram,sum_const,card_univ,Fintype.card_fin]; simp
lemma parcel_rescue {A:Fin r→ Lines L} (a b:Fin r→Axis)(c:Fin r→Cover)(j m:ℕ)(l:List (Keys r))(h:∀ i,horn η B j (A i))(hu:l.length≤j)(ho:Odd L.val)(he:0<η)(x:Bin r): Sack (poise m) (dvol l (parcelK A a b c) x) (poise m (parcelY c L x)*((widthCost η m*B)^r/(L.val:ℝ)^(r+l.length))):=by
    let k:= parcelY c L x; let U:= (widthCost η m*B)^r/(L.val:ℝ)^(r+l.length);let f:= dvol l (parcelK A a b c) x
    have hp:= parcelT a b c j m l h hu ho he x; let w i:= poise m (i-k); have hhk:0 ≤ poise m k:= zero_le_one.trans (poise_one m _)
    let t i:= w i* ‖f i‖; have hb: SumBudget (fun i=> poise m k * t i) (poise m k*U):= ⟨fun i=> mul_nonneg hhk (hp.1 _), hp.2.1.mul_left _,by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hp.2.2 hhk⟩
    apply Work.F08.budget_minor hb (fun i=>mul_nonneg (zero_le_one.trans (poise_one m _)) (norm_nonneg _)); intro i; rw [show poise m k*t i=(poise m k*w i)*‖f i‖ from (_root_.mul_assoc ..).symm]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); change poise m i≤ _; conv_lhs=>rw [show i=k+(i-k) by abel]
    exact poise_cumul ..
lemma heft (c:Fin r→Cover)(h:∀ i, size (c i) ≤ 4*L.val)(x:Bin r): (size (parcelY c L x):ℝ) ≤ r*8+size x/(L.val:ℝ):=by
   have hL:0 < (L.val:ℝ):= Nat.cast_pos.mpr L.property
   have he (i:Fin r) : (size (stepOut (parcelY c L x) i):ℝ) ≤ 8+size (stepOut x i)/(L.val:ℝ):=by
       apply (scost (L:=L) (c i + stepOut x i)).trans
       have hu : ((size (c i + stepOut x i)):ℝ)≤size (c i)+ (size (stepOut x i):ℝ):=by exact_mod_cast (size_add ..)
       have hx: (size (c i):ℝ) ≤ 4*(L.val:ℝ):= by exact_mod_cast h i
       unfold unitStep; rw [inv_mul_eq_div]; field_simp; linarith only [hx,hu]
   rw [couple_size x,couple_size (parcelY c L x),Nat.cast_sum,Nat.cast_sum]; apply (sum_le_sum (fun i _=>he i)).trans; rw [sum_add_distrib,← sum_div]; simp
end YM.OPE.Flume
