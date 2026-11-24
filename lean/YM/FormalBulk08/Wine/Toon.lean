import YM.FormalBulk08.Wine.Cab

/-! Reader and coupling normalization. All potential orders reexpressed in
g-coupling variable after kinetic read, not only curvature parts. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wine
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge City Cork
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} (a:hue G) (T : Pot G) {k : ℝ} {j : ℕ} {v:Next.Free.Train j}

def scalar : Pence := PowerSeries.mk fun n=> value a (T n 2)
def normalized := let H:=scalar a T;stamp (bookH H) (bookU H) T

lemma income_sum {I : Type} (S:Finset I) (K:I→Slopes G)(h:∀ i∈S,Purse (K i)):Purse (∑ i∈S,K i)∧ value a (∑ i∈S,K i)=∑ i∈S,value a (K i) := by
   induction S using Finset.induction with
   | empty=> simp only [Finset.sum_empty];exact ⟨⟨1,0,by norm_num,bail_void ..⟩,by simp [value,mir,net,hem]⟩
   | @insert i S he ih=> obtain ⟨hv,Hp⟩:=ih (fun j hj=> h j (Finset.mem_insert_of_mem hj));have hk:=h i (Finset.mem_insert_self ..); rw [Finset.sum_insert he,Finset.sum_insert he,value_add hk hv, Hp];refine ⟨?_,rfl⟩; obtain ⟨s,A,hs,hA⟩:=hv;obtain ⟨t,B,ht,hB⟩:= hk; exact ⟨min s t,_,lt_min hs ht,(hB.shrink (min_le_right ..)).add (hA.shrink (min_le_left ..))⟩
lemma gauge_salary (H U:Pence) (hp:∀ j,Purse (T j 2)): scalar a (stamp H U T)=(scalar a T).subst (X*H)*U^2 := by
   ext1 n; simp only [scalar, coeff_mk]; let S:=scalar a T; let q:=X*H
   have ht: coeff 0 q=0:=by unfold q;rw [coeff_zero_eq_constantCoeff_apply,map_mul];simp
   have h:Through n (S.subst q) ((∑ j∈Finset.range (n+1), C (coeff j S)*X^j : Pence).subst q):= (dict S n).compose (Through.exact_eq _ _) ht
   change value _ _=coeff n (S.subst q*U^2); rw [stamp, (h.mul (Through.exact_eq _ _)).apex,(income_sum a _ _ (fun j _=> ?_)).2]; swap
   · obtain ⟨s,C,hs,hC⟩:=hp j;exact ⟨s,_,hs,hC.smul _⟩
   simp_rw [value_coin]; rw [←coe_substAlgHom (tribe ht),map_sum]; simp_rw [Finset.sum_mul]; rw [map_sum]; apply Finset.sum_congr rfl; intro j hj; rw [coe_substAlgHom, subst_mul (tribe ht),subst_pow (tribe ht),subst_X (tribe ht)]; rw [show PowerSeries.subst q (C (coeff j S))=C (value a (T j 2)) by unfold S;rw [subst_C,scalar,coeff_mk]; rfl]
   rw [show C (value a (T j 2)) * q^j*U^2 = C (value a (T j 2))*(H^j*U^2)*X^j by unfold q;rw [mul_pow];ring, coeff_mul_X_pow',if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), coeff_C_mul]; exact mul_comm ..
lemma sig_mat (h:Story T (Next.Free.pink k v))(hk:0<k)(hj:4≤j): Fresh (scalar a T)∧Still (scalar a T) := by
    refine ⟨?_,fun n hn=> ?_⟩
    · rw [Fresh,scalar,coeff_mk,h.ink,pink_weigh k hk hj]
    have hp: T n 2=0:= by by_contra he; have hx:=h.valence n 2 he; omega
    simp [scalar,hp,value,mir,net,hem]
lemma rulecraft (h:Story T (Next.Free.pink k v))(hk:0<k)(hj:4≤j): Story (normalized a T) (Next.Free.pink k v) ∧ scalar a (normalized a T)=1 := by
    obtain ⟨h₁,h₂⟩:= sig_mat a T h hk hj; constructor
    · exact tale _ _ h (even_book _ h₁ h₂) (even_coupon _ h₁ h₂) (book_fresh _) (book_guard _) (book_equal _)
    simp_rw [normalized];rw [gauge_salary,forward_green,correction_read _ h₁];exact fun i=>h.fare i 2

structure FrameV (T : Pot G) (R: Row (TypeFace 2) (TypeFace 2)) : Prop extends Story T R where
   seals : ∀ e, 0<e → Cork.Null (T e 2)

lemma rulecraft_full (h:Story T (Next.Free.pink k v))(hk:0<k)(hj:4≤j)(hs:G.Simple): FrameV (normalized a T) (Next.Free.pink k v):= by
    obtain ⟨h₁,h₂⟩:=rulecraft a T h hk hj
    refine { h₁ with seals:= fun e he=> direct_nil (splendid h₁ e) hs a ?_ }
    have he:= congr_arg (coeff e) h₂; rwa [scalar,coeff_mk,coeff_one,if_neg (Nat.ne_of_gt ‹_›)] at he
lemma filing (G : Gauge)(k:ℝ)(hk:0<k)(hj:4≤j): FrameV (Enter G) (Next.Free.pink k (Next.Free.Train.top j)):= by
   refine { kingdom G k hk hj with seals:=fun e he=>?_ }
   have hh : Enter G e 2=0:= by unfold Enter; rw [if_pos Nat.zero_lt_two, bend_rank e 2 (by omega)]; simp [deploy_void]
   rw [hh]; constructor <;> intros <;> simp [net,hem,mir]
end YM.FormalBulk08.Wine
