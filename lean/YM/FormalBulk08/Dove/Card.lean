import YM.FormalBulk08.Dove.Tares

/-! Price across a variable but finite number of substitutions. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {Z Λ:Type}{p E:ℕ}
-- g=g0*b. Next g is substituted by `b'`.

def propel (S U:Pence):Pence:=U*S.subst (X*U)
lemma fuel_fresh {S T:Pence}(h:Fresh S)(p:Fresh T): Fresh (propel S T):=p.mul (by rw [Wine.Fresh,peep (by simp only [coeff_zero_eq_constantCoeff_apply,map_mul,constantCoeff_X,zero_mul]),h])
lemma invited (h:Pence)(V:Pence): propel (nextU h) (propel (bookH h) V)=V ∧ propel (bookH h) (propel (nextU h) V)=V := by
    have hp (P S:Pence): X*propel P S= PowerSeries.subst (X*S) (X*P) := by
        have hu:coeff 0 (X*S)=0:=by rw [coeff_zero_eq_constantCoeff_apply,map_mul,constantCoeff_X,zero_mul]
        rw [propel,subst_mul (tribe hu),subst_X (tribe hu),mul_assoc]
    have ht : coeff 0 (X*V)=0:=by rw [coeff_zero_eq_constantCoeff_apply,map_mul,constantCoeff_X,zero_mul]
    constructor <;> apply mul_left_cancel₀ (a:=(X:Pence)) X_ne_zero <;> simp_rw [hp,forward_green,show X * nextU h=wake h from rfl]
    · rw [←subst_comp_subst_apply (tribe (runic_phi h)) (tribe ht), back_merge, subst_X (tribe ht)]
    rw [←subst_comp_subst_apply (tribe (wake_phi h)) (tribe ht),front_merge,subst_X (tribe ht)]
variable {τ:Time Z}{δ:Z→ℝ}{T U S Q:Z→Pence}
lemma transit (ht:Priced τ δ T U p): Priced τ δ (fun i=>X * T i) (fun i=> X * U i) (p+1) := by
    intro j hj; cases j with
    | zero=>simp_rw [coeff_zero_eq_constantCoeff_apply,map_mul,constantCoeff_X,zero_mul];apply Pact.coin
    | succ j=>simp_rw [coeff_succ_X_mul];apply ht j (by omega)
lemma no_time (h:Priced τ δ T U p)(he:Priced τ δ S Q (p+1))(hs:∀ i,Fresh (S i))(ht:∀ i,Fresh (Q i)): Pact τ δ (fun i=> coeff (p+1) (propel (S i) (T i))-coeff (p+1) (T i)) (fun i=> coeff (p+1) (propel (Q i) (U i))-coeff (p+1) (U i)):= by
    have hu (S:Pence): coeff 0 (X*S)=0:= by simp [coeff_zero_eq_constantCoeff_apply]
    have hp:=he.by_order (transit h) (fun i=>hu (T i)) (fun i=>hu (U i)); let F:=(Finset.antidiagonal (p+1)).erase (p+1,0)
    have hh (S U:Pence)(h:Fresh S): coeff (p+1) (propel S U)-coeff (p+1) U= ∑ i∈F,coeff i.1 U*coeff i.2 (S.subst (X*U)):= by
       rw [propel,coeff_mul,←Finset.add_sum_erase _ _ (a:=(p+1,0)) (by simp),peep (hu U),h,mul_one]; simp only [F,add_sub_cancel_left]
    simp_rw [hh _ _ (hs _),hh _ _ (ht _)]; apply pact_sums _;intro x hx; obtain ⟨v,e⟩:=Finset.mem_erase.mp hx;rw [Finset.mem_antidiagonal] at e;exact (h x.1 (by rcases x; simp at v;omega)).times (hp _ (by omega))
structure Lengths (s:Z→ℕ) where
    z:Z
    i:ℕ
    endD:i≤ s z
structure Walk (s:Z→ℕ) where
    z:Z
    i:ℕ
    away:i < s z
variable {s:Z→ℕ}
abbrev tbook (T:Time Z)(s:Z→ℕ): Time (Lengths s):= T.reach (·.z)
abbrev tcash (T:Time Z)(s:Z→ℕ):Time (Walk s):= T.reach (·.z)
def stubW (i:Walk s):Lengths s:= ⟨i.z,i.i,i.away.le⟩
lemma sum_soft {f:Z→ℕ→ℝ}(h:Soft (tcash τ s) (fun i=> f i.z i.i))(he:Soft τ (fun i=>(s i:ℝ))): Soft (tbook τ s) (fun i=>∑ k∈Finset.range i.i,f i.z k):= by
    obtain ⟨B,n,hb,H⟩:=h; have ht:= he.times ((soft_coin τ B).times ((soft_day τ).pows n)); refine (ht.reach (fun i:Lengths s=>i.z)).below (fun i=>?_)
    refine le_trans (Finset.abs_sum_le_sum_abs ..) ?_; have hx:(∑ k∈Finset.range i.i, |f i.z k|) ≤ ∑ _k∈Finset.range i.i,B*(τ.day i.z)^n:= Finset.sum_le_sum fun j v=> H ⟨i.z,j,(Finset.mem_range.mp v).trans_le i.endD⟩
    refine le_trans hx ?_; simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; exact (mul_le_mul_of_nonneg_right (show (i.i:ℝ) ≤ (s i.z:ℝ) by exact_mod_cast i.endD) (mul_nonneg hb (pow_nonneg (τ.good _) _))).trans (le_abs_self _)
lemma sum_faint {f:Z→ℕ→ℝ}(h:Faint (tcash τ s) (fun i=>δ i.z) (fun i=>f i.z i.i))(he:Soft τ (fun i=>(s i:ℝ)))(hp:∀ i,0≤δ i): Faint (tbook τ s) (fun i=>δ i.z) (fun i=>∑ k∈Finset.range i.i,f i.z k):= by
    obtain ⟨C,⟨B,n,hb,A⟩,c,H⟩:= h; have ht:= he.times ((soft_coin τ B).times ((soft_day τ).pows n)); refine ⟨_,ht.reach (fun i:Lengths s=>i.z),fun i=>?_,fun i=>?_⟩
    · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hb (pow_nonneg (τ.good _) _))
    let v:= B*(τ.day i.z)^n; have hv:0≤ v:=mul_nonneg hb (pow_nonneg (τ.good _) _); refine le_trans (Finset.abs_sum_le_sum_abs ..) ?_; have hx: (∑ k∈Finset.range i.i, |f i.z k|) ≤∑ _k∈Finset.range i.i,v*δ i.z:= by
       apply Finset.sum_le_sum; intro k hk; let j: Walk s:=⟨i.z,k,(Finset.mem_range.mp hk).trans_le i.endD⟩; exact (H j).trans (mul_le_mul_of_nonneg_right ((le_abs_self (C j)).trans (A j)) (hp _))
    refine le_trans hx ?_; simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show (i.i:ℝ) ≤ (s i.z:ℝ) by exact_mod_cast i.endD) hv) (hp _)
lemma sum_priced {f g:Z→ℕ→ℝ} (h:Pact (tcash τ s) (fun i=>δ i.z) (fun i=> f i.z i.i) (fun i=>g i.z i.i))(he:Soft τ (fun i=>(s i:ℝ)))(hp:∀ i,0≤δ i) : Pact (tbook τ s) (fun i=>δ i.z) (fun i=>∑ k∈Finset.range i.i, f i.z k) (fun i=>∑ k∈Finset.range i.i,g i.z k):= by
    refine ⟨sum_soft (f:=f) h.left he,sum_soft (f:=g) h.right he,?_⟩; convert sum_faint (f:=fun x i=> f x i - g x i) h.blur he hp using 1; ext;simp [Finset.sum_sub_distrib]
lemma rolls {T U S V:Z→ℕ→Pence}(hv:∀ i:Walk s, T i.z (i.i+1)=propel (S i.z i.i) (T i.z i.i))(hh:∀ i:Walk s,U i.z (i.i+1)=propel (V i.z i.i) (U i.z i.i))(he:Soft τ (fun i=>(s i:ℝ)))(hp:∀ i,0≤ δ i)
     (a:∀ i: Walk s,Fresh (S i.z i.i))(b:∀ i: Walk s,Fresh (V i.z i.i))(hx:Priced τ δ (fun i=>T i 0) (fun i=>U i 0) E)(hl: Priced (tcash τ s) (fun i=>δ i.z) (fun i=>S i.z i.i) (fun i=> V i.z i.i) E): Priced (tbook τ s) (fun i=>δ i.z) (fun i=> T i.z i.i) (fun i=> U i.z i.i) E:= by
    intro k hk; induction k using Nat.strong_induction_on with
    | _ k ih=>
       let f (T:Z→ℕ→Pence) (x) (i:ℕ):= coeff k (T x (i+1))-coeff k (T x i)
       have H(P:Z→ℕ→Pence)(i:Lengths s): coeff k (P i.z i.i)= coeff k (P i.z 0)+ ∑ l∈Finset.range i.i,f P i.z l:= by unfold f; rw [Finset.sum_range_sub (fun l=>coeff k (P i.z l))];ring
       have hu:(fun (i:Lengths s)=>coeff k (T i.z i.i))= _ := funext fun i=>H T i
       rw [hu,show (fun i:Lengths s=> coeff k (U i.z i.i))=_ from funext fun i=> H U i]; refine ((hx k hk).link (fun i:Lengths s=>i.z)).plus (sum_priced (f:=f T) (g:=f U) ?_ he hp)
       unfold f; simp_rw [hv,hh]; cases k with
       | zero=>
          have hh(S U:Pence)(p:Fresh S): coeff 0 (propel S U)=coeff 0 U:= by
             rw [propel,coeff_zero_eq_constantCoeff_apply,map_mul,←coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply,peep (by rw [coeff_zero_eq_constantCoeff_apply,map_mul,constantCoeff_X,zero_mul]),p,mul_one]
          simp_rw [hh _ _ (a _),hh _ _ (b _),sub_self]; apply Pact.coin
       | succ n=> exact no_time (fun j hj=>(ih j (by omega) (by omega)).link stubW) (hl.le hk) a b
end YM.FormalBulk08.Dove
