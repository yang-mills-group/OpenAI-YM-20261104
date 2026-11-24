import YM.XSpace.LimitWork

/-!
# Exact bounds and convergence on shell for flare of normalized homogeneous fees
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Drama
open Lattice Sail Scale Trace Mu Future Tide Further.FreeCovariance.KP Function Set Filter Chart2 MvPolynomial Lows
open scoped Topology BigOperators
variable {ι:Type*} {L:Filter ι} {G:Gauge}{k d n m:ℕ}
abbrev Stage (G:Gauge)(d n:ℕ):=↥(Load G d n)
def readStage (X:Hat G d) (n:ℕ): Module.Dual ℂ (Stage G d n):= (view X).toLinearMap ∘ₗ (Load G d n).subtype
lemma no_change (p:Stage G d n)(h:∀ X,readStage X n p=0):p=0:= Subtype.ext (sameCap fun X=> (h X).trans (map_zero (view X)).symm)
lemma atmosphere {X:ι→ Hat G d}(H:Likely L X){p:ι→Stage G d n}(h:Still ℂ L p): Likely L fun i=> view (X i) (p i).val := send h (fun i=> readStage (X i) n) (fun A=> H.cont (walk_cont A.val))

def area (x:Cover):ℝ :=1+(reach x:ℝ)
lemma room (x:Cover):1≤area x:=by unfold area;simp
lemma included (x:Cover): 0<area x:= zero_lt_one.trans_le (room x)
lemma carry_cost (m:ℕ)(x:Cover):carry m (reach x)=(area x ^ m)⁻¹:=inv_pow ..
variable (d)
lemma scenic_break (t:ℝ)(X: Hat G d): scenic d (orchestra d t X)=∑ i:Fin (d+1), t^(1+i.val) • release (X i).val:=by unfold scenic castBlaze; rw [LinearMap.comp_apply,LinearMap.sum_apply]; apply Finset.sum_congr rfl; intro i _; exact map_smul (release (d:=i.val)) _ _
lemma fee_entry {p:Line G}(q:p∈cane k G)(B:ℝ)(hB:0≤B): ∃ C:ℝ,0≤C∧∀ (t:ℝ)(X:Hat G d)(x y:Cover),0≤ t→ t*area y≤ B→ area x≤ area y→ ‖probe (displace x p) (scenic _ (orchestra _ t X))‖ ≤ C*‖X‖ *carry (1+k) (reach y):=by
  choose C hC H using fun i:Fin (d+1)=> rate_flags (n:=i.val) q; refine ⟨∑ i:Fin (d+1),B^(1+i.val)*C i,Finset.sum_nonneg fun i _=>by positivity [hC i],fun t X x y ht h hx=>?_⟩
  rw [scenic_break,map_sum,Finset.sum_mul,Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>?_); rw [map_smul,norm_smul, Real.norm_of_nonneg (pow_nonneg ht _)]
  by_cases he : i.val<k; simp_rw [vacuity q he, norm_zero,mul_zero]; positivity [hC i,carry_pos (1+k) (reach y)]; set z:=area x; set m:=i.val; set v:=area y; have h' : 0<v:=included y; have hp:0<z:=included x; have hv:=hC i
  change t^(1+m)*_≤_; rw [carry_cost]; calc
    _ ≤ t^(1+m)*(C i*‖X i‖*z^(m-k)):= mul_le_mul_of_nonneg_left (H i (X i).val x) (by positivity)
    _ ≤ (B/v)^(1+m)*(C i*‖X‖*v^(m-k)):=by
      have hr:t≤B/v:= (le_div_iff₀ h').2 h; gcongr; exact norm_le_pi_norm X i
    _ = _:=by rw [div_pow,show (1+m)=m-k + (1+k) by omega,pow_add v]; change _= B^(m-k+(1+k))*C i * ‖X‖* (v^(1+k))⁻¹; field_simp

private lemma rent (x y:Fee G): ∃ C:ℝ,0≤C∧∀ p:Cover, ‖handshake (displace p y.line) x.line‖ ≤ C*carry (x.cost+y.cost) (reach p):=by
  rw [show x.cost+y.cost=2+x.k+y.k by unfold Fee.cost; omega]; exact line_receipt y.due (advertised _ x.line x.due)

lemma across (P:Tile G)(X:Book G n P){A B:ℝ}(hA:0≤A)(hB:0≤B):∃ C:ℝ,0≤C∧∀ (v:Hat G d)(z:Cover)(t:ℝ),‖v‖≤A→0≤t→ t*area z≤B→ ‖pit (scenic _ (orchestra d t v)) (P z)‖ ≤ C*carry n (reach z):= by
  have he(p:Fee G):∃ C:ℝ,0≤C∧∀ (v:Hat G d)(z:Cover)(t:ℝ),‖v‖≤A→0≤t→ t*area z≤ B→∀ x:Cover,area x≤area z→ ‖pit (scenic _ (orchestra d t v)) (harp (displace x p.line))‖≤ C*carry p.cost (reach z):=by
    obtain ⟨C,hC,H⟩:= fee_entry d p.due B hB; refine ⟨C*A,mul_nonneg hC hA,fun v z t h ht hp x hx=>?_⟩; rw [leg_test,Complex.norm_real]; apply le_trans (H _ _ _ _ ht hp hx); apply mul_le_mul_of_nonneg_right _ (carry_pos p.cost (reach z)).le; gcongr
  induction X with
  | zero=> exact ⟨0, le_rfl,fun _ _ _ _ _ _=> by simp⟩
  | unit=> exact ⟨1,zero_le_one, fun _ _ _ _ _ _=> by simp [carry]⟩
  | left p=> obtain ⟨C,hC,H⟩:=he p; exact ⟨C,hC,fun v z t hv ht hp=> by simpa [originate] using H v z t hv ht hp 0 (by simpa [area,reach_zero] using room z)⟩
  | right p=> obtain ⟨C,hC,H⟩:=he p; exact ⟨C,hC,fun v z t hv ht hp=> H v z t hv ht hp z le_rfl⟩
  | rent p q=> obtain ⟨c,hc,H⟩:=rent p q; refine ⟨c,hc,fun v z t _ _ _=>?_⟩; rw [pit,aeval_C,Algebra.algebraMap_self,RingHom.id_apply,Complex.norm_real]; apply H
  | mul a b i j=> obtain ⟨c,hc,H⟩:=i; obtain ⟨z,hz,K⟩:=j; refine ⟨c*z,mul_nonneg hc hz,fun v x t h ht hp=>?_⟩; rw [Pi.mul_apply,map_mul,norm_mul]; exact (mul_le_mul (H v x t h ht hp) (K v x t h ht hp) (norm_nonneg _) (mul_nonneg hc (carry_pos _ _).le)).trans_eq (by rw [mul_mul_mul_comm, carry_power])
  | add a b i j=> obtain ⟨c,hc,H⟩:=i; obtain ⟨z,hz,K⟩:=j; refine ⟨c+z,add_nonneg hc hz,fun v x t h ht hp=>?_⟩; rw [Pi.add_apply,map_add,add_mul]; exact (norm_add_le ..).trans (add_le_add (H v x t h ht hp) (K v x t h ht hp))
  | scale a b ih=> obtain ⟨c,hc,H⟩:=ih; refine ⟨‖b‖*c,mul_nonneg (norm_nonneg _) hc,fun v x t h ht hp=>?_⟩; rw [Pi.smul_apply,map_smul, norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (H v x t h ht hp) (norm_nonneg _)

def inspect (d:ℕ){P: Tile G}(p:Book G n P)(x:Cover): Stage G d (n*(1+d)):= ⟨scale (area x)⁻¹ (overture d (P x)),capacity _ (recorder d p x)⟩
lemma ticket (P:Tile G)(p:Book G n P): TestBound ℂ (fun x=> carry n (reach x)) (inspect d p):=by
  apply coupon (V:=Stage G d (n*(1+d))) (fun v=>readStage v (n*(1+d))) no_change; intro v; obtain ⟨C,hC,H⟩:=across d P p (norm_nonneg v) zero_le_one; refine ⟨C,hC,fun i=>?_⟩; change ‖view v (scale _ _)‖ ≤ _; rw [scaled,music_at]; exact H _ _ _ le_rfl (inv_pos.mpr (included i)).le (inv_mul_cancel₀ (included i).ne').le

-- cost of partial Taylor port on scaled jets
variable {d}
lemma budget_row (T:Cap G d)(x:Cover)(B:Hat G d): view B (Cut coin k T)=(area x:ℂ)^k*view B (Cut coin k (scale (area x)⁻¹ T)):=by
  rw [scale_saves,map_smul,smul_eq_mul,Complex.ofReal_inv,inv_pow,mul_inv_cancel_left₀]; exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (included x).ne')
lemma steam_row (P:Tile G)(p:Book G n P)(X:Hat G d)(k:ℕ): ∃ C:ℝ, 0≤C∧∀ x:Cover, ‖view X (Cut coin k (overture d (P x)))‖ ≤ C*area x^k * carry n (reach x):=by
  obtain ⟨C,hC,H⟩:=ticket d P p ((view X).toLinearMap ∘ₗ Cut coin k ∘ₗ (Load G d _).subtype)
  refine ⟨C,hC,fun x=>?_⟩; rw [budget_row (overture d _) x X,norm_mul,norm_pow, Complex.norm_real, Real.norm_of_nonneg (included x).le]; exact (mul_le_mul_of_nonneg_left (H _) (pow_nonneg (included x).le k)).trans_eq (by ring)
lemma shuttled (P:Tile G)(p:Book G n P)(B:ι→Hat G d)(H:Likely L B)(k:ℕ):∃ C:ℝ, 0≤C∧∀ᶠ i in L,∀ x:Cover, ‖view (B i) (Cut coin k (overture d (P x)))‖ ≤ C*area x^k * carry n (reach x):=by
  let f:= fun x=> inspect d p x; let V:= Module.finBasis ℂ (Stage G d (n*(1+d))); let ℳ i:Module.Dual ℂ (Stage G d (n*(1+d))):= (view (B i)).toLinearMap ∘ₗ Cut coin k ∘ₗ (Load G d (n*(1+d))).subtype
  choose C hc Hc using fun u=>ticket d P p (V.coord u); choose D hd HD using fun j=> (show Likely L fun i=> ℳ i (V j) from H.cont (walk_cont (Cut coin k (V j).val))).bound
  refine ⟨∑ i,C i*D i,Finset.sum_nonneg fun i _=>mul_nonneg (hc i) (hd i),?_⟩; filter_upwards [eventually_all.mpr HD] with i hi x; rw [budget_row (overture _ _) x, norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (included x).le]
  rw [mul_comm (∑ _,_),mul_assoc]; gcongr area x ^ k * ?_; · positivity [included x]
  change ‖ℳ i (f x)‖ ≤ _; rw [← V.sum_repr (f x),map_sum,Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun j _=>?_); rw [map_smul,norm_smul]; exact (mul_le_mul (Hc j x) (hi j) (norm_nonneg _) (mul_nonneg (hc j) (carry_pos n (reach x)).le)).trans_eq (by ring)
end YM.XSpace.Drama
