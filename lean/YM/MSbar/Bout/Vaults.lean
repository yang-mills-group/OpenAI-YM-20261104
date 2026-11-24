import YM.MSbar.Bout.Commit
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bout
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Parma Portal
variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio)(v:S.Choices)(x:Positions (Primary c G))(w:Positions (Key F G))(l:List (Primary c G))(i:Primary c G)(p:ℕ)
variable {t B K r:ℝ}
local notation "Y"=>Positions (Primary c G)
local notation "E"=>Positions (Joint F G)
local notation "X"=>meetVar x w
local notation "L"=>l++[i]
local notation "J"=> Lis.rope i
local notation "A₀"=> arch F v (Lis.rope i)
local notation "A"=>singularity (pushChart F G v) 2
variable {m b d s N M:ℕ}{a:ℝ}(z:Site f)
 local notation "μ"=>PowerSeries.coeff
section
variable {σ:Type}[Fintype σ][DecidableEq σ]{n:Side}{y:Site n}{U:σ→Site n}{C:ℝ}{y0:View σ} {p1:ℕ}
local notation "V"=> Vault U {y} a s m y0
local notation "R"=> PowerSeries (Pot σ)
lemma entire (f g:PowerSeries (Pot σ))(ha:0≤a) (hh:∀ i≤p1,V (μ i f) B∧ (μ i f).totalDegree≤ b) (hx :∀ i≤p1,V (μ i g) C∧ (μ i g).totalDegree≤ d)(u:ℕ)(he:u≤p1): Vault U {y} a s m y0 (μ u (f*g)) ((p1+1:ℕ)*(2^m*(B*C))) ∧ (μ u (f*g)).totalDegree ≤ b+d:=by
    rw [elevator]; have hK:=hh p1 le_rfl|>.1.1; have hC:=hx p1 le_rfl|>.1.1; constructor
    · refine Quote.widen (Quote.total (fun i:ℕ=>μ i f*μ (u-i) g) _ (fun _=> (2^m*(B*C))) (fun i hi=> Bout.stock ha (hh i (by simp only [mem_range] at hi;omega)|>.1) (hx (u-i) (by omega)|>.1))) ?_ le_rfl
      simp only [sum_const, nsmul_eq_mul, card_range];gcongr
    apply totalDegree_finsetSum_le; intro i hi; simp only [mem_range] at hi; exact (totalDegree_mul ..).trans (Nat.add_le_add (hh i (by omega)|>.2) (hx (u-i) (by omega)|>.2))
lemma pantry (f':List Bool→Pot σ)(h:∀ l,l.length=p1→ Vault U {y} a s m y0 (f' l) C∧(f' l).totalDegree≤d): Vault U {y} a s m y0 (Yarn p1 f') (2^p1*C)∧(Yarn p1 f').totalDegree ≤d:=by
    induction p1 generalizing f' with
    | zero=>rw [twillz,pow_zero,one_mul]; exact h [] rfl
    | succ i ih=>
       let G(b)(v):=f' (b::v); let B(b):=Yarn i (G b); have hx(b:Bool):V (B b) (2^i*C)∧ (B b).totalDegree≤ d:=ih _ (fun l hL=> h (b::l) (by simp only [List.length_cons,hL])); rw [twilled]; refine ⟨?_,totalDegree_finsetSum_le (fun i _=> hx i|>.2)⟩; refine Quote.widen (Quote.total B Finset.univ (fun _=> 2^i*C) (fun i _=>hx i|>.1)) ?_ le_rfl; rw [Fintype.sum_bool];exact le_of_eq (by ring)
end
noncomputable def plateD (z :Site f)(a:ℝ)(p s m n N:ℕ)(B:ℝ):= 1+ 2^n*((p+1:ℕ)*(2^m* (liftW a s N* B))) -- z is site.drop
variable (hA :∀ u≤p, Tokew (address F G) a s M 0 (PowerSeries.coeff u (singularity (pushChart F G v) 2)) B)(hv :ranged F l z N)(ha:0≤a)
include hA hv ha
lemma hearts (he:l.length=d)(ht:d≤b)(hh:m+b≤ M):∀ i≤p,Vault (address F G) {z} a s m 0 (PowerSeries.coeff i (cycleP F v l)) ((plateD z a p s m b N B)^d) ∧(PowerSeries.coeff i (cycleP F v l)).totalDegree ≤ d*(p+2):=by
    let T:=plateD z a p s m b N B; let E':=liftW a s N*B; have hB':0 ≤ E':= mul_nonneg (wpos ..|>.le) (hA _ le_rfl|>.1); have hP':1 ≤ T:= le_add_of_nonneg_right (mul_nonneg (by positivity) (mul_nonneg (by positivity) (mul_nonneg (by positivity) hB')))
    induction d using Nat.strong_induction_on generalizing l with
    | h r ih=> rcases List.eq_nil_or_concat' l with hhx|⟨ l',i,hEq⟩
               · subst l; subst r; simp only [cycleP,batt,pow_zero,List.length_nil,zero_mul]; intro i hi; by_cases hx:i=0; subst i; simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,_root_.map_one,pow_zero,totalDegree_one]; refine ⟨?_,le_rfl⟩; exact (by simpa only [MvPolynomial.C_1,abs_one] using (Bout.VaultC (p:=m) (z:=z) (j:=address F G) (a:=a) (s:=s) (x:=0) (1:ℝ))); rw [PowerSeries.coeff_one,if_neg hx,totalDegree_zero]; exact ⟨Quote.nill zero_le_one,le_rfl⟩
               subst l; intro u hu; let g(T:List Bool):= takeout true T l'; let v'(T:List Bool):= takeout false T l' ++[i]; let n:=l'.length; have he':n+1=r:=by unfold n; rw [←he,List.length_append]; rfl
               have hk :m+l'.length ≤ M:=by omega -- fix semicolon
               let f'(T:List Bool):= μ u (cycleP F v (g T)* Jets F v (v' T)); have hz(T':List Bool)(h:T'.length=n): Vault (address F G) {z} a s m 0 (f' T') ((p+1:ℕ)*(2^m*(T^n* E'))) ∧ (f' T').totalDegree ≤ r*(p+2):=by
                       refine And.imp (fun h=>h) (fun h=> le_trans h (Nat.le_of_eq (by rw [←he',Nat.add_mul,Nat.one_mul]))) (Bout.entire (y:=z) (m:=m) (s:=s) (p1:=p) (cycleP F v (g T')) (Jets F v (v' T')) ha ?_ ?_ u hu); -- remove arith
                       · intro i' hh'; have ht' : (takeout true T' l').length≤ n:=(sunset true _ _ h).trans_le ((part_le ..).trans_eq h); let d':=(g T').length; obtain ⟨h₀,hi⟩:=ih d' ((ht'.trans_lt (by omega:n<r))) _ (show ranged F (g T') z N from fun i hi=>hv i (List.mem_append_left _ (Bout.narrow l' true T' hi))) rfl (by unfold d' g; omega) i' hh'; exact ⟨Quote.widen h₀ (pow_le_pow_right₀ hP' ht') le_rfl,hi.trans (Nat.mul_le_mul_right _ ht')⟩
                       intro i' hh'; have hN(T:List Bool):ranged F (v' T) z N:=by intro i' hp; rcases List.mem_append.mp hp with he|he'; exact hv _ (List.mem_append_left _ (Bout.narrow l' false T he)); exact hv _ (List.mem_append_right _ he')
                       exact ⟨Bout.behalf F v _ i i' z (hA _ hh') (hN _) ha (Nat.add_le_add_left ((sunset false T' l' h).trans_le ((part_le false T').trans_eq h)) _|>.trans hk),Bout.edgesD F v _ i p i' hh'⟩ -- fill length proof
               rw [springP,show μ u _=Yarn l'.length f' from Whisk.spun (PowerSeries.coeff u : PowerSeries (Pot (Joint F G))→ₗ[Pot (Joint F G)]Pot (Joint F G)).toAddMonoidHom n (fun t:List Bool=> cycleP F v (g t)* Jets F v (v' t))]; have hp:=Bout.pantry f' hz; refine ⟨Quote.widen hp.1 ?_ le_rfl,hp.2⟩; unfold T; rw [←he']; let q:=2^m* ((liftW a s N)*B); have h0(n):0 ≤ T^n:=pow_nonneg (zero_le_one.trans hP') (n:ℕ)
               change 2^n*_ ≤ T^(n+1)
               refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num: (1:ℝ)≤2) (by omega:n≤ b)) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (mul_nonneg (h0 _) hB')))) ?_; unfold T; unfold E'; rw [pow_succ]; refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (show (0:ℝ) ≤ 1 from zero_le_one)) (by exact h0 n)); change _= (plateD z a p s m b N B)^n * (_); ring
end YM.MSbar.Bout
