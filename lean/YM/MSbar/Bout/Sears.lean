import YM.MSbar.Bout.Vaults
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
variable {m b d s N M:ℕ}{a C ρ:ℝ}(z:Site f)
variable (hA :∀ u≤p, Tokew (address F G) a s M 0 (PowerSeries.coeff u (singularity (pushChart F G v) 2)) C)(hv :ranged F l z N)(ha:0≤a)
variable (ht:0<t)(hH:t≤1)(hx:‖t • meetVar x w‖ < r)(hz:‖meetVar x w‖ ≤ ρ) (hr:1 ≤ ρ)
local notation "T!"=> taste
local notation "H"=> cycleP F v
local notation "π"=>address F G
noncomputable def barry (u k p:ℕ) (C ρ:ℝ):= (p+1:ℕ)*(C*(1+ρ)^(k+1))
lemma beltR (F':PowerSeries (Pot (Joint F G)))(x':E)(ha:0≤a)(hz:‖x'‖≤ ρ)(he:∀ i≤p,Vault π {z} a s d 0 (PowerSeries.coeff i F') C∧(PowerSeries.coeff i F').totalDegree≤ d): Belt p (picture x' F') ≤ barry 0 d p C ρ:=by
    have hp(i:ℕ)(hi:i≤p): |PowerSeries.coeff i (picture x' F')|≤ C*(1+ρ)^(d+1):=by unfold picture; rw [PowerSeries.coeff_map]; apply looks ha (across x' (he i hi|>.1) ha (by rwa [sub_zero]) (he i hi|>.2) 0)
    unfold Belt; exact (sum_le_sum (fun i hi=> hp i (Nat.lt_succ_iff.mp (mem_range.mp hi)))).trans_eq (by unfold barry; simp [nsmul_eq_mul])
lemma gust (F:List Bool→ PowerSeries (Pot (Joint F G)))(z:E)(p:ℕ) (t:ℝ): taste p (picture z (Yarn m F)) t= Yarn m (fun i=>taste p (picture z (F i)) t):=by
    induction m generalizing F with|zero=> rfl|succ m ih=> rw [twilled,twilled]; unfold taste picture; simp_rw [_root_.map_sum, mul_sum]; rw [sum_comm]; exact Finset.sum_congr rfl fun i _=> (ih _)
private lemma siren (p:ℕ) (t h i P W Z C B:ℝ)(f g:PowerSeries ℝ)(h1:0≤t)(h2:t ≤ 1)(h3:Belt p f ≤ P)(h4:Belt p g ≤ W)(h5:|h-taste p f t|≤ t^(p+1)* C)(h6:|i-taste p g t| ≤ t^(p+1)*B)(hz:0 ≤ C)(ht:0≤B) : |h*i - taste p (f*g) t| ≤ t^(p+1)*( C*(W+B)+P*(B+W)):=by
     let x:=taste p f t; let y:= taste p g t; let s:= t^(p+1); have hp: |i| ≤ W+B :=by
         nth_rw 1 [show i=i-y+y from (sub_add_cancel ..).symm]; exact (abs_add_le ..).trans ((add_le_add (h6.trans (mul_le_of_le_one_left ht (pow_le_one₀ h1 h2))) ((taste_pays h1 h2 g).trans h4)).trans_eq (add_comm ..))
     let z:= taste p (f*g) t; have he : h*i-z=(h-x)*i+x*(i-y)+(x*y-z):=by ring
     have ht' : |x*y-z|≤ t^(p+1)*(P*W):=by rw [abs_sub_comm]; exact (taste_mul p _ h1 h2 f g).trans (mul_le_mul_of_nonneg_left (mul_le_mul h3 h4 (Belt_pos ..) ((Belt_pos ..).trans h3)) (by positivity))
     change |h*i-z| ≤ _; rw [he]; refine (abs_add_le ..).trans ((add_le_add ((abs_add_le ..).trans (add_le_add (b:=t^(p+1)*C*(W+B)) (d:=P*(t^(p+1)*B)) ?_ ?_)) ht').trans_eq ?_)
     · exact (abs_mul ..).trans_le (mul_le_mul h5 hp (abs_nonneg _) ((abs_nonneg _).trans h5))
     · exact (abs_mul ..).trans_le (mul_le_mul ((taste_pays h1 h2 f).trans h3) h6 (abs_nonneg _) ((Belt_pos ..).trans h3))
     ring
variable {n:ℕ} (hS:S.patch.Branches S.kernel G)(hr':p+2+1 ≤ n)(hB:∀ i:Bond c,∀ x:Positions (Joint F G),‖x‖<r→ Allows n (arch F v i) x B)
include hA hv ha ht hH hx hz hr hS hr' hB
-- marker.Envelope ratio uses b global. choose m = max etc.
variable (hw:b*(p+2) ≤ m)(hm:m+b ≤ M)(hu:l.length≤ b)(hk:p+2 ≤ m) (hj:l.length≤n)
local notation "p!"=>barry 0 m p ((plateD z a p s m b N C)^b) ρ
local notation "μ!"=> barry 0 m p ((liftW a s N)*C) ρ
local notation "c₀"=>B*ρ^(p+3)
include hw hm hu hk hj
noncomputable def spoolP (s w c:ℝ)(b:ℕ):=1+2^b*((s+1)*(c+w))
lemma sail : |strap S (t⁻¹^2) t v x l (parmaM F w t) - taste p (picture (meetVar x w) (cycleP F v l)) t| ≤ t^(p+1)*(spoolP p! μ! (B*ρ^(p+3)) b)^l.length:=by
    let Z:= p!; let G':= μ!; let C':= c₀; let q:= spoolP p! μ! c₀ b; let H':=parmaM F w t; have hb:= hA _ le_rfl|>.1; have hW: 1 ≤ plateD z a p s m b N C:= le_add_of_nonneg_right (by have hh:=wpos a s N; positivity); have hZ:0≤ Z:=by unfold Z barry; positivity
    have hN:0≤ G':=by unfold G' barry; have h':=wpos a s N; positivity
    have hC' : 0 ≤ C' := by -- choose an edge. count.B.nonempty.
        let i:=Classical.arbitrary (Bond c); exact mul_nonneg (hB i _ hx|>.nonneg) (by positivity)
    have hq:1 ≤ q:=by refine le_add_of_nonneg_right ?_; change 0 ≤ 2^b*((Z+1)*(C'+G'));positivity
    let g(l):=strap S (t⁻¹^2) t v x l (parmaM F w t); let O(l) := picture X (H l); let R(l:List (Primary c G)):=Jets F v l; let X':=X
    generalize he:l.length= e
    induction e using Nat.strong_induction_on generalizing l with
    | h r IH=>
       rcases List.eq_nil_or_concat' l with hg|⟨a',u,hg⟩
       · subst l; rw [lonely,picture,cycleP,batt,_root_.map_one]; have hz':taste p 1 t=1:=by unfold taste; rw [sum_range_succ'];simp [PowerSeries.coeff_one]
         rw [hz',sub_self,abs_zero]; exact mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans hq) _)
       subst l; let n':= a'.length; have he':n'+1=r:=by rw [←he]; unfold n'; rw [List.length_append,List.length_cons,List.length_nil]
       let f(t': List Bool):= takeout true t' a'; let j(t': List Bool):= takeout false t' a'; let d'(T):=j T++[u]; let S'(L':List (Primary c G)):= buoy (tribe S (t⁻¹^2) t H' v) x L'; let Q':= t^(p+1); have hp(T:List Bool)(h:T.length=n'): |g (f T)*S' (d' T)-taste p (O (f T)*picture X' (R (d' T))) t| ≤ Q'*( q^n'*(G'+C')+Z*(C'+G')):=by
            have hD: n'+1≤n:=by omega
            have he(T :List Bool): ranged F (f T) z N:=fun i hi=>hv i (List.mem_append_left _ (Bout.narrow a' true T hi)); let L':=d' T; let d'':=(f T).length; have ht':(j T).length ≤ n':= (sunset false T a' h).trans_le ((part_le ..).trans_eq h); have hF:d''≤ n':= (sunset true T a' h).trans_le ((part_le ..).trans_eq h); have hv':n'+1 ≤ b:=by omega
            have hY: ranged F (d' T) z N:=by intro i hi; rcases List.mem_append.mp hi with hl|hl; exact hv i (List.mem_append_left _ (Bout.narrow a' false T hl)); exact hv i (List.mem_append_right _ hl)
            apply siren p t _ _ Z G' 0 _ C' _ _ ht.le hH
            · apply beltR F p z (d:=m) (s:=s) (a:=a) _ _ ha hz; intro i hi; obtain ⟨hP,hT⟩:= Bout.hearts F v (f T) p z hA (he T) ha rfl (ht:=show (f T).length≤ b from by apply hF.trans; omega) hm i hi; exact ⟨Quote.widen hP (pow_le_pow_right₀ hW (hF.trans (by omega))) le_rfl,(hT.trans (le_trans (Nat.mul_le_mul_right _ (hF.trans (by omega:n'≤ b))) hw))⟩
            · apply beltR F p z (d:=m) (s:=s) (a:=a) _ _ ha hz; intro i hi; exact ⟨Bout.behalf F v _ u i z (hA _ hi) hY ha ((Nat.add_le_add_left (ht'.trans (by omega:n' ≤ b)) m).trans hm),(Bout.edgesD F v _ _ p i hi).trans hk⟩
            · exact (IH d'' (hF.trans_lt (by omega:n'<r)) _ (he T) (hF.trans (by omega)) (hF.trans (by omega)) rfl).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hF) (by positivity))
            · exact ebb F v _ _ (j T) u p hS ht hx hr' (ht'.trans_lt (by omega :n'<n)) hB hr hz hH
            · positivity
            exact hC'
       rw [twig,springP,gust]; unfold picture at hp ⊢; simp_rw [_root_.map_mul]; rw [← show ∀ p' g':List Bool→ℝ,∀ n:ℕ,Yarn n (fun i=>p' i-g' i)= Yarn n p'-Yarn n g' from ?_] -- fill stitch
       rotate_left; · intro f g' n; induction n generalizing f g' with|zero=> rfl|succ u ih=> rw [twilled,twilled,twilled,← sum_sub_distrib]; apply sum_congr rfl; intro k _; exact ih (fun p=> f (k::p)) (fun p=> g' (k::p))
       have hQ:0≤ Q':=by unfold Q'; positivity
       refine (polished ..).trans ((shiny n' hp).trans ?_); rw [total_books,Fintype.card_bool,Nat.cast_ofNat]; refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega:n'≤ b)) (by positivity)) ?_; rw [←he',pow_succ]; change 2^b * (Q'*(q^n'*_+_))≤ Q'*(q^n'*q); have hx:= one_le_pow₀ (n:=n') hq
       calc
          _ = Q'*(2^b*(q^n'*(C'+G')+ Z*(C'+G'))):=by ring
          _ ≤ Q'*(2^b*(q^n'*(C'+G')+q^n'* (Z*(C'+G')))):=by gcongr Q' * (_ * (_ + ?_)); exact le_mul_of_one_le_left (by positivity) hx
          _ = Q'*(q^n'*(2^b*((Z+1)*(C'+G')))):=by ring
          _ ≤ Q'*(q^n'*q):=by exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)) hQ
end YM.MSbar.Bout
