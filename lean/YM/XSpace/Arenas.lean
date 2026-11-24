import YM.XSpace.Premiere

/-!
# Taylor remainder, before integration, on lattice cells (native units)

Paid jointly already: Book gives multiplicative λ factor at each incident end, no extra
from a raw-stencil bundle norm that lost cancellations. Work with radius square (reach).
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Drama
open Lattice Sail Scale Trace Mu Future Tide Further.FreeCovariance.KP Function Set Filter Chart2 MvPolynomial Lows
open scoped Topology BigOperators
variable {ι:Type} {L:Filter ι} {G:Gauge}{k d n m:ℕ}
variable {A:ι→Contact G}{a:ι→ℝ}{r:ι→ℕ}(b:ℝ) (B:ι→Hat G d) (S:Studio L a r A)(ha:∀ᶠ i in L,0< a i)
    (hb:1≤b) (hx:Likely L B) (H:∀ᶠ i in L, orchestra d (a i) (B i)=gather d (A i))

-- menu cap independent of issues outside observed clear region
private def Port (r:ι→ℕ)(a:ι→ℝ)(b:ℝ)(u:ℕ)(i:ι)(x:Cover): Prop:= reach x+u ≤r i∧a i*area x ≤ b
private def Ready (u:ι→ℕ)(a:ι→ℝ)(P:ι→Cover→ℂ)(L:Filter ι)(b:ℝ)(n k:ℕ): Prop:=∃ R:ℕ,∃ C:ℝ,0≤C∧ ∀ᶠ i in L, ∀ x:Cover, Port u a b R i x→ ‖P i x‖ ≤ C*carry n (reach x)*(a i*area x)^k
private def twin (p:Tile G)(k d:ℕ)(G':ι→Contact G)(B:ι→ Hat G d)(u:ι→ℕ)(a:ι→ℝ)(L:Filter ι)(b:ℝ): Prop:=
  let f i x:= pit (G' i) (p x); let g i x:= pit (scenic d (orchestra d (a i) (B i))) (p x)
  Ready u a f L b k 0 ∧ Ready u a g L b k 0 ∧ Ready u a (f-g) L b k (d+1)
private lemma larger {u v i x}(h:u≤v)(H: Port r a b v i x): Port r a b u i x:=⟨ le_trans (by omega : reach x+u≤ reach x+v) H.1,H.2⟩
private lemma no_work : Ready r a (fun _ _=>(0:ℂ)) L b k d:= ⟨0,0,le_rfl,Eventually.of_forall fun _ _ _=>by simp⟩
private lemma ready_scale {f:ι→Cover→ℂ} (h:Ready r a f L b k d)(p:ℂ):Ready r a (p • f) L b k d:=by
  obtain ⟨R,C,hC,H⟩:= h; refine ⟨R,‖p‖*C,mul_nonneg (norm_nonneg _) hC,H.mono (fun i hi x hx=>?_)⟩; rw [Pi.smul_apply,Pi.smul_apply,norm_smul, mul_assoc ‖p‖,mul_assoc ‖p‖]; gcongr; apply hi _ hx
private lemma ready_add {f g:ι→Cover→ℂ} (h:Ready r a f L b k d)(p:Ready r a g L b k d): Ready r a (f+g) L b k d:=by
  obtain ⟨R,C,hC,H⟩:=h; obtain ⟨F,D,hD,K⟩:=p; refine ⟨R+F,C+D,add_nonneg hC hD,?_⟩; filter_upwards [H,K] with i hi hh x hx; rw [Pi.add_apply,Pi.add_apply,add_mul,add_mul]; exact (norm_add_le ..).trans (add_le_add (hi x (larger b (by omega) hx)) (hh x (larger b (by omega) hx)))
include ha in
private lemma ready_mul {l:ℕ}{f g:ι→Cover→ℂ}(h:Ready r a f L b k l)(p:Ready r a g L b d m):Ready r a (f*g) L b (k+d) (l+m):=by
  obtain ⟨R,C,hC,H⟩:=h; obtain ⟨F,D,hD,K⟩:=p; refine ⟨R+F,C*D,mul_nonneg hC hD,?_⟩; filter_upwards [ha,H,K] with i hp hi hh x hx; rw [Pi.mul_apply,Pi.mul_apply,norm_mul,pow_add,← carry_power]; exact (mul_le_mul (hi x (larger b (by omega) hx)) (hh x (larger b (by omega) hx)) (norm_nonneg _) (by positivity [carry_pos k (reach x), included x])).trans_eq (by ring)
lemma wake (z:ℝ)(hz:0≤z)(k n:ℕ)(v:Cover): z^k ≤ (z*area v)^k*carry k (reach v):=by apply le_of_eq; unfold carry; change _= (z* area v)^k * (area v)⁻¹^k; rw [← mul_pow, mul_assoc z, mul_inv_cancel₀ (included v).ne',mul_one]
private lemma incor {q:ℝ}(hq:0<q){r:ℝ}(hr: q*r≤b)(k d:ℕ)(h:d≤k)(ht:0<r): (q*r)^k ≤ b^(k-d)*(q*r)^d:=by
  nth_rw 1 [show k=k-d+d by omega]; rw [pow_add]; gcongr
include hb S H ha hx in
private lemma pulse (X:Fee G): ∃ C:ℝ,∃ R:ℕ,0≤C∧∀ᶠ i in L,∀ x:Cover,Port r a b R i x →∀ y:Cover,reach y≤reach x→
    let A':=scenic d (orchestra d (a i) (B i)); let p:Stamp G:= harp (displace y X.line)
    ‖pit (A i) p‖ ≤ C*carry X.cost (reach x) ∧ ‖pit A' p‖ ≤ C*carry X.cost (reach x) ∧
    ‖pit (A i) p-pit A' p‖ ≤ C*carry X.cost (reach x)*(a i*area x)^(d+1):=by
  have hZ : ∃ C:ℝ,∃ R:ℕ, 0≤C∧∀ᶠ i in L,∀ x:Cover,Port r a b R i x →∀ y:Cover,reach y≤reach x→ |probe (displace y X.line) (A i-scenic d (orchestra d (a i) (B i)))| ≤ C*carry X.cost (reach x)*(a i*area x)^(d+1):= by
    by_cases h: X.k ≤ d; swap
    · obtain ⟨C,R,hC,T⟩:= steady_price S (ha.mono fun i hi=>hi.le) X.due; refine ⟨C*b^(X.cost-(d+1)),R,by positivity,?_⟩; filter_upwards [T,ha] with i hi ht x hh y hy; rw [map_sub,scenic_break,map_sum,Finset.sum_eq_zero (fun j _=>?_ ),sub_zero]; swap; · rw [map_smul,vacuity X.due (by have he:=j.isLt; omega),smul_zero];
      apply le_trans (hi _ (le_trans (Nat.add_le_add_right hy _) hh.1)); calc C*_ ≤ C*((a i*area x)^X.cost*carry X.cost (reach x)):= mul_le_mul_of_nonneg_left (wake _ ht.le X.cost 0 x) hC
                                                                             _ ≤ C*(b^(X.cost-(d+1))*(a i*area x)^(d+1) *carry X.cost (reach x)) :=by gcongr C * (?_*_); exacts [(carry_pos ..).le,incor b ht hh.2 X.cost (d+1) (by unfold Fee.cost; omega) (included _)]
                                                                             _ = _:= by ring
    obtain ⟨C,R,hC,T⟩:= remainder_price S (ha.mono fun i hi=>hi.le) X.due (show X.k≤d+1 by omega); have hb':=zero_lt_one.trans_le hb; refine ⟨C*b,R,by positivity,?_⟩; filter_upwards [H,T,ha] with i hi ht hP x hx y hy; rw [hi]; apply (ht _ (le_trans (Nat.add_le_add_right hy _) hx.1)).trans; have he: d+1-X.k+(1+X.k)=d+2:=by omega
    have hh : area y≤area x:= by unfold area; gcongr
    refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (included y).le hh (d+1-X.k)) (mul_nonneg hC (pow_nonneg hP.le (d+2)))) ?_; rw [carry_cost]; have hz:0<area x:=included x; have hp:=hx.2
    calc _ = C*(area x^(1+X.k))⁻¹*(a i*area x)^(d+2):=by rw [mul_pow, ← show d+1-X.k+ (1+X.k)=d+2 from he,pow_add (area x)]; field_simp; ring
         _ ≤ _:= by -- one power cost b
           change _≤ C*b*(area x^(1+X.k))⁻¹*(a i*area x)^(d+1); rw [show (a i*area x)^(d+2)=a i*area x*(a i*area x)^(d+1) from pow_succ' .., ← mul_assoc, mul_right_comm C]; gcongr -- fix
  have hb':= zero_lt_one.trans_le hb; obtain ⟨C,R,hC,hZ⟩:= hZ; obtain ⟨D,hD,T⟩:= fee_entry d X.due b hb'.le; obtain ⟨K,hK,P⟩:=Likely.bound (F:=Hat G d) hx
  set C':= D*K; have hv: 0≤C':=mul_nonneg hD hK
  refine ⟨C*b^(d+1)+C'+C,R,by positivity,?_⟩; filter_upwards [ha,hZ,P] with i hi hp hv' x hx y hy; set t:= carry X.cost (reach x); set v:=a i*area x; have ht:0<t:=carry_pos ..; have hu:0≤v:=by unfold v; positivity [included x]
  have Hx:v≤b:=hx.2; simp only [leg_test]
  let a₁:= probe (displace y X.line) (A i); let a₂:=probe (displace y X.line) (scenic d (orchestra d (a i) (B i)));  have hY:=hp x hx y hy
  have hh : ‖(a₁:ℂ)-(a₂:ℂ)‖ ≤ C*t*v^(d+1):=by rw [← Complex.ofReal_sub,Complex.norm_real]; simpa only [t,v,map_sub,a₁,a₂,Real.norm_eq_abs] using hY
  have h₁: ‖(a₂:ℂ)‖ ≤ C'*t:=by rw [Complex.norm_real]; apply (T _ _ _ _ hi.le Hx (show area y≤area x by unfold area; gcongr)).trans; change D*_ *t ≤ (D*_)*t; gcongr
  have hn := show C*b^(d+1)≥C from le_mul_of_one_le_right hC (one_le_pow₀ hb); set b':=C*b^(d+1)+C'+C; have hhC:C≤b':=by unfold b'; linarith
  have hhD:C'≤b':=by unfold b'; linarith
  refine ⟨le_trans ((norm_le_norm_sub_add (a₁:ℂ) (a₂:ℂ)).trans (add_le_add hh h₁)) ?_, h₁.trans (by change _≤ b'*t; gcongr),hh.trans (by change _≤ b'*t*v^(d+1); gcongr)⟩
  change _≤ b'*t; calc
    _ ≤ C*t*b^(d+1) + C'*t:=by gcongr
    _ = (C*b^(d+1)+C')*t:=by ring
    _ ≤ _:=by gcongr ?_ * t; unfold b'; linarith

include hb S H ha hx in
private lemma particle (V:Fee G)(f:Cover→Cover)(h:∀ x,reach (f x) ≤reach x): twin (fun x=> harp (displace (f x) V.line)) V.cost d A B r a L b:=by
  obtain ⟨C,R,hC,H⟩:= pulse b B S ha hb hx H V; refine ⟨⟨R,C,hC,H.mono fun i hi x hh=>?_⟩,⟨R,C,hC,H.mono fun i hi x hh=>?_⟩,⟨R,C,hC,H.mono fun i hi x hh=>(hi _ hh _ (h x)).2.2⟩⟩
  all_goals rw [pow_zero,mul_one]; first| exact (hi _ hh _ (h x)).1| exact (hi _ hh _ (h x)).2.1
include hb S H ha hx in
private theorem rings {P:Tile G} (X:Book G n P): twin P n d A B r a L b:=by
  induction X with
  | zero=> simp only [twin,Pi.zero_apply,map_zero,sub_self]; exact ⟨no_work b,no_work b,no_work b⟩
  | unit=> have h:Ready r a (fun _ _=>(1:ℂ)) L b 0 0:=⟨0,1,by simp,Eventually.of_forall fun i _ _=> by simp [carry]⟩
           simp only [twin,Pi.one_apply,map_one,sub_self]; exact ⟨h,h,no_work b⟩
  | rent x y => obtain ⟨C,hC,K⟩:= line_receipt y.due (advertised _ x.line x.due); simp only [twin,pit,aeval_C,Algebra.algebraMap_self,RingHom.id_apply,sub_self]; refine ⟨?_,?_,no_work _⟩; any_goals refine ⟨0,C,hC,?_⟩ <;> exact Eventually.of_forall (fun i z h=>by rw [pow_zero,mul_one,Complex.norm_real, show x.cost+y.cost=2+x.k+y.k by unfold Fee.cost; omega]; exact K _)
  | left p=> have he:= particle b B S ha hb hx H p (fun _=>0) (by simp); simp_rw [originate] at he; exact he
  | right p=> exact particle b B S ha hb hx H p id fun _=>le_rfl
  | @add p q k y c i j=>
    let Z (l:Tile G)(V:ι→Contact G) (i:ι) (x:Cover):= pit (V i) (l x)
    let D (i:ι):=scenic d (orchestra d (a i) (B i))
    have he V: Z (p+q) V=Z p V+Z q V:= by funext i j; simp [Z]
    simp only [twin]; refine ⟨?_,?_,?_⟩
    · change Ready _ _ (Z _ _) _ _ _ _; rw [he]; exact ready_add _ i.1 j.1
    · change Ready _ _ (Z _ D) _ _ _ _; rw [he]; exact ready_add _ i.2.1 j.2.1
    change Ready _ _ (Z _ A-Z _ D) _ _ _ _; rw [he,he,add_sub_add_comm]; exact ready_add _ i.2.2 j.2.2
  | @scale p n h c i=>
    let Z (l:Tile G)(V:ι→Contact G) (i:ι) (x:Cover):= pit (V i) (l x)
    let D (i:ι):=scenic d (orchestra d (a i) (B i))
    have he V: Z (c • p) V=c • Z p V:= by funext i j; simp [Z]
    simp only [twin]; refine ⟨?_,?_,?_⟩
    · change Ready _ _ (Z _ _) _ _ _ _; rw [he]; exact ready_scale _ i.1 c
    · change Ready _ _ (Z _ D) _ _ _ _; rw [he]; exact ready_scale _ i.2.1 c
    change Ready _ _ (Z _ A-Z _ D) _ _ _ _; rw [he,he,← smul_sub]; exact ready_scale _ i.2.2 c
  | @mul p q k l y c i j=>
    let Z (l:Tile G)(V:ι→Contact G) (i:ι) (x:Cover):= pit (V i) (l x)
    let D (i:ι):=scenic d (orchestra d (a i) (B i))
    have he V: Z (p*q) V=Z p V*Z q V:= by funext i j; simp [Z]
    simp only [twin]; refine ⟨?_,?_,?_⟩
    · change Ready _ _ (Z _ _) _ _ _ _; rw [he]; exact ready_mul _ ha i.1 j.1
    · change Ready _ _ (Z _ D) _ _ _ _; rw [he]; exact ready_mul _ ha i.2.1 j.2.1
    change Ready _ _ (Z _ A-Z _ D) _ _ _ _; rw [he,he, show Z p A*Z q A-Z p D*Z q D=(Z p A-Z p D)* Z q A+ Z p D*(Z q A-Z q D) by ring]; apply ready_add
    · exact ready_mul (l:=d+1) (m:=0) _ ha i.2.2 j.1
    simpa only [Nat.zero_add] using ready_mul _ ha i.2.1 j.2.2

def LTop (P:Stamp G)(c:ℝ)(u:Hat G d):= view (orchestra d c u) (trunc coin d (overture d P))
def Remainder (P:Tile G)(A:ι→Contact G)(B:ι→Hat G d)(a:ι→ℝ)(i:ι)(x:Cover):= pit (A i) (P x)-LTop (P x) (a i) (B i)
-- High part of pure polynomial playback beyond horizon is payable without issue
private lemma finish_lo (b:ℝ)(hb:1≤ b)(hx:Likely L B)(h:∀ᶠ i in L, 0<a i){P:Tile G}(X:Book G n P): Ready r a (fun i x=> pit (scenic _ (orchestra d (a i) (B i))) (P x)-LTop (P x) (a i) (B i)) L b n (d+1):=by
  let m:= max (n*(1+d)) d; have hp (x):overture d (P x)∈Load G d m:= Contraction.higher coin (le_max_left ..) (recorder d X x)
  choose C hC H using fun k:ℕ=> shuttled P X B hx k
  set t:= Finset.range (d+1); let s:= Finset.range (m+1); refine ⟨0,∑ k∈s\t,C k*b^(k-(d+1)),Finset.sum_nonneg fun i _=>by positivity [hC i],?_⟩
  filter_upwards [h,(eventually_all_finset s).mpr (fun i _=> H i)] with i hi ht x hx'; rw [← music_at,uncut _ _ (hp x),LTop,low_value]; rw [← Finset.sum_sdiff_eq_sub (s₁:= t) (s₂:=s) (by unfold t s m; simp)]; rw [Finset.sum_mul,Finset.sum_mul]; apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro k hk; obtain ⟨h1,h2⟩:= Finset.mem_sdiff.mp hk; have he:=hC k; have h2: d+1≤ k:=le_of_not_gt (mt Finset.mem_range.mpr h2); rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hi.le]; apply le_trans (mul_le_mul_of_nonneg_left (ht _ h1 x) (pow_nonneg hi.le _)) -- ht _ h1 x
  calc
    _ = (C k * carry n (reach x)) * (a i*area x)^k :=by rw [mul_pow]; ring
    _ ≤ (C k * carry n (reach x))*(b^(k-(d+1))*(a i*area x)^(d+1)):= by
      gcongr _ * ?_; · positivity [carry_pos n (reach x)]
      exact incor b hi hx'.2 k (d+1) h2 (included x)
    _ = _:= by ring
include hb S H ha hx in
lemma outer (P:Tile G)(X:Book G n P): ∃ (s:ℕ)(C:ℝ),0≤C∧∀ᶠ i in L,∀ x:Cover, reach x+s≤r i→ a i*area x≤ b→ ‖Remainder P A B a i x‖ ≤ C*carry n (reach x)*(a i*area x)^(d+1):= by
  obtain ⟨s,C,hC,F⟩:= ready_add b (Drama.rings b B S ha hb hx H X).2.2 (finish_lo (r:=r) B b hb hx ha X)
  refine ⟨s,C,hC,?_⟩; filter_upwards [F] with i hi x h hh; specialize hi x ⟨h,hh⟩; simp only [Pi.add_apply,Pi.sub_apply,sub_add_sub_cancel] at hi; exact hi
end YM.XSpace.Drama
