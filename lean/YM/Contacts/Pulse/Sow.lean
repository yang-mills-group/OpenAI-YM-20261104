import YM.Contacts.Pulse.Afar
namespace YM.Pulse.Spine
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration Quill
open scoped Classical Topology BigOperators NNReal ENNReal
noncomputable section
variable {α β X Y Z:Type} {L:Side}{σ δ η:ℝ≥0} {k n t:ℕ}
-- fixed root at 0. Evaluation arrays in external Q with no location convention, must include in estimate B at any prescribed profile.
def network (R: Fin t→ Node α→Node β→ℝ) (z:Cover)(b:Breed t α)(v:Tailor t) (y:Fin t→Node β) := ∏ i:Fin t,R i (publish z b v i.succ) (y i)
def gas (σ:ℝ≥0)(n:ℕ)(y:Node β)(q:Fin t→Node β):= (bath σ n β).bill (Fin.cons y q)
def thread (σ:ℝ≥0)(n:ℕ)(L:Side)(z: Cover)(b:Breed t α)(y:Node β)(v:Tailor t):= spokes σ n (size v) L * hook σ n L (z,b 0) y
lemma thread_pos (z:Cover)(b:Breed t α)(y:Node β)(v:Tailor t): 0<thread σ n L z b y v:= mul_pos (mist_pos (by positivity)) (mist_pos (Nat.cast_nonneg _))
variable {z:Cover}{c:ℝ} {b:Breed t α}{R: Fin t→Cross L α β}
lemma web_grows (R: Fin t→Node α→Node β→ℝ)(u:Fin t→ℝ)(hR:∀ j x,Balanced (R j x) (hook σ n L x) (u j)) (v:Tailor t)(y:Node β) :
    Balanced (network R z b v) (gas σ n y) (thread σ n L z b y v * ∏ i,u i):= by
  let x:= publish z b v; refine budget_mono (budget_scale (thread_pos z b y v).le (budget_pi (fun j:Fin t=> hR j (x j.succ)))) (fun q=>by unfold gas; positivity) fun q=> ?_
  have he:= mul_le_mul_of_nonneg_right (canopy (L:=L) σ n x (Fin.cons y q)) (norm_nonneg (network R z b v q)); unfold gas; apply he.trans; apply le_of_eq; rw [show degree x=v from deg_issue .., Fin.prod_univ_succ]; unfold thread network; simp only [norm_prod,Fin.cons_succ,Fin.cons_zero,prod_mul_distrib]; rw [show x 0=(z,b 0) by simp [x,publish,legLane]]; unfold x; ring
lemma web_jump (hL:Odd L.val)(i:Keys t)(y) : jump i (fun v=>network (install ∘ R) z b v y)=(fun v=>network (install ∘ update R i.1 (forwardC L (R i.1) i.2)) z b v y):= by
  funext v; let x:= publish z b v
  have hu : publish z b (v+arc i)= shuttle i.1.succ (Lattice.step i.2) x:= by
    let r:= shuttle i.1.succ (Lattice.step i.2) x
    have ht:= retrieve r; convert ht using 2 -- easier rw sub eq?
    all_goals try simp only [r,shuttle_rule, Fin.succ_ne_zero,show (0:Fin (t+1))≠_ from (Fin.succ_ne_zero i.1).symm, if_false,x,publish,legLane,Fin.cons_zero, add_zero]
    all_goals try simp [r,x,shuttle_alpha,shuttle_deg] -- 
  let t (j:Fin t):= install (R j) (x j.succ) (y j); let q j:= install (R j) ((shuttle i.1.succ (Lattice.step i.2) x) (Fin.succ j)) (y j); let u j:= install (update R i.1 (forwardC L (R i.1) i.2) j) (x j.succ) (y j)
  have hp j (he:j≠i.1) : q j=t j ∧ u j=t j:= by unfold q u t; rw [update_of_ne he,shuttle_rule,if_neg (show j.succ≠i.1.succ from fun h=> he (Fin.succ_inj.mp h))]; simp
  simp only [jump,network]; rw [hu]; change (∏ j,q j)-(∏ j,t j)=∏ j,u j; rw [← mul_prod_erase _ q (mem_univ i.1),← mul_prod_erase _ t (mem_univ i.1),← mul_prod_erase _ u (mem_univ i.1),show (∏ j∈Finset.univ.erase i.1,q j)=_ from (prod_congr rfl fun j hj=>(hp j (mem_erase.mp hj).1).1),show (∏ j∈Finset.univ.erase i.1,u j)=_ from (prod_congr rfl fun j hj=>(hp j (mem_erase.mp hj).1).2), ← sub_mul]; congr 1; unfold t q u; rw [shuttle_rule,if_pos rfl,update_self,install_forward _ hL]
lemma network_t (hL:Odd L.val) (u:Fin t→List Axis)(i:Fin t×Axis)(y:Fin t→Node β) : jump i (fun v=>network (fun j=>install (advanceC L (R j) (u j))) z b v y) = (fun v=> network (fun j=>install (advanceC L (R j) (update u i.1 (i.2::u i.1) j))) z b v y):= by
  let A i:= advanceC L (R i) (u i); have he : install ∘ update A i.1 (forwardC L (A i.1) i.2)=(fun j=>install (advanceC L (R j) (update u i.1 (i.2::u i.1) j))) := by ext j x q; by_cases h:j=i.1 <;> simp [h,A,advanceC]
  rw [← he]; exact web_jump hL i y
lemma net_iter (hL:Odd L.val)(l:List (Keys t)) (u:Fin t→List Axis)(H:∀ i (v:List Axis), v.length ≤ (u i).length+l.length → ∀ x, Balanced (install (advanceC L (R i) v) x) (hook σ n L x) (c/(L.val:ℝ)^(1+v.length))) (y:Node β)(v:Tailor t):
    Balanced (fun y'=> iterate (fun x=>network (fun j=>install (advanceC L (R j) (u j))) z b x y') l v) (gas σ n y)
      ((thread σ n L z b y v)*(∏ i,c/(L.val:ℝ)^(1+(u i).length)) / (L.val:ℝ)^l.length):= by
  induction l generalizing u with
  | nil=> simp only [iterate,List.length_nil,pow_zero,div_one]; exact web_grows _ _ (fun i=>H i _ le_rfl) _ _
  | cons i l ih=>
    let j:= i.1; let U:= update u j (i.2::u j)
    have he k : (U k).length+l.length ≤ (u k).length+(i::l).length:= by by_cases h:k=j<;> simp [U,h] <;> omega
    have hh := ih U fun j u h=> H j u (h.trans (he j)); simp_rw [iterate,network_t hL]; convert hh using 1; simp only [List.length_cons,U]; rw [pow_succ]; clear hh; let f (s:List Axis):= c/(L.val:ℝ)^(1+s.length)
    have hr : ∏ i,f (U i)=(∏ i,f (u i))/(L.val:ℝ):= by
      rw [← mul_prod_erase _ (fun i=>f (U i)) (mem_univ j), ← mul_prod_erase _ (fun i=>f (u i)) (mem_univ j),mul_div_right_comm]; apply congr_arg₂ _
      · unfold f U; rw [update_self,List.length_cons,← add_assoc,pow_succ]; field_simp
      exact prod_congr rfl fun i hi=>congr_arg f (update_of_ne (mem_erase.mp hi).1 ..)
    change _= _ * (∏ i,f (U i))/_; rw [hr]; field_simp; ring
-- For far evaluation of the unexpanded web. φ exponent dynamic; `k` is any spare polynomial power.
lemma leg_weight (σ η:ℝ≥0)(t n:ℕ)(x:Breed t (Node α))(v:Tailor t) (h:v=degree x) (L:Side)(he : (2*(η:ℝ)/(L.val:ℝ))*(t+1) ≤ σ):
    Real.exp ((2*(η:ℝ)/(L.val:ℝ))*size v)*(1+(size v:ℝ))^n ≤ (t+1:ℝ)^n * (bath σ n α).bill x := by
  have H:= leg_price (n:=n) x v h (by positivity) he
  calc
    _ ≤ Real.exp _ * ((t+1:ℝ)^n*(1+(size v:ℝ)/(t+1))^n):= by rw [← mul_pow]; gcongr _ * ?_^n; have h:0<t+1:=(show 0<t+1 by omega); have hv:= Nat.cast_nonneg (α:=ℝ) t; field_simp; nlinarith
    _ ≤ _:= by rw [mul_left_comm]; gcongr
lemma spokeFar (σ:ℝ≥0)(n m:ℕ)(L:Side)(he:L.val≤m) : spokes σ n m L ≤ (mist σ n 6)* (Real.exp ((2*(σ:ℝ)/(L.val:ℝ))*m)*((1+(m:ℝ))/(L.val:ℝ))^n) := by
  let x:= 2*(m:ℝ)/(L.val:ℝ); have hv:1≤((m:ℝ)/(L.val:ℝ)):= (one_le_div (side_pos L)).2 (by exact_mod_cast he)
  have ht : 1 + (4+x) ≤ 7*((1+(m:ℝ))/ (L.val:ℝ)) := by unfold x; rw [add_div,mul_div_assoc]; linarith only [hv, show 0 ≤ 1/(L.val:ℝ) by positivity]
  have hQ : (Real.exp (σ*(4+x))) ≤ Real.exp (σ*6)* Real.exp ((2*(σ:ℝ)/(L.val:ℝ))*m) := by rw [← Real.exp_add]; apply Real.exp_monotone; unfold x; have hf:= NNReal.coe_nonneg σ; field_simp; nlinarith [side_pos L]
  rw [spokes, mist, mist]; apply le_trans (mul_le_mul hQ (d:=7^n* ((1+(m:ℝ))/ (L.val:ℝ))^n) (?_) (by positivity) (by positivity)) -- type?
  · ring_nf; rfl
  rw [← mul_pow]; gcongr

-- first apply ∆ stuff, then size-cost union. Distribution of stronger weights. 
lemma Balanced.sum_v {f:Fin k→X→ℝ}{a:ℝ}{u:X→ℝ} (h:∀ i,Balanced (f i) u a)(hu:∀ x,0≤u x): Balanced (fun x=>∑ i:Fin k,f i x) u ((k:ℝ)*a):= by
  rw [show (k:ℝ)*a= ∑ i:Fin k,a by simp]; refine budget_mono (budget_over Finset.univ (fun i x=> u x * ‖f i x‖) _ (fun i _=> h i)) (fun _=> mul_nonneg (hu _) (norm_nonneg _)) (fun x=> ?_); rw [← mul_sum]; apply mul_le_mul_of_nonneg_left ?_ (hu _); exact norm_sum_le ..
lemma plume (hL: Odd L.val)(σ η δ:ℝ≥0)(H:∀ i (v:List Axis), v.length ≤ k→∀ x, Balanced (install (advanceC L (R i) v) x) (hook η n L x) (c/(L.val:ℝ)^(1+v.length))) (hk:k≤n) (hv:η≤δ) (he:(2*(η:ℝ)/(L.val:ℝ))*(t+1) ≤ σ)(hc:0≤ c)(y:Node β) (v: Tailor t):
    Balanced (fun q=> Quill.tail k (fun x=>network (install ∘ R) z b x q) v) (gas η n y)
      (((mist δ n 6)*(k+1)*(t+1:ℝ)^n)* ((bath σ n α).bill (publish z b v)*hook η n L (z,b 0) y)* (c/(L.val:ℝ))^t/(L.val:ℝ)^k):= by -- k+1 includes newton
  let D:= hook η n L (z,b 0) y*(c/(L.val:ℝ))^t; let d:= spokeFar η; let a:=mist δ n 6; let s:ℝ:= size v; let r:ℝ:=L.val; let f:= network (install ∘ R) z b; let Z:= (1+s)/r; let u:= gas (t:=t) η n y; have hu q: 0≤u q:= by unfold u gas; positivity
  have Hr := side_pos L; have hr:1≤r:= by unfold r; exact_mod_cast L.property
  have hs:0≤s:= Nat.cast_nonneg _; have ha: 1≤ a:= mist_one (by norm_num); have hX:0≤Z:= by unfold Z r; positivity
  have hD:0≤D:= mul_nonneg (mist_pos (Nat.cast_nonneg _)).le (by positivity)
  have hd : mist η n 6 ≤ a:= by unfold a mist; gcongr
  let W := Real.exp ((2*(η:ℝ)/r)*s); have hW:1≤ W:= Real.one_le_exp (by unfold s r; positivity)
  have hw (x:Tailor t)(l:List (Keys t))(hp:l.length≤k): Balanced (fun q=> iterate (fun x=> f x q) l x) u (spokes η n (size x) L * D / r^l.length):= by
    have hi:= net_iter (z:=z) (b:=b) hL l (fun _=>[]) (fun i k he=> H i k ((show k.length ≤ l.length from (by simpa using he)).trans hp)) y x
    simpa only [f,u,Function.comp_def,List.length_nil,add_zero,pow_one,prod_const,card_univ,Fintype.card_fin,advanceC,thread,D,r,mul_assoc] using hi
  have near {m:ℕ} (h:m≤L.val) : spokes η n m L ≤ a:= by
    apply le_trans _ hd; apply mist_le (by positivity); have hm : (m:ℝ)≤ (L.val:ℝ):= by exact_mod_cast h
    field_simp; nlinarith
  have hp: Balanced (fun q=> Quill.tail k (fun x=> f x q) v) u (a*D*(k+1)*(W * (1+s)^n)/r^k):= by
    rcases le_total (size v) L.val with h|h
    · have hl : Balanced (fun q=> Quill.tail k (fun x=> f x q) v) u ((a*D/r^k)*(1+(size v:ℝ))^k):= penciled hu f _ r (by positivity) (fun l hl x hx=> by apply budget_loosen (hw x l hl.le); rw [hl]; gcongr; apply near; dsimp [r] at hx; exact_mod_cast hx) _ (show (size v:ℝ) ≤ (L.val:ℝ) from by exact_mod_cast h)
      apply budget_loosen hl; change _ / _ * (1+s)^k ≤ _; rw [←mul_div_right_comm]; gcongr ?_ / _; calc
        _ ≤ a*D*(W*(1+s)^n):= by apply mul_le_mul_of_nonneg_left ?_ (by positivity); apply le_trans ?_ (le_mul_of_one_le_left (by positivity) hW); gcongr; simp [hs]
        _ ≤ _:= mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) (by simp)) (by positivity)
    have hZ:1≤ Z:= by
      rw [← div_self (zero_lt_one.trans_le hr).ne']; apply div_le_div_of_nonneg_right _ (by positivity); have hi : r≤s:= by unfold r s; exact_mod_cast h
      linarith
    let p:=a*D*W*Z^n; have hp:0≤p:=by unfold p; positivity
    have hl : Balanced (f v) u p:= by
      apply budget_loosen (hw v [] (Nat.zero_le _)); simp only [List.length_nil,pow_zero,div_one]; unfold p; apply (mul_le_mul_of_nonneg_right (spokeFar _ n _ L h) hD).trans; change mist _ _ _* (W * Z^n)*D≤ _; calc
        _ ≤ a*(W*Z^n)*D:= by gcongr
        _ = _:= by ring
    have he (q): Quill.tail k (fun x=>f x q) v = f v q - ∑ j : Fin k, piece j.val (fun x=> f x q) v:= by rw [Fin.sum_univ_eq_sum_range (fun j:ℕ=> piece j (fun x=> f x q) v) k]; rfl
    have hh (j:ℕ)(hj:j≤k) : Balanced (fun q=>piece j (fun x=>f x q) v) u p:= by
      refine budget_loosen (pencil hu f j (C:=a*D/r^j) (by positivity) (fun l ht=> budget_loosen (hw 0 l (ht ▸ hj)) (by rw [ht]; gcongr; apply near; simp [Laurent.size])) v) ?_; unfold p Z; change _/ _ * (1+s)^j ≤ _; rw [←mul_div_right_comm, mul_div_assoc,← div_pow]; change _* Z^j≤ _*Z^n; exact mul_le_mul (le_mul_of_one_le_right (by positivity) hW) (pow_le_pow_right₀ hZ (hj.trans hk)) (by positivity) (by positivity)
    apply budget_loosen (budget_mono (budget_plus hl (Balanced.sum_v (f:=fun j:Fin k=> fun q=>piece j.val (fun x=>f x q) v) (fun j=> hh _ j.isLt.le) hu)) (g:=fun q=> u q * ‖Quill.tail k (fun x=> f x q) v‖) (fun _=> mul_nonneg (hu _) (norm_nonneg _)) (fun q=> by rw [he,← mul_add]; exact mul_le_mul_of_nonneg_left (norm_sub_le ..) (hu _)))
    have hO : p≤ a*D*(W*(1+s)^n)/r^k:= by unfold p Z; rw [div_pow]; change _ *( _/ _ ) ≤ _; rw [← mul_div_assoc,mul_assoc (a*D)]; gcongr
    apply (add_le_add hO (mul_le_mul_of_nonneg_left hO (Nat.cast_nonneg (α:=ℝ) k))).trans_eq; ring
  refine budget_loosen hp ?_; have hw := leg_weight σ η t n (publish z b v) v (deg_issue z b v).symm L he; change W * _ ≤ _ at hw; refine le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw (show 0≤a*D*(k+1) by positivity)) ?_) ?_ -- b arg wrong
  · positivity
  apply le_of_eq; unfold a D r; ring
end
end YM.Pulse.Spine
