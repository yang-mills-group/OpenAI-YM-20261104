import YM.OPE.Compatible.Tides.Dash
/-!
# Taylor moment costs through small distances -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{d r B:ℝ}{g:ℕ→ Cover→ℝ}{k j m u o K:ℕ}{R:ℕ→ℕ}{f t:Cover→ℝ}
lemma stepper (hp:0 ≤ B)(he:∀ l:List Axis,l.length<j→ dvol l t 0=0)(hx:∀ l:List Axis,l.length=j→∀ x,size x≤ K→‖dvol l t x‖ ≤ B)(x:Cover)(hv:size x≤ K):‖t x‖≤ (size x:ℝ)^j*B:=by
   let g(x:Cover):Unit→ℝ:= fun _=> t x; have hg(l:List Axis)(x:Cover):dvol l g x=dvol l t x • (1:Unit→ℝ):=by rw [show g=(fun x=>t x • (1:Unit→ℝ)) from funext fun i=>funext fun _=>by simp [g]]; exact slot_run ..
   have hh:= polynomial_walk (I:=Axis) (k:=K) (c:=B) (f:=g) j hp (w:=fun _ => 1) (fun i=>zero_le_one) (fun l h=>by rw [hg,he l h, zero_smul]) (fun l h x h' =>?_) x hv; rotate_left
   · let L:=dvol l t x; rw [hg]; have hp:‖L‖ ≤ B:=hx l h x h'
     unfold Sack RG.SumBudget; refine ⟨fun i=>by simp, (hasSum_fintype _).summable,?_⟩; rw [tsum_fintype]; simpa using! hp -- first simp maybe fails
   have hx0 := hh.single (); simpa only [one_mul] using! hx0
lemma polishP (h:Port U d k g)(hr:r<d)(hn:∀ᶠ i in atTop, U.h i * R i≤r)(j:ℕ):∃ C≥0,∀ᶠ i in atTop,∀ x∈pod (R i), ‖g i x-sketch j (g i) x‖ ≤ (notch x:ℝ)^j*C*U.h i^(k+j):=by
   let A:=Port.listX j; have hd(v:A):v.val.toList.length=j:=by rw [Multiset.length_toList]; exact (Port.cardA v.val).1 v.property
   choose c hc hC using fun v:A=>(h (v.val).toList).near r hr; let t:=∑ v:A,c v; have hp:0 ≤ t:=Finset.sum_nonneg (fun i _=> hc i); refine ⟨t,hp,?_⟩
   filter_upwards [hn, eventually_all.mpr hC] with i hi H x hx; let f:=g i-sketch j (g i); have hw:0 < U.h i:=U.h_pos i
   have hf(l:List Axis)(hl:l.length=j)(p:Cover)(ht:size p≤ R i): ‖dvol l f p‖ ≤ t*U.h i^(k+j):=by
       rw [show f=g i-_ from rfl,run_sub,sketch_fizz _ _ _ hl.ge,sub_zero]
       let v:A:= ⟨(l:Multiset Axis),(Port.cardA _).mpr hl⟩; have hg:=H v p (le_trans (mul_le_mul_of_nonneg_left (show (size p:ℝ)≤(R i:ℝ) by exact_mod_cast ht) hw.le) hi); change ‖dvol _ (g i) p‖≤ _ at hg; rw [hd] at hg; rw [← mapped]; exact hg.trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i (_:i∈Finset.univ)=> hc i) (Finset.mem_univ _)) (pow_nonneg hw.le _))
   refine (stepper (t:=f) (show 0≤ t*U.h i^(k+j) by positivity) (fun l h=>?_ ) hf x (in_pod.mp hx)).trans ?_ -- remove f param
   · unfold f; rw [run_sub,sketch_hits _ _ h, sub_self]
   exact le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (show (size x:ℝ)≤ notch x by unfold notch; push_cast; linarith) j) (by positivity)) (le_of_eq (by ring))
lemma unfog (hn:Crown U R)(ht:Port U d k g)(hr:r<d)(he:∀ᶠ i in atTop,U.h i*R i≤r)(hp:0 ≤ B)(hw:∀ x,‖f x‖ ≤ B/(notch x:ℝ)^(j+4)):
   Sake U (k+j) (fun i=> ∑ x∈pod (R i),f x*(g i x-sketch (j+1) (g i) x)):=by
   obtain ⟨C,hC,H⟩:=polishP ht hr he (j+1); obtain ⟨M,hM,L⟩:= hn.big; apply coseal (s:=16*(B*C)*M) ?_ (by positivity)
   filter_upwards [H,L] with i hi hh; let A:=U.h i; have ha:0 < A:=U.h_pos i; grw [norm_sum_le]; apply le_trans (fade_low (f:=fun x=> f x*(g i x-sketch (j+1) (g i) x)) (k:=3) (r:=0) (B:=B*C*A^(k+(j+1))) (fun x hx=>?_) (by positivity) rfl) ?_
   swap
   ·  rw [norm_mul]; grw [hw,hi x hx]; have hx:0<(notch x:ℝ):=Nat.cast_pos.mpr (notch_one x); unfold A; exact le_of_eq (by rw [pow_add (notch x:ℝ) j,pow_succ]; field_simp; ring)
   rw [zero_add,pow_one]; apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 16*(B*C))) (pow_nonneg ha.le (k+j))); change _≤ 16*(B*C)*(A*((R i:ℝ)+1))* _; exact le_of_eq (by ring)
lemma brain (hh:Crown U R)(hm:o+4=k+j)(hu:u+k=3)(h:Port U d j g)(hr:r<d)(he:∀ᶠ i in atTop,U.h i* R i≤r)(hp:0 ≤ B)(hw:∀ x,‖f x‖ ≤ B/(notch x:ℝ)^k) : Fruit U o (fun i=>∑ x∈pod (R i), f x*g i x) 0:=by
   obtain ⟨C,hC,H⟩:= h.lo.near r hr; obtain ⟨M,hM,L⟩:=hh.big; apply Fruit.call; apply booze_sake; refine coseal ?_ (show 0 ≤ 16*(B*C)*M^(u+1) by positivity); filter_upwards [H,L,he] with i hv hν hh; let A:=U.h i; have hp:0 < A:=U.h_pos i; grw [norm_sum_le]; apply le_trans (fade_low (f:=fun x=> f x*g i x) (r:=u) (B:=B*C*A^j) (fun x hx=> ?_) (by positivity) (by omega : k+u=3)) ?_ -- remove K
   swap
   · have hy:=in_pod.mp hx; rw [norm_mul]; apply le_trans (mul_le_mul (hw x) (hv x (le_trans ?_ hh)) (norm_nonneg _) (by positivity)); · exact le_of_eq (by unfold A; ring)
     exact mul_le_mul_of_nonneg_left (by exact_mod_cast hy) hp.le
   apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by unfold A at hp; positivity) hν (u+1)) (by positivity : 0≤16*(B*C))) (show 0 ≤ A^o from pow_nonneg hp.le _)); apply le_of_eq; change _= 16*(B*C)*(A*_)^_*A^o; rw [show j=u+1+o from by omega,pow_add A (u+1) o, mul_pow A];ring
end YM.OPE.Balsam
