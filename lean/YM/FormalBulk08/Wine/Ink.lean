import YM.FormalBulk08.Wine.Car

/-! Adjacent coupling data. θ normalization from unmasked quadratic value.
Check correctness BOTH directions. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wine
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge City Cork
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {V I : Type} (H : Pence)

-- data = 1+ω included from zeroth

def Fresh (P : Pence):=coeff 0 P=1
def Still (P : Pence):=∀ j, j%2=1 → coeff j P=0
lemma Fresh.mul {A B:Pence}(h:Fresh A)(e:Fresh B): Fresh (A*B):= by unfold Fresh at *; rw [coeff_zero_eq_constantCoeff_apply, map_mul,←coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply,h,e,one_mul]
lemma Fresh.pow {A:Pence}(h:Fresh A)(r): Fresh (A^r) := by induction r with
   | zero=> rw [pow_zero]; simp [Fresh]
   | succ r ih=> rw [pow_succ];exact ih.mul h
lemma Still.mul {A B:Pence}(h:Still A)(e:Still B): Still (A*B):= by
    intro i hi;rw [coeff_mul]; apply Finset.sum_eq_zero; intro v hv; rw [Finset.mem_antidiagonal] at hv
    by_cases he:v.1%2=1; rw [h v.1 he,zero_mul]; rw [e v.2 (by omega),mul_zero]
lemma Still.pow {A:Pence}(h:Still A)(r): Still (A^r):=by
   induction r with
   | zero=> rw [pow_zero];intro i hi;rw [coeff_one];exact if_neg (by omega)
   | succ r ih=> rw [pow_succ];exact ih.mul h

def violet := expan (C (1/2:ℝ) * covelog H)
def nextU := invOfUnit (violet H) 1
def wake := X * nextU H
lemma wake_phi : coeff 0 (wake H)=0 := by rw [wake,coeff_zero_eq_constantCoeff_apply,map_mul];simp
lemma fresh_N : Fresh (nextU H):= by rw [Fresh, coeff_zero_eq_constantCoeff_apply]; simp [nextU]
lemma wake_tip : coeff 1 (wake H)=1:= by rw [wake, show (1:ℕ) = 0+1 from rfl, coeff_succ_X_mul]; exact fresh_N H
lemma wake_unit : IsUnit (coeff 1 (wake H)) := by rw [wake_tip];exact isUnit_one

def runic := PowerSeries.substInvOfIsUnit (wake H) (wake_unit H)
def bookH := afterX (runic H) 1
def bookU := invOfUnit (bookH H) 1
lemma runic_phi : coeff 0 (runic H)=0:= by rw [coeff_zero_eq_constantCoeff_apply]; simp [runic]
lemma forward_green : X * bookH H=runic H:= by simpa only [pow_one] using! after_rope (runic H) 1 (fun _ hi=> Nat.lt_one_iff.mp hi ▸ runic_phi H)
lemma back_merge : PowerSeries.subst (runic H) (wake H)=X := subst_substInvOfIsUnit_right _ ((coeff_zero_eq_constantCoeff_apply _).symm.trans (wake_phi H)) _
lemma front_merge : PowerSeries.subst (wake H) (runic H)=X := subst_substInvOfIsUnit_left _ ((coeff_zero_eq_constantCoeff_apply _).symm.trans (wake_phi H)) _
lemma book_credit : bookH H * ((nextU H).subst (runic H))=1:= by
    apply mul_left_cancel₀ X_ne_zero; have he:=back_merge H; rw [wake,subst_mul (tribe (runic_phi H)),subst_X (tribe (runic_phi H))] at he
    rw [←mul_assoc,forward_green,mul_one]; exact he
lemma book_fresh : Fresh (bookH H):= by
    have he:=congr_arg (coeff 0) (book_credit H); rw [coeff_zero_eq_constantCoeff_apply, map_mul,←coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply, peep (runic_phi H), fresh_N H,mul_one] at he; exact he.trans coeff_zero_one
lemma book_guard : Fresh (bookU H):= by rw [Fresh,coeff_zero_eq_constantCoeff_apply]; simp [bookU]
lemma book_equal : bookH H * bookU H=1 := mul_invOfUnit _ _ ((coeff_zero_eq_constantCoeff_apply _).symm.trans (book_fresh H))
lemma blue_credit : bookU H= (nextU H).subst (runic H) := mul_left_cancel₀ (show bookH H≠0 from fun he=> by have h:=book_fresh H; simp [Fresh,he] at h) ((book_equal H).trans (book_credit H).symm)
lemma violet_flour (h:Fresh H): violet H*violet H=H:= by
   have he: coeff 0 (C (1/2:ℝ)*covelog H)=0:=by rw [coeff_C_mul,covelog_rank h,mul_zero]
   rw [violet,expan_mul he he,←add_mul,←map_add,show (1/2:ℝ)+1/2=1 by norm_num,map_one,one_mul,expan_after h]
lemma violet_height (h:Fresh H): Fresh (violet H):= expan_zero (by rw [coeff_C_mul,covelog_rank h,mul_zero])
lemma next_foot (h:Fresh H): violet H*nextU H=1:= mul_invOfUnit _ _ ((coeff_zero_eq_constantCoeff_apply _).symm.trans (violet_height H h))
lemma post_grid (h:Fresh H): H*(nextU H)^2=1 := by
   nth_rw 1 [←violet_flour H h]; rw [←pow_two,←mul_pow, next_foot H h,one_pow]
lemma correction_read (h:Fresh H): H.subst (runic H)*(bookU H)^2=1:= by
   rw [blue_credit,← subst_pow (tribe (runic_phi H)),←subst_mul (tribe (runic_phi H)),post_grid H h];rw [←coe_substAlgHom (tribe (runic_phi H)),map_one]
-- parity via motion of g negative

def flipN (q:Pence):= rescale (-1:ℝ) q
lemma still_flip {f:Pence}: Still f ↔flipN f=f:= by
   constructor
   · intro h; ext1 n;rw [flipN,coeff_rescale]; by_cases he:n%2=0
     · rw [(Nat.even_iff.mpr he).neg_one_pow,one_mul]
     rw [h n (by omega),mul_zero]
   intro h i hi; have hx:=congr_arg (coeff i) h;rw [flipN,coeff_rescale,(Nat.odd_iff.mpr hi).neg_one_pow] at hx;linarith only [hx]
lemma dressed_even (h:Fresh H)(hP:Still H): Still (violet H):= by
    rw [still_flip]; let u:=flipN (violet H); let p:=violet H
    have he:u^2=p^2:= by rw [pow_two,pow_two]; unfold u flipN p; rw [←map_mul,violet_flour H h]; exact still_flip.mp hP
    have ht:coeff 0 u=coeff 0 p:= by unfold u flipN; simp [coeff_rescale,p]
    apply (sq_eq_sq_iff_eq_or_eq_neg.mp he).resolve_right; intro hi; rw [hi,map_neg, show coeff 0 p=1 from violet_height H h] at ht;norm_num at ht
lemma even_inverse {P Q : Pence}(h: Still P) (hp:P*Q=1): Still Q:= by
   rw [still_flip];have hH:P≠0:= fun e=> by rw [e,zero_mul] at hp;exact zero_ne_one hp
   apply mul_left_cancel₀ hH; nth_rw 1 [← still_flip.mp h]; unfold flipN;rw [←map_mul,hp,map_one]
lemma next_even (h:Fresh H)(hP:Still H): Still (nextU H):= even_inverse (dressed_even H h hP) (next_foot H h)
lemma flip_X (f : Pence): flipN f=f.subst (-X : Pence):= by simp only [flipN,rescale_eq_subst,neg_one_smul]
lemma flip_shim : flipN X=(-X:Pence):= by unfold flipN; simp
lemma wake_odd (h:Fresh H)(hp: Still H): flipN (wake H) = - wake H := by
    have he:= still_flip.mp (next_even H h hp); unfold flipN at *; rw [wake,map_mul, he, show rescale (-1:ℝ) X =_ from flip_shim]; ring
lemma iron (h:Fresh H)(hp:Still H): flipN (runic H)= -runic H := by
   have he:= wake_odd H h hp; rw [flip_X] at he
   let f:=runic H; let u:=wake H
   have hn : HasSubst (-X:Pence):= tribe (by simp)
   have hu : HasSubst u:= tribe (wake_phi H); have hf : HasSubst f:= tribe (runic_phi H)
   have hx : PowerSeries.subst u (f.subst (-X:Pence))=(-X:Pence):= by
       rw [subst_comp_subst_apply hn hu, show PowerSeries.subst u (-X:Pence)=-u by rw [←coe_substAlgHom hu,map_neg,coe_substAlgHom,subst_X hu], show (-u:Pence)=_ from he.symm,← subst_comp_subst_apply hu hn f, front_merge];exact subst_X hn
   rw [flip_X];change (f.subst (-X:Pence))= -f
   have hg : PowerSeries.subst X (f.subst (-X:Pence))= f.subst (-X:Pence):= ?id
   have hk:= congr_arg (PowerSeries.subst f) hx; rw [subst_comp_subst_apply hu hf,back_merge,hg,show PowerSeries.subst f (-X:Pence)=-f by rw [←coe_substAlgHom hf,map_neg,coe_substAlgHom,subst_X hf]] at hk; exact hk
   case id=> simp
lemma even_book (h:Fresh H)(hp:Still H): Still (bookH H):= by
    rw [still_flip];apply mul_left_cancel₀ X_ne_zero; have he:=iron H h hp; rw [←forward_green H] at he; unfold flipN at *;rw [map_mul,show rescale (-1:ℝ) X=_ from flip_shim,neg_mul] at he; exact neg_injective he
lemma even_coupon (h:Fresh H)(hp:Still H): Still (bookU H):= even_inverse (even_book H h hp) (book_equal H)
end YM.FormalBulk08.Wine
