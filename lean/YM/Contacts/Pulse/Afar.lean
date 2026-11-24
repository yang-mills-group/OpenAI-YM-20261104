import YM.Contacts.Pulse.Pelt
import YM.Contacts.Pulse.Bind
import YM.Contacts.Pulse.Registry
namespace YM.Pulse.Spine
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration Quill
open scoped Classical Topology BigOperators NNReal ENNReal
noncomputable section
variable {α β X Y Z : Type} {L: Side}{σ η δ:ℝ≥0}{n t:ℕ}
def mist (σ:ℝ≥0)(n:ℕ)(r:ℝ):ℝ:= Real.exp (σ*r)*(1+r)^n
lemma mist_pos (h:0≤a) : 0 < mist σ n a:= by unfold mist; positivity
@[simp] lemma mist_zero : mist σ n 0=1:= by simp [mist]
lemma mist_join {a b:ℝ}(ha:0≤a)(hb:0≤b) : mist σ n (a+b) ≤ mist σ n a*mist σ n b:= by
  unfold mist; rw [_root_.mul_add, Real.exp_add,mul_mul_mul_comm (Real.exp _) ((1+a)^n), ← mul_pow]; gcongr; nlinarith
lemma mist_le {a b:ℝ}(ha:0≤a)(he:a≤b) : mist σ n a≤mist σ n b:= by unfold mist; gcongr
lemma mist_one {a:ℝ}(h:0≤a): 1≤ mist σ n a := mist_zero (σ:=σ) (n:=n) ▸ mist_le le_rfl h
def bath (σ:ℝ≥0)(n:ℕ)(α:Type): Range (Node α) where
  fee x y:= ⟨mist σ n (size (y.1-x.1)), (mist_pos (Nat.cast_nonneg _)).le⟩
  one _ _:= mist_one (Nat.cast_nonneg _)
  flat x:= NNReal.eq (by change mist _ _ _=1; simp [Laurent.size])
  mirror x y:= NNReal.eq (by rw [← neg_sub y.1 x.1,size_neg])
  fold a b c:= NNReal.coe_le_coe.mp ((mist_le (Nat.cast_nonneg _) (show (size (c.1-a.1):ℝ) ≤ size (b.1-a.1) + (size (c.1-b.1):ℝ) from by exact_mod_cast (le_trans (a:=size (c.1-a.1)) le_rfl (show _≤_ by rw [show c.1-a.1=b.1-a.1+(c.1-b.1) from by abel]; apply size_add)))).trans (mist_join (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
def hook (σ:ℝ≥0)(n:ℕ)(L:Side)(x:Node α)(y:Node β) := mist σ n (size (y.1-rent L x.1))
def spokes (σ:ℝ≥0)(n:ℕ)(p:ℕ)(L:Side):ℝ:= mist σ n ((4:ℝ)+ 2*(p:ℝ)/(L.val:ℝ)) -- remove spurious
lemma hook_span (x y:Node α)(a b:Node β) {v:ℕ} (h:size (y.1-x.1) ≤2*v) : (bath η n β).step a b ≤ hook η n L x a * spokes η n v L * hook η n L y b:= by
  let f (x y:Cover):= size (y-x); have he : size (b.1-a.1) ≤ size (a.1-rent L x.1)+size (rent L y.1-rent L x.1)+size (b.1-rent L y.1):= by
    calc
      _ = Laurent.size ((-(a.1-rent L x.1)+(rent L y.1-rent L x.1))+(b.1-rent L y.1)) := by rw [show (-(a.1-rent L x.1)+(rent L y.1-rent L x.1))+(b.1-rent L y.1)=b.1-a.1 by abel]
      _ ≤ _:= (size_add ..).trans (by gcongr; exact (size_add ..).trans_eq (by rw [size_neg]))
  change mist η n _≤_
  apply (mist_le (by positivity) (Nat.cast_le (α:=ℝ).mpr he)).trans; push_cast
  apply (mist_join (by positivity) (by positivity)).trans; apply mul_le_mul_of_nonneg_right ?_ (mist_pos (by positivity)).le; apply (mist_join (by positivity) (by positivity)).trans; unfold hook spokes; apply mul_le_mul_of_nonneg_left ?_ (mist_pos (by positivity)).le
  apply mist_le (by positivity); apply (stride ..).trans; rw [add_comm]; gcongr; exact_mod_cast h
lemma canopy (σ:ℝ≥0)(n:ℕ)(x: Breed t (Node α))(y:Breed t (Node β)) : (bath σ n β).bill y ≤ spokes σ n (size (degree x)) L * ∏ i,hook σ n L (x i) (y i):= by
  let g i:=hook σ n L (x i) (y i); let r:=spokes σ n (size (degree x)) L; have hh j:1≤g j:= mist_one (Nat.cast_nonneg _); have hz : 1≤r:= by unfold r spokes; exact mist_one (by positivity)
  have hw : 1≤r*∏ i,g i:= one_le_mul_of_one_le_of_one_le hz (one_le_prod fun i _=> hh _)
  refine (bath σ n β).wide _ hw fun i j=> ?_; by_cases he:i=j; · subst j; unfold Range.step; rw [Range.flat]; exact hw
  apply (hook_span (x i) (x j) _ _ (L:=L) (η:=σ) (between x j i)).trans -- η!
  rw [mul_comm (hook _ _ _ _ _) _,mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le_one.trans hz); change g i*g j ≤ _; rw [show g i*g j=∏ j∈{i,j},g j from by rw [prod_insert (by simpa using he),Finset.prod_singleton]]; exact prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) (fun i _=> zero_le_one.trans (hh i)) (fun i _ _=>hh i)

-- geometry conversion with no inverse width. input Θ slot normalization soft. 
lemma leg_price (x:Breed t (Node α))(v:Tailor t)(h:v=degree x) {u:ℝ} (hu:0≤u) (hp:u*(t+1)≤ σ) : Real.exp (u*(size v:ℝ)) * (1+(size v:ℝ)/(t+1))^n ≤ (bath σ n α).bill x:= by
  let g (i:Fin (t+1)) := size ((x i).1-(x 0).1); let b:= Finset.univ.sup g
  obtain ⟨j,-,hj⟩ : ∃ j∈(univ:Finset (Fin (t+1))),b=g j:= Finset.exists_mem_eq_sup _ Finset.univ_nonempty g
  have he : size v≤ (t+1)*b:= by
    rw [h,degree_code]; calc
      _ ≤ ∑ i:Fin t,b:= sum_le_sum fun i _=> le_sup (mem_univ (Fin.succ i))
      _ ≤ _ := by simp [add_mul]
  have hV : (size v:ℝ) ≤ ((t:ℝ)+1)*b:= by exact_mod_cast he
  apply le_trans _ ((bath σ n α).width x 0 j); change _≤ Real.exp (σ*(g j:ℝ))*(1+(g j:ℝ))^n; rw [← hj]; gcongr Real.exp ?_ * (1+?_)^n
  · apply (mul_le_mul_of_nonneg_left hV hu).trans; rw [← mul_assoc]; gcongr
  rw [div_le_iff₀ (by positivity),mul_comm]; exact hV
end
end YM.Pulse.Spine
namespace YM.Pulse.Spine
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration Quill
open scoped Classical Topology BigOperators NNReal ENNReal
noncomputable section
variable {α β X Y Z : Type} {L: Side}{σ η δ:ℝ≥0}{n t:ℕ}
lemma coat_price (η:ℝ≥0)(n:ℕ)(he:0<η):∃ c:ℝ,1≤c∧∀ σ:ℝ≥0, (σ:ℝ)*2≤ η → ∀ L:Side,∀ a:Node α,∀ b:Node β, hook σ n L a b ≤ c*access L η a b:= by
  obtain ⟨c,hc,H⟩:= expPocket η ((η:ℝ)/2) n (by linarith only [NNReal.coe_pos.mpr he]); refine ⟨max 1 c,le_max_left ..,fun σ h L a b=>?_⟩
  let d:ℝ:= size (b.1-rent L a.1); have hd:0≤d:=Nat.cast_nonneg _; change Real.exp _ * _ ≤ _
  rw [mul_comm]; unfold access; apply le_trans _ ((H d hd).trans _)
  · gcongr; linarith
  change c*Real.exp ((η:ℝ)*d) ≤ max 1 c * Real.exp ((η:ℝ)*(d+2)); gcongr <;> first | exact le_max_right .. | norm_num
lemma Weirs.coupons {t v:X→Y→ℝ}{G:X→Y→ℝ}{a b d:ℝ}(h:YM.Pulse.Weirs t G a b)(hd:0≤d)(hp:∀ x y,0≤v x y)(he:∀ x y,v x y≤d*t x y): YM.Pulse.Weirs v G (d*a) (d*b):= by
  have H x y : ‖G x y‖*v x y≤ d*(‖G x y‖*t x y) := (mul_le_mul_of_nonneg_left (he x y) (norm_nonneg _)).trans_eq (mul_left_comm ..)
  exact ⟨mul_nonneg hd h.left,mul_nonneg hd h.right,fun y=> budget_mono (budget_scale hd (h.columns y)) (fun x=> mul_nonneg (norm_nonneg _) (hp _ _)) (fun x=> H x y),fun x=> budget_mono (budget_scale hd (h.rows x)) (fun y=> mul_nonneg (norm_nonneg _) (hp _ _)) (fun y=> H x y)⟩
lemma coatContract (η:ℝ≥0)(n:ℕ)(he:0<η) (α β:Type)[Fintype α][Fintype β](D:ℝ)(hD:0≤D) : ∃ c:ℝ,0≤c∧∀ L:Side,∀ σ:ℝ≥0, (σ:ℝ)*2≤η→ ∀ R:Cross L α β,∀ k:ℕ, Row.strip R η (D/(L.val:ℝ)^k) → Weirs (hook σ n L) (install R) ((L.val:ℝ)^4*(c/(L.val:ℝ)^k)) (c/(L.val:ℝ)^k) := by
  obtain ⟨c,hc,H⟩:= coat_price (α:=α) (β:=β) η n he; let d:=c*(foot α β*beamPrice η D); have hd : 0≤ d := by unfold d beamPrice foot; positivity
  refine ⟨d,hd,fun L σ h R k hp=> ?_⟩
  convert Weirs.coupons (v:=hook σ n L) (t:=access L η) (straight (R:=fun _: Fin (0+1)=> R) (i:=0) hp (by positivity)) (zero_le_one.trans hc) (fun x y=>(mist_pos (σ:=σ) (n:=n) (Nat.cast_nonneg (α:=ℝ) (size (y.1-rent L x.1)))).le) (H σ h L) using 1 <;> unfold d beamPrice <;> ring
end
end YM.Pulse.Spine
