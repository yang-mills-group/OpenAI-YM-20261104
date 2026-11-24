import YM.X.Chir.Lent
/-!
# ∑ convolution cost and Lips matrix stature. ceilings independent of R or period.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir.Imprint
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e a c:ℝ}
local notation "D"=> Interval.mass
local notation "S"=> Site n
local notation "p"=> fund
variable (x y:Site n)
abbrev balance (x y w:S):= p 3 x w * p 3 y w
abbrev tab (x y w:S):=(D x y+D x w+D y w)*balance x y w
lemma bal (z:S): tab x y z=tab y x z:= by unfold tab balance; rw [comm y x];ring
lemma bal_one (s:Finset S)(hx:∀ i∈s,D x i ≤ D y i): ∑ i∈s,tab x y i ≤ 70000 * p 1 x y:= by
    let A:=D x y; let B:=p 1 x y; have hA:0<A:=pay_pos x y; apply le_trans (binaryF s (fun i=>D x i ≤ A) _ (a:=48000*B) (b:=10368*B) ?_ ?_); rotate_left
    · let v:=s.filter (fun i=>D x i ≤ A); have he:= head_pay x v (R:=A) (fun i hi=> (mem_filter.mp hi).2) hA.le
      calc
       _ ≤ ∑ i∈v,(4*A) * (8*p 3 x y)*p 3 x i := by
           apply sum_le_sum; intro i hi; obtain ⟨hh,h⟩:=mem_filter.mp hi; have hg:= hx i hh; have hv:= tip x i y; have hk:= tip y x i; rw [comm y x] at hk; rw [comm i y] at hv; have hp: D x y≤ 2*D y i:= by linarith
           have hh0:=live (k:=3) x i; have hh1:=live (k:=3) y i; have hh2:=pay_pos x i; have hq: p 3 y i≤ 8*p 3 x y:= by convert! justice (k:=3) x y y i 2 hp using 1; norm_num
           unfold tab balance; rw [mul_assoc (4*A),mul_comm (8*_)]; gcongr <;> try positivity
           change A+D x i+D y i≤ _; linarith only [h,hk,show A=D x y from rfl]
       _ ≤ (4*A)*(8*p 3 x y)*(1500*A):= by rw [← Finset.mul_sum]; gcongr; have h:=live (k:=3) x y; positivity
       _ = _:= by change _= 48000*p 1 x y; unfold A fund; change 0 < D x y at hA; field_simp; ring
    · let v:=s.filter (fun i=>¬ D x i ≤ A); have he:= tails x (k:=5) v (by omega) (R:=A) (fun i hi => (lt_of_not_ge (mem_filter.mp hi).2).le) hA
      calc
       _ ≤ ∑ i∈v,4*p 5 x i:= by
          refine sum_le_sum fun i hi=>?_ ; obtain ⟨hi,h⟩:= mem_filter.mp hi; have hh:=hx i hi; have hg:= justice' (k:=3) x i y i hh; have hv:=tip y x i; rw [comm y x] at hv; unfold tab balance; rw [← raising (k:=5) x i, show 5+1=3+3 from rfl, addF x i, ← mul_assoc 4]; have ht:=lt_of_not_ge h; have hx1:=live (k:=3) x i; have hx2:=live (k:=3) y i; have hx3:=pay_pos x i; gcongr <;> try positivity
          linarith only [ht,hv,show A=D x y from rfl]
       _ ≤ 4*(2592*A⁻¹^(5-4)):= by rw [← Finset.mul_sum]; gcongr
       _ = _:= by change _= 10368*fund 1 x y; unfold fund; unfold A; norm_num; ring
    have he:=live (k:=1) x y; linarith only [he,show B=p 1 x y from rfl]
lemma bal_full (s:Finset S): ∑ i∈s, tab x y i ≤ 140000*p 1 x y:= by
    apply le_trans (binaryF s (fun i=>D x i≤D y i) (tab x y) (bal_one x y _ (fun i hi=> (mem_filter.mp hi).2)) (b:=70000*p 1 x y) ?_); rotate_left; · simp_rw [bal x y]; rw [funds]; exact bal_one y x _ (fun i hi=> (lt_of_not_ge (mem_filter.mp hi).2).le)
    exact le_of_eq (by ring)
lemma bal₀ (s:Finset S): ∑ i∈s,balance x y i ≤ 140000*p 2 x y:= by
    have hx:=pay_pos x y; apply le_of_mul_le_mul_left (a:= D x y) ?_ hx; rw [Finset.mul_sum,mul_left_comm _ 140000,raising (k:=1)]; refine le_trans (Finset.sum_le_sum (g:=tab x y) fun i _=> ?_) (bal_full x y s); apply mul_le_mul_of_nonneg_right; linarith only [pay_pos x i,pay_pos y i]; exact mul_nonneg (live x i|>.le) (live y i|>.le)
lemma bal₁ (s:Finset S): ∑ i∈s,(D x i)*balance x y i≤ 140000*p 1 x y:= by refine (sum_le_sum (g:=tab x y) (fun i _=>?_)).trans (bal_full x y s); apply mul_le_mul_of_nonneg_right; linarith only [pay_pos x y,pay_pos y i]; exact mul_nonneg (live x i|>.le) (live y i|>.le)
-- aftermath
abbrev Paying (x:S)(k:ℕ)(c:ℝ)(f:S→ℝ):Prop:=∀ y, ‖f y‖≤ c*p k x y
abbrev NiceF (F:Scaff)(n:Side)(k:ℕ)(c:ℝ):Prop:= ∀ x:Site n, Paying x (2+k) c (F n x) ∧ ∀ i:Axis,Paying x (2+k+1) c (ds i F n x)
lemma pay_cheap (F:S→ℝ)(h:Paying x k c F)(he:c≤a): Paying x k a F:= fun i=> (h i).trans (mul_le_mul_of_nonneg_right he (live _ _|>.le))
include k in
lemma sturdy {n:Side}(h:a≤c)(A:Scaff)(ht:NiceF A n k a): NiceF A n k c:= fun i=>⟨pay_cheap _ _ (ht i).1 h,fun j=> pay_cheap _ _ ((ht i).2 j) h⟩
variable (hq:1<q.val) (F:Scaff)
include hq
lemma costF (h:F∈ air k): ∃ c:ℝ,c>0 ∧ ∀ᶠ i:ℕ in atTop,∀ x: Site (side q i),Paying x (2+k) c (F (side q i) x):= by
    obtain ⟨c,hc,he⟩:= Print.cost hq (sky.mp h); refine ⟨c+1,by positivity,?_⟩; filter_upwards [he] with i hi x y; specialize hi (lift x) (lift y); unfold fund; have hp:= pay_pos x y; rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hp _)]; apply le_trans _ (le_add_of_nonneg_right zero_le_one); simpa [castG,Print.scale] using! hi
lemma nice (h:F∈air k):∃ c:ℝ,c>0 ∧ ∀ᶠ i:ℕ in atTop,NiceF F (side q i) k c:= by
    choose c hc hC using fun i:Axis=>costF hq (ds i F) (air_ds i h); obtain ⟨r,hr,he⟩:= costF hq F h; let C:=∑ i:Axis,c i; have hp:0≤C:=Finset.sum_nonneg (fun i _=>(hc i).le); refine ⟨r+C,by linarith,?_⟩; filter_upwards [he,eventually_all.mpr hC] with i hi h x; refine ⟨pay_cheap _ _ (hi x) (le_add_of_nonneg_right hp),fun j=>?_⟩; rw [Nat.add_assoc]; exact pay_cheap x _ (h j x) ((single_le_sum (fun i _=> (hc i).le) (mem_univ j)).trans (le_add_of_nonneg_left hr.le))
end YM.PositionX.Chir.Imprint
