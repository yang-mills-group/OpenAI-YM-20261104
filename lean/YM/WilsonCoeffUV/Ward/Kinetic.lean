import YM.WilsonCoeffUV.Ward.AffineMoments
/-!
# Direction independence and affine-null signal
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power
open scoped ContDiff Topology BigOperators
variable {G:Gauge} {K H:Ten ℝ (YForest G) 2}{t s A B:ℝ}
-- sign vanishing according parity list multiplicities
lemma oddPair (h:Spin K)(p:Amber terrain t A K)(hp:0<t)(w:∀ x c,windsL x c K=0)(u v:G.ColorIndex)(a b k l c:Axis)(e:tSign (.mirror c) b*tSign (.mirror c) a*tSign (.mirror c) k*tSign (.mirror c) l= -1): tailor K (coord a,u) b v (chalk k*chalk l)=0:=by
   have he:= spin_squares h p hp w (.mirror c) u v a b k l
   rw [e] at he
   simp only [Signed.mirror,Equiv.refl_apply] at he; linarith

def azur (K:Ten ℝ (YForest G) 2)(u:G.ColorIndex) := -tailor K (coord 1,u) 1 u (chalk 0*chalk 0)

lemma same_azur (h:Spin K)(p:Amber terrain t A K)(hp:0<t)(w:∀ x c,windsL x c K=0)(g:Medium K)(u v:G.ColorIndex)(a j:Axis)(hg:a≠j):
    -tailor K (coord a,v) a v (chalk j*chalk j)=azur K u:=by
    obtain ⟨s,hs,ht⟩:= fuel_twin (a:=a) (i:=j) (b:=1) (j:=0) hg one_ne_zero
    let H:Signed:= ⟨s,fun _=>false⟩
    rw [liner g a a v v u, if_pos rfl]
    have he:= spin_squares h p hp w H u u a a j j
    unfold azur; simp only [H,tSign,Bool.false_eq_true,↓reduceIte,one_mul,hs,ht] at he; rw [he]
-- use this as chosen order k base read. no factor 1/2 since ordinary V.
open Classical in
def readSun (K:Ten ℝ (YForest G) 2) := if h:Nonempty G.ColorIndex then azur K h.some else 0
lemma read_azur (K:Ten ℝ (YForest G) 2)(s:Nonempty G.ColorIndex) : readSun K=azur K s.some:= dif_pos s
lemma azur_le (h:Amber terrain t A K)(hp:0<t)(c:G.ColorIndex): |azur K c|≤ A*(ceilPoly 2 (t/2)*sheetPay (t/2)):=by
  have hz i : |(chalk 0*chalk 0) i| ≤ (1:ℝ)*(1+size i:ℝ)^2:=by simp only [Pi.mul_apply, ← sq, abs_pow,one_mul]; exact pow_le_pow_left₀ (abs_nonneg _) ((chalk_fee 0 i).trans (by linarith)) _
  have he := sweat hp (petals_price h (coord 1,c) 1 c) _ hz h.1 zero_le_one
  unfold azur tailor; rw [abs_neg]; exact (norm_tsum_le_tsum_norm he.2.1).trans (he.2.2.trans_eq (by rw [mul_one,mul_assoc]))
lemma sun_cost (h:Amber terrain t A K)(hp:0<t): |readSun K|≤ A*(ceilPoly 2 (t/2)*sheetPay (t/2)):=by unfold readSun; split; exact azur_le h hp _; rw [abs_zero]; exact mul_nonneg h.1 (mul_nonneg (ceilPoly_pos ..).le (sheetPay_pos _ (by positivity)).le)
lemma sun_zero (G:Gauge) : readSun (0: Ten ℝ (YForest G) 2)=0:=by
  unfold readSun; split
  · simp [azur,tailor,petals]
  rfl
lemma sun_add (h:Amber terrain t A K)(g:Amber terrain s B H)(hp:0<t)(he:0<s) : readSun (K+H)=readSun K+readSun H:=by
   unfold readSun; split <;> rename_i hv
   · unfold azur tailor; simp_rw [show ∀ i j v x, petals (K+H) i j v x= petals K i j v x+petals H i j v x from fun i j v x=>rfl, mul_add]
     rw [Summable.tsum_add (tailor_sum h hp _ _ _ _ ((broad.chalk 0).mul (broad.chalk 0))) (tailor_sum g he _ _ _ _ ((broad.chalk 0).mul (broad.chalk 0)))]; abel
   simp
lemma sun_μ (c:ℝ) : readSun (c•K)=c*readSun K:=by
   unfold readSun; split; swap; · simp
   unfold azur tailor; rw [mul_neg,← tsum_mul_left]; congr 1; apply tsum_congr; intro x; unfold petals; simp_rw [Pi.smul_apply, smul_eq_mul]; ring
lemma sun_sub (h:Amber terrain t A K)(g:Amber terrain s B H)(hp:0<t)(he:0<s) : readSun (K-H)=readSun K-readSun H:=by
   rw [sub_eq_add_neg, sun_add h g.neg hp he]; simpa only [neg_one_smul,neg_mul,one_mul,sub_eq_add_neg] using congr_arg (readSun K+·) (sun_μ (K:=H) (-1))

def Aware (K:Ten ℝ (YForest G) 2): Prop:= ∀ i v c, tailor K i v c 1=0 ∧ (∀ a,tailor K i v c (chalk a)=0) ∧ ∀ a b, tailor K i v c (chalk a*chalk b)=0

lemma squab (h:Spin K)(p:Amber terrain t A K)(hp:0<t)(w:∀ x c,windsL x c K=0)(g:Medium K)(e:readSun K=0)(u:G.ColorIndex)(a k:Axis): tailor K (coord a,u) a u (chalk k*chalk k)=0:= by
  by_cases hh:a=k
  · subst k; exact axle p hp h w u a
  have hs:Nonempty G.ColorIndex:=⟨u⟩
  rw [read_azur K hs, ← same_azur h p hp w g hs.some u a k hh] at e; exact neg_eq_zero.mp e

lemma zerosaw (h:Spin K)(p:Amber terrain t A K)(hp:0<t)(w:∀ x c,windsL x c K=0)(g:Medium K)(e:readSun K=0)(u:G.ColorIndex)(a b k l:Axis): tailor K (coord a,u) b u (chalk k*chalk l)=0:=by
   have he (v:Axis): tSign (.mirror v) b*tSign (.mirror v) a*tSign (.mirror v) k*tSign (.mirror v) l=-1→tailor K (coord a,u) b u (chalk k*chalk l)=0:= oddPair h p hp w u u a b k l v
   by_cases hh:a=b
   · subst b; by_cases hz:k=l
     · subst l; exact squab h p hp w g e u a k
     apply he k; by_cases ha:k=a <;> simp_all [tSign,Signed.mirror]
   by_cases ht:k=l
   · subst l; apply he a; by_cases ha:a=k<;>simp_all [tSign,Signed.mirror]
   have hw : tailor K (coord a,u) b u (chalk a*chalk b) = 0:= by
     have he:=cornerM p hp h w u (coord a,u) a b hh
     rw [squab h p hp w g e u a b] at he; linarith
   by_cases H:a=k
   · subst k; by_cases hg:b=l
     · subst l; exact hw
     apply he b; simp [*,tSign,Signed.mirror,Ne.symm]
   by_cases hm:a=l
   · subst l; by_cases hg:b=k
     · subst k; rw [mul_comm]; exact hw
     apply he b; simp [*,tSign,Signed.mirror,Ne.symm]
   apply he a; simp [*,tSign,Signed.mirror]

theorem aware_of_reset (h:Spin K)(p:Amber terrain t A K)(hp:0<t)(w:∀ x c,windsL x c K=0)(g:Medium K)(e:readSun K=0): Aware K := by
    intro i v c; refine ⟨kail p hp w i c v, wick_white h p hp w _ _ _,?_⟩
    intro a b; obtain ⟨i,j⟩:=i; obtain ⟨k,rfl⟩:= axisEquiv.surjective i; rw [coord_map, liner g, zerosaw h p hp w g e c]; simp
end YM.WilsonCoeffUV.Bank
