import YM.WilsonCoeffUV.Marked.Paths.Vector
/-!
# At a fixed finite list, supreme analytic derivative budgets of formal orders.
Connect any actual Slot-word representation with priced innovation to same language.
 -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Rolls
open Gauge Power PowerSeries Matrix Filter Lattice Laurent Exterior Precision Wilson RG Tree Bloch Stationary
open Function Blue Bank Fountain Soil Source Source.Drops Labels Cosmos Planned.PrimaryIntegral295 Place Carrier Bank.Carp Bank.Mosaic Bank.Mosaic.Near
open scoped Topology ContDiff BigOperators Classical
open Work.F03
variable {G:Gauge}{n:Side}{k h r t i j e:ℕ}{s A B:ℝ}
variable {V W I α β:Type}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]

lemma scalar_clock [Fintype α][Fintype β] {P:I→Pal ℝ α}{Q:Pal ℝ α}(he:∀ i,shellK k (P i))(p:shellK k Q)(h:∀ i j x,HasSum (fun n=>P n i j x) (Q i j x))(v:α→Blue.Ink β)(M:ℕ)(m:β→₀ℕ): HasSum (fun n=> MvPolynomial.coeff m (coeff M (train v (flash (P n))))) (MvPolynomial.coeff m (coeff M (train v (flash Q)))):=by
    let K:POL α→ₐ[ℝ]Blue.Ink β :=(MvPolynomial.aeval v); let Φ (j:ℕ)(B:POL α) :ℝ := MvPolynomial.coeff m (coeff M ((K B)*PowerSeries.X^j))
    let L (j):POL α→ₗ[ℝ]ℝ := {
        toFun:=Φ j
        map_add' x y:=by simp [Φ,map_add,add_mul]
        map_smul' c x:=by simp [Φ,map_smul] }
    let A j (r:ℕ)(x:Fin r→α):ℝ:= L j (∏ i,MvPolynomial.X (x i)); let B j:= Finset.range (k+j+1); let S:= Finset.range (M+1)
    let U (T:Pal ℝ α):=∑ j∈S,∑ r∈B j,∑ x:Fin r→α,A j r x • T j r x
    have hV (T:Pal ℝ α)(h:shellK k T):MvPolynomial.coeff m (coeff M (train v (flash T)))= U T:=by
       rw [train,edit_coeff _ _ _ (Nat.lt_succ_self M),map_sum,MvPolynomial.coeff_sum]; apply Finset.sum_congr rfl; intro i _; rw [Blue.flash,coeff_mk]; change L i (totalR (T i))=_
       have hs: still (T i) (k+i+1):= fun j hj=> h i j hj
       rw [visible hs,map_sum]; refine Finset.sum_congr rfl (fun j _=>?_); rw [paint,palm_form,map_sum]; exact Finset.sum_congr rfl (fun x _=>by rw [map_smul,smul_eq_mul,smul_eq_mul]; exact mul_comm ..)
    rw [hV Q p]; simp_rw [show ∀ i,MvPolynomial.coeff m (coeff M (train v (flash (P i))))=_ from fun i=> hV (P i) (he i)]; exact hasSum_sum (s:=S) (fun i _=> hasSum_sum (s:=B i) (fun j _=>hasSum_sum (s:=Finset.univ (α:=Fin j→α)) (fun x _=> (h i j x).const_smul _)))

omit [CompleteSpace V] in
lemma honesty {P:I→Era G V}{Q:Era G V}(hp:∀ i, Auth k (P i))(h:∀ n i k x,HasSum (fun c=>(P c).1 n i k x) (Q.1 n i k x)) (s:∀ i k,Bends 0 (fun n=>Q.1 n i k) (Q.2 i k)): Auth k Q:=by
    have ht n: shellK k (Q.1 n):= by
      intro i j p; ext1 x; apply (h n i j x).unique; simp_rw [show ∀ c,(P c).1 n i j =0 from fun c=>(hp c).span n i j p]; exact hasSum_zero
    refine ⟨s,ht,fun n i j q x=>?_,fun n=>certify (fun L:V→L[ℝ]ℝ=>L.toLinearMap) (fun _ _ h=>probe h) _ (ht n) (fun L=>?_)⟩
    · apply (h n i j (x ∘ q)).unique; simp_rw [show ∀ c,(P c).1 n i j (x ∘ q) = (P c).1 n i j x from fun c=> (hp c).pale n i j q x]; exact h _ _ _ _
    intro U I a M N x
    let X (V':Era G V)(z:V→L[ℝ]ℝ) (Z:Woods G n→Blue.Ink U)(j:ℕ)(m:U→₀ℕ):= MvPolynomial.coeff m (coeff j (train Z (flash (ply z.toLinearMap (V'.1 n)))))
    have hz c j m: X (P c) L (spool M) j m=X (P c) L (spool N) j m:= by unfold X; rw [(hp c).token n L.toLinearMap x]
    have hg Z j m: HasSum (fun c=> X (P c) L Z j m) (X Q L Z j m):= scalar_clock (P:=fun c=>ply L.toLinearMap ((P c).1 n)) (Q:= ply L.toLinearMap (Q.1 n)) (fun c=>ply_shell _ ((hp c).span n)) (ply_shell _ (ht n)) (fun i j t=> L.hasSum (h n i j t)) ..
    ext1 j; apply MvPolynomial.ext; intro m; apply HasSum.unique (hg (spool M) j m); simp_rw [hz]; exact hg _ _ _

variable {X: I→Comet G V r}

-- budgets full

def bolus (X: I→ Comet G V r)(e:ℕ) : Era G V:=let T:=fun i j x=> ∑' v,(volumeR (X v) e).2 i j x;                                                        (fun n i j=> plume (T i j) n, T)
lemma elevated (p:0<s)(b:SumBudget (fun i=>integerP (X i) s) A)(e:ℕ)(n:Side)(i j x): HasSum (fun v=> (volumeR (X v) e).1 n i j x) ((bolus X e).1 n i j x):=by
    let u := steep s; let B:= flour G u r j; have h:0<u:= div_pos p (by norm_num); have hp: SumBudget (fun i=>integerP (X i) s* B) (A*B):=by
       have hx:0≤B:=flour_nn ..; exact ⟨fun i=> mul_nonneg (b.1 i) hx,b.2.1.mul_right _, by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right b.2.2 hx⟩
    simp_rw [aug_plane]; exact plume_budget (fun v=>(volumeR (X v) e).2 i j) _ (fun a=> volume_price _ p _ _ _) h hp n x
omit [CompleteSpace V] in
lemma sky_high (p:0<s)(b:SumBudget (fun i=> integerP (X i) s) A)(e:ℕ)(i j): Cork Bank.terrain 0 (steep s) (A*flour G (steep s) r j) ((bolus X e).2 i j):=by
    let C:= flour G (steep s) r j
    refine sigma_cap _ (fun i=>integerP (X i) s*C) (fun v=> volume_price (X v) p e i j) (div_pos p (by norm_num)) ?_
    have hx:0≤C:=flour_nn ..; exact ⟨fun i=> mul_nonneg (b.1 i) hx,b.2.1.mul_right _, by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right b.2.2 hx⟩
lemma stars (p:0<s)(b: SumBudget (fun i=>integerP (X i) s) A)(q:r≤k+e)(h:∀ i,shadeStar (X i)): Auth k (bolus X e):=honesty (P:=fun i=>volumeR (X i) e) (fun i=> aug_auth (X i) (h i) q) (elevated p b e) (fun i j=> caisson (sky_high p b e i j) (div_pos p (by norm_num)))
omit [CompleteSpace V] in
lemma prior_m (H:I→Comet G V r)(p:i< e): (bolus H e).2 i=0:=by funext j x; unfold bolus volumeR moved; simp only [if_neg p.not_ge]; exact tsum_zero
omit [CompleteSpace V] in
lemma latter_m (H:I→Comet G V r)(p:r≠k): (bolus H e).2 e k=0:=by
   funext x; have hx i : moved r e (august (H i)) e k x=0:=by rw [moved,if_pos le_rfl,Nat.sub_self,add_zero,shine_dark p]; rfl
   change (∑' i,moved r e (august (H i)) e k x)=0; rw [tsum_congr hx]; simp
end YM.WilsonCoeffUV.Mer.Rolls
