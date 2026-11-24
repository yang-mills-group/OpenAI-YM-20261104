import YM.FormalBulk08.Chapel.Bow

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Chapel
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ η A B C : ℝ}{m r:ℕ}{L : Side}{I J : Type}

-- only for coherence
lemma gob {X Y: Type*}(_D : Reach X)(S:Y→X→ℝ)(H:∀ x,Summable fun y=>S y x) (T:Tile Y (r+1))(h:∀ v,‖T v‖≤C)(_hc:0≤C)(w:chain X (r+1)) : Summable (fun v:chain Y (r+1)=> T v * ∏ i,S (v i) (w i)):= by
   apply Summable.of_norm_bounded (g:=fun v=>C*∏ i,‖S (v i) (w i)‖) ?_ ?_
   · apply Summable.mul_left
     have he (i:Fin (r+1)) : (∑' v, ENNReal.ofReal ‖S v (w i)‖) ≠ ⊤:= (H _).norm.tsum_ofReal_ne_top
     refine (ENNReal.summable_toReal (f:=fun v:chain Y (r+1)=>∏ i,ENNReal.ofReal ‖S (v i) (w i)‖) (by rw [eun_tsum (fun i (v:Y)=>ENNReal.ofReal ‖S v (w i)‖)]; exact ENNReal.prod_ne_top fun i _=>he i)).congr ?_
     intro v;simp only [ENNReal.toReal_prod]; exact Finset.prod_congr rfl fun i _=> ENNReal.toReal_ofReal (norm_nonneg _)
   intro v; rw [_root_.norm_mul,norm_prod]; exact mul_le_mul_of_nonneg_right (h _) (Finset.prod_nonneg (fun _ _=>norm_nonneg _))

def snaking (x:Cover) : chain I m×cloud m≃ chain (Biglot I) m where
   toFun a:= snake x a.1 a.2
   invFun v:= (fun i=>(v i).2,fun i=>((v i.1).1-x) i.2)
   left_inv a:= by refine Prod.ext rfl ?_; ext ⟨i,j⟩; simp [snake,rack]
   right_inv v:= by ext1 i; apply Prod.ext; swap;· rfl
                    ext j;simp [snake,rack]
variable [Fintype I][Fintype J]
lemma center_row (S : Cross L I J)(hs:S.strip η A)(hp:0≤η)(hA:0≤A)(u : Biglot J): Summable (fun x=> merit S x u) := by
   have hx:=radix S hs hA u; refine (tsum_enorm_ne_top_iff_summable_norm.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((ENNReal.tsum_le_tsum ?_).trans hx))).of_norm
   intro v;exact le_mul_of_one_le_left zero_le (shine_plus _ hp _)
lemma altar_sum (S: Cross L I J)(x:Biglot I)(T:Tile (Biglot I) (m+1))(u:Biglot J)(v:chain (Biglot J) m)(hs:S.strip η A)(hp:0≤η)(hA:0≤A)(h:Bail (fame I) σ T C)(hx:0≤σ):
   merit S x u*(∑ t,glassTail S x T t v) = ∑' w:chain (Biglot I) m,T (Fin.cons x w)*∏ i, merit S ((Fin.cons x w : chain (Biglot I) (m+1)) i) ((Fin.cons u v : chain (Biglot J) (m+1)) i) := by
   let F:= fun w:chain (Biglot I) (m+1)=> T w*∏ i,merit S (w i) ((Fin.cons u v : chain (Biglot J) (m+1)) i)
   let f:= fun w:chain (Biglot I) m=>F (Fin.cons x w); let g:= snaking (m:=m) (I:=I) x.1; have hh: Summable F:= gob (fame J) (merit S) (center_row S hs hp hA) T (fun v=>h.value hx v 0) h.1 _
   have ht: Summable (f ∘ g):= (g.summable_iff).mpr (hh.comp_injective (f:=F) (i:=(fun v:chain (Biglot I) m=>Fin.cons x v)) (fun x y e=> by simpa [Fin.cons_inj] using e))
   change _=∑' v,f v; rw [← Equiv.tsum_eq g];change _= ∑' v:chain I m × cloud m,(f ∘ g) v;rw [ht.tsum_prod,tsum_fintype, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_; rw [glassTail, ←tsum_mul_left]; apply tsum_congr; intro a; simp only [Function.comp_apply]; unfold f g F rowC; rw [Fin.prod_univ_succ]; simp only [snaking,Equiv.coe_fn_mk, Fin.cons_zero,Fin.cons_succ,candor,crown]; ring
lemma altar (S: Cross L I J)(T:Tile (Biglot I) (m+1))(u:Biglot J)(hs:S.strip η A)(hp:0≤η)(hA:0≤A)(h:Bail (fame I) σ T C)(hx:0≤σ):
    Lava.shed (pearl (merit S) T) u = fun v=>∑' x:Biglot I, merit S x u*(∑ t:chain I m,glassTail S x T t v) := by
   funext v; simp_rw [altar_sum S _ T u v hs hp hA h hx]; unfold Lava.shed pearl; rw [← Equiv.tsum_eq (Fin.consEquiv _)]
   apply Summable.tsum_prod
   have he:=gob (fame J) (merit S) (center_row S hs hp hA) T (fun v=>h.value hx v 0) h.1 (Fin.cons u v)
   exact (Fin.consEquiv _).summable_iff.mpr he

omit [Fintype J] in
lemma travel_W (x : Biglot J)(a: Biglot J)(T : Tile (Biglot J) m)(h:Knoxville (fame _) η x T C)(hx:0≤η): Knoxville (fame _) η a T (Real.exp (η*(fame _).d a x)*C):= by
   refine ⟨mul_nonneg (Real.exp_pos _).le h.1,?_⟩;rw [ENNReal.ofReal_mul (Real.exp_pos _).le];refine le_trans ?_ (mul_le_mul_right h.2 _);rw [←ENNReal.tsum_mul_left];apply ENNReal.tsum_le_tsum;intro v; rw [←mul_assoc]; apply mul_le_mul_left
   let D:= fame J; have he: wide D (Fin.cons a v) ≤ D.d a x + wide D (Fin.cons x v):= by
      let X:= (Fin.cons x v : chain (Biglot J) (m+1)); apply known_wide; intro i j; cases i using Fin.cases <;> cases j using Fin.cases
      · rw [D.self]; exact Nat.zero_le _
      · rename_i j;exact (D.tri a x (v j)).trans (Nat.add_le_add_left (reached D X 0 j.succ) _)
      · rename_i i; rw [D.turn];exact (D.tri a x (v i)).trans (Nat.add_le_add_left (reached D X 0 i.succ) _)
      rename_i i j; exact (reached D X i.succ j.succ).trans (Nat.le_add_left ..)
   exact (shine_le _ hx he).trans_eq (shine_add ..)

lemma all_youth (S : Cross L I J)(T : Tile (Biglot I) (m+1))(hs:S.strip η A)(hp:0≤η)(hA:0≤A)(h:Bail (fame I) σ T C)(hx:0≤σ)(hB:0≤B)(u : Biglot J)(H : ∀ x t, Knoxville (fame _) η (piz L x u.2) (glassTail S x T t) B):
   Knoxville (fame _) η u (Lava.shed (pearl (merit S) T) u) ((L.val:ℝ)^4*(Fintype.card I*A)*((Fintype.card I)^m*B)) := by
   let D:=(Fintype.card I:ℝ)^m * B;have hD:0≤D:=by unfold D; positivity
   have he x: Knoxville (fame _) η (piz L x u.2) (∑ t:chain I m,glassTail S x T t) D:= Knoxville.mono (knox_sum Finset.univ (fun t _=>H x t)) (by simp [D,nsmul_eq_mul,chain])
   rw [show Lava.shed (pearl (merit S) T) u=(fun v=>∑' x:Biglot I,(merit S x u • (∑ t:chain I m,glassTail S x T t)) v) from ?hz]
   swap; · rw [altar S T u hs hp hA h hx];simp_rw [Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
   have hh x:= (travel_W _ u _ (he x) hp).smul (merit S x u)
   apply knox_tsum _ _ _ _ hp hh (by positivity) _ |>.1
   rw [ENNReal.ofReal_mul (show 0≤ (L.val:ℝ)^4*(Fintype.card I*A) from by positivity)]; refine le_trans ?_ (mul_le_mul_left (radix S hs hA u) _);rw [←ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum; intro x; exact le_of_eq (by rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_mul (Real.exp_pos _).le,mul_left_comm,←Real.norm_eq_abs, ofReal_norm]; exact (mul_assoc ..).symm)
end YM.FormalBulk08.Chapel
