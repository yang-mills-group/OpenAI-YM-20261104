import YM.X.Rank.Steady
/-!
There is a neighborhood at identity where the empirical gauge-preserving
condition on the tested polynomials actually forces equality. Tangent proof by
moving samples, no Lie subgroup regularity of the color stabilizer assumed.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank
open Function Set Filter MeasureTheory Matrix Maxwell Wick Maxwell.Free
open Screen Next.Rank.Normal MvPolynomial NormedSpace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius RealInnerProductSpace ContDiff
variable {G : Gauge} {A I : Type*} {P : Mat G}
local instance Rext : NormedAlgebra ℚ (Mat G) := .restrictScalars ℚ ℝ _
private lemma anyFret (V : Type*) [MetricSpace V] : FrechetUrysohnSpace V:= inferInstance
local instance fret : FrechetUrysohnSpace (Mat G):= anyFret (Mat G)
lemma unit_expO (P:Mat G)(he:P.transpose=-P) (t:ℝ) : exp (t • P)∈O G := by 
  change (exp (t • P)).transpose*_=_
  exact Matrix.mem_unitaryGroup_iff'.mp (exp_mem_unitary_of_mem_skewAdjoint (x:=t • P) (show star (t • P) = _ by simp only [star_smul,star_trivial,show star P=-P from he,smul_neg]))
private lemma glideO {p: WickPol G}(h:∀ A, vel p A P=0) (t:ℝ) (A:Sample G) : snap p (exp (t • P)) A=snap p 1 A:= by
  let A' (t:ℝ):=exp (t • P); let f(t:ℝ) := snap p (A' t) A
  have e (A:Sample G): HasDerivAt (fun z=> snap p (A' z) A) 0 0:= by
    rw [← h A]; exact (show HasFDerivAt (fun X:Mat G=> snap p X A) (vel p A) (A' 0) by simpa only [A',zero_smul, NormedSpace.exp_zero] using! ((regularity A p).differentiable (by simp) (1:Mat G)).hasFDerivAt).comp_hasDerivAt _ (show HasDerivAt A' P 0 from (by simpa [A'] using! hasDerivAt_exp_smul_const P (0:ℝ)))
  have he (u:ℝ): HasDerivAt f 0 u := by
    have he (t:ℝ): f t=snap p (A' (t-u)) (coatV (A' u) A):= by
       have h: exp ((t-u) • P)*exp (u • P)=exp (t • P):=(NormedSpace.exp_add_of_commute (((Commute.refl P).smul_left (t-u)).smul_right u)).symm.trans (by rw [← add_smul, sub_add_cancel]; rfl)
       unfold f snap; rw [coat_mul, show A' (t-u)*A' u=A' t from h]
    have ht: HasDerivAt (fun t:ℝ=>t-u) 1 u:= (hasDerivAt_id' ..).sub_const u
    rw [funext he]; simpa using! ((e (coatV (A' u) A)).scomp_of_eq u ht (sub_self u).symm)
  have H:=is_const_of_deriv_eq_zero (fun t=> (he t).differentiableAt) (fun t=> (he t).deriv) t 0
  simpa only [f,A',zero_smul,NormedSpace.exp_zero] using H
variable (q:I→ WickPol G) (h:G.Simple) (hp:∀ i,Painted (q i))
lemma same_comp {a b c:Mat G}(h:Same q a b): Same q (a*c) (b*c):= fun i A=> by simp only [snap,← coat_mul]; exact h i _
lemma st_union (X:Mat G): IsClosed {Y| Same q Y X} := by rw [show {Y: Mat G| Same q Y X}=⋂ i:I,⋂ A:Sample G,{Y| snap (q i) Y A=snap (q i) X A} from by ext Y; simp [Same] ]; exact isClosed_iInter fun i=>isClosed_iInter fun A=> isClosed_eq (regularity A (q i)).continuous continuous_const
lemma aim {X : Mat G}(hx:X∈O G) : ∃ Y:Mat G,Y∈O G ∧ Same q Y X ∧ ∀ Z:Mat G,Z∈O G → Same q Z X → ‖Y-1‖≤ ‖Z-1‖ := by
   let s:=O G∩ {Y| Same q Y X}; obtain ⟨x,hx,h⟩ := (IsCompact.inter_right (show IsCompact (O G) from gram_closed) (st_union q X)).exists_isMinOn (f:=fun x=> ‖x-1‖) (show s.Nonempty from ⟨X,hx,fun _ _=>rfl⟩) ((by fun_prop : Continuous (fun x:Mat G=> ‖x-1‖)).continuousOn); exact ⟨x,hx.1,hx.2,fun Z he ht=>h ⟨he,ht⟩⟩

include hp h
variable {v : ℕ→Mat G}
lemma relapse (hS:Tendsto v atTop (𝓝 1))(hx:∀ i:ℕ,v i∈ O G ∧ Keeps q (v i)): ∃ i,Same q (v i) 1:= by
   choose z hu hv hz using fun i=>aim q (hx i|>.1); by_contra! H
   let u(i:ℕ):= ‖z i-1‖; have hK : ∀ i,z i≠1 := fun i hi=> H i (fun j A=> by rw [← hv i j A, hi]); have hk i : 0<u i := norm_pos_iff.mpr (sub_ne_zero.mpr (hK i)); have hU:= squeeze_zero' (Eventually.of_forall (fun i=>(hk i).le)) (Eventually.of_forall (fun i=> hz i _ (hx i|>.1) (fun _ _=>rfl))) (show Tendsto (fun i=> ‖v i-1‖) atTop (𝓝 0) by simpa using! (hS.sub_const (1:Mat G)).norm)
   have hB := tendsto_iff_norm_sub_tendsto_zero.mpr (show Tendsto (fun i=>‖z i-1‖) atTop (𝓝 0) from hU)
   let f:= Drop (1:Mat G) z; have hA i : ‖f i‖ =1 := by change ‖(u i)⁻¹ • (z i-1)‖=1; rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hk i).le),inv_mul_cancel₀ (hk i).ne'] -- edit
   letI : ProperSpace (Mat G):= FiniteDimensional.proper ℝ _
   obtain ⟨P,hP,g,hg,hY⟩:= (isCompact_sphere (0:Mat G) 1).tendsto_subseq (fun i=> show f i∈ Metric.sphere (0:Mat G) 1 from (by rw [Metric.mem_sphere,dist_zero_right,hA])); let l:= u ∘ g
   have hT: Tendsto (Drop 1 (z ∘ g)) atTop (𝓝 P) := hY; have hJ:= hg.tendsto_atTop; have hZ:=hB.comp hJ; have hL:= hU.comp hJ
   have hW:= tiltO hZ hT (Eventually.of_forall (fun i=> hu (g i))); have hd i A : vel (q i) A P=0 := still q h hp hZ hT (Eventually.of_forall (p:=fun i:ℕ=> z (g i)∈ O G∧ Keeps q (z (g i))) (fun i=> ⟨hu _, fun j k V=> by rw [hv (g i) j (coatV (Sk k) V),hv (g i)]; exact (hx (g i)).2 j k V⟩)) i A
   let U(t:ℝ):Mat G:=exp (t • (-P))
   let F(i:ℕ):=U (l i)*z (g i)
   have hl (i): 0<l i:=hk _
   have hh : HasDerivAt U (-P) 0:= by simpa [U] using! hasDerivAt_exp_smul_const (-P) (0:ℝ)
   have he: Tendsto l atTop (𝓝[≠] (0:ℝ)) := tendsto_nhdsWithin_iff.mpr ⟨hL, Eventually.of_forall (fun i=> (hl i).ne')⟩
   have ht: Tendsto (fun i=> (l i)⁻¹ • (U (l i)-1)) atTop (𝓝 (-P)) := by simpa [U,slope_def_module,Function.comp_def] using! hh.tendsto_slope.comp he
   have hb : Tendsto (fun i=>(l i)⁻¹ • (F i-1)) atTop (𝓝 0):= by
     have hh:= (ht.mul hZ).add hY; rw [mul_one,neg_add_cancel] at hh
     apply hh.congr; intro i; unfold F; rw [show U (l i) * z (g i)-1=(U (l i)-1)*z (g i)+(z (g i)-1) by rw [sub_mul, one_mul]; abel, smul_add,smul_mul_assoc];rfl
   apply not_le_of_gt zero_lt_one (le_of_tendsto_of_tendsto (tendsto_const_nhds (x:=(1:ℝ))) (show Tendsto (fun i=> (l i)⁻¹ * ‖F i-1‖) atTop (𝓝 0) by simpa only [norm_zero, norm_smul, fun i:ℕ=> Real.norm_of_nonneg (inv_nonneg.mpr (hl i).le)] using! hb.norm) ?_)
   refine Eventually.of_forall fun i=>le_trans (b:=(l i)⁻¹ * ‖z (g i)-1‖) (inv_mul_cancel₀ (hl i|>.ne')|>.ge) (mul_le_mul_of_nonneg_left (hz (g i) _ ?_ ?_) (inv_nonneg.mpr (hl i).le))
   · apply folds (unit_expO (-P) (by rw [transpose_neg,hW]) _) (hu _)
   intro j A; rw [← hv (g i)]; unfold snap F; rw [← coat_mul]; unfold U; rw [smul_neg, ← neg_smul (l i)]; exact (glideO (hd j) (-(l i)) _).trans (by rw [snap,coat_one])

lemma steady : ∀ᶠ x in 𝓝 (1:Mat G), x∈ O G → Keeps q x→ Same q x 1:= by
  by_contra ht; let T:={x:Mat G|x∈O G ∧ Keeps q x ∧ ¬ Same q x 1}; have he:∃ᶠ x in 𝓝 (1:Mat G),x∈T := (not_eventually.mp ht).mono fun x hx=> by change x∈ O G ∧ _ ∧ _; simpa using hx
  obtain ⟨x,hx,hK⟩:= mem_closure_iff_seq_limit.mp (mem_closure_iff_frequently.mpr he); obtain ⟨i,hi⟩:= relapse q h hp hK (fun i=> ⟨(hx i).1,(hx i).2.1⟩); exact (hx i).2.2 hi
end YM.PositionX.Rank
