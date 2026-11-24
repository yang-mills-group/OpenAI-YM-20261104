import YM.WilsonCoeffUV.Reclosure.Revenue
/-!
# Funding the polygon array in actual unmasked path representation
Size costs independent of finite side. Period-cylinder transfers used below
for Ward and completion identities. No masks or exponential activities here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Stationary AnalyticNext.QuarticMatch.Estimate Near
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{N M e m i k r t:ℕ}{s a:ℝ}
variable {A:ℕ→Atom G t}

lemma trestle (h:0<s)(e: SumBudget (fun i=>(A i).budget s) a) (p:Site c) (x: Fin k→ Woods G c): HasSum (fun i=>rye (meter (A i) p) k x) (rye (atend A p ∘ arm G c 1) k x):=by
   let L: Lawn (Woods G c)→L[ℝ] fieldDir G c 1:= (arm G c 1).toContinuousLinearMap
   have hm:= e.2.1.mul_left (((2:ℝ)^k*gratuity G (down s k) k)^t)
   have H :HasSum (fun i=>iteratedFDeriv ℝ k (Cargo.effect (A i) p) 0) (iteratedFDeriv ℝ k (atend A p) 0):= honorable (fun i=>Cargo.effective ..) hm (m:=k) (Metric.ball (0:fieldDir G c 1) 1) isOpen_ball (convex_ball _ _).isPreconnected (fun i x hx j hj=> neighbors x (le_of_lt (by simpa using hx)) h _ _ hj _) (by simp) k le_rfl
   let P i:Lawn (Woods G c):= Blue.pebble (x i)
   let u:=(k.factorial:ℝ)⁻¹
   have hx : rye (atend A p ∘ L) k x=u • iteratedFDeriv ℝ k (atend A p) 0 (L ∘ P):=by rw [rye,wired L (Village.atend_rate A h e p (L 0)).analyticAt, map_zero]; rfl
   have he i: rye (meter (A i) p) k x=u • iteratedFDeriv ℝ k (Cargo.effect (A i) p) 0 (L ∘ P):=by rw [rye,show meter (A i) p=(Cargo.effect (A i) p) ∘ L from rfl,wired L ((Cargo.effective (A i) p).contDiffAt.analyticAt (x:=L 0)),map_zero]; rfl
   change HasSum _ (rye (atend A p ∘ L) _ x); simp_rw [hx,he]; exact ((ContinuousMultilinearMap.apply ℝ _ ℝ (L ∘ P)).hasSum H).const_smul _
lemma crownS (h:0<s)(e:SumBudget (fun i=>(A i).budget s) a) (x:Fin k→Woods G c): HasSum (fun i=>archInk (A i) c k x) (rye (seriesScore c A) k x):=by
    have hx (i:ℕ): archInk (A i) c k x= ∑ j:Site c,rye (meter (A i) j) k x:= by rw [archInk,Finset.sum_apply]
    have ht: seriesScore c A= ∑ j:Site c, (atend A j ∘ arm G c 1):=by funext x; rw [Finset.sum_apply]; rfl
    have hh (j:Site c): Green (atend A j ∘ arm G c 1) := (Village.atend_rate A h e _ _).comp _ (arm G c 1).contDiff.contDiffAt
    have hv:=jet_sum (U:=Woods G c) Finset.univ _ (fun j _=>hh j)
    have hy:= rye_sym (score_analytic c A h e).contDiffAt k
    have he : rye (seriesScore c A) k= ∑ j:Site c, rye (atend A j ∘ arm G c 1) k := by
       apply unique_kernel hy (Blue.Smooth.sum (fun i _=>rye_sym (hh i) k)); rw [← jet_apply,ht,hv,map_sum,map_sum]; simp_rw [jet_apply]
    simp_rw [he,hx,Finset.sum_apply]; exact hasSum_sum fun k _=> trestle h e k x
lemma traveling_stone (n:Side)(k:ℕ)(Q:Atom G t): stroll (archInk Q n k):= by
   have he : archInk Q n k= wear (iris (Option.map (foldUnder n) ∘ lead Q) (shine (rye (line Q) k)) k):=by rw [iris_apply]; unfold archInk; simp_rw [frames]; rfl
   rw [he]; apply north_stroll; intro b x y; unfold iris Blue.fade; apply Finset.sum_congr rfl; intro i _; congr 1; apply Finset.prod_congr rfl; intro j _; rw [plank, plank,Matrix.of_apply,Matrix.of_apply]; congr 1; simp only [Function.comp_apply]; rw [show ((jog ((jog b (y 0)).1)).symm (jog b (x j)))=(jog (y 0).1).symm (x j) from Prod.ext (by change -(b+(y 0).1)+(b+(x j).1) = -(y 0).1+(x j).1; abel) rfl]
lemma led (h:0<s)(p: SumBudget (fun i=>(A i).budget s) a)(n:Side)(k:ℕ): stroll (rye (seriesScore n A) k):=by
   intro b x; rw [←(crownS h p (jog b ∘ x)).tsum_eq,←(crownS h p x).tsum_eq]; apply tsum_congr; intro i
   exact traveling_stone _ _ _ _ _

def spreadW (A:ℕ→Atom G t) (k :ℕ) : Ten ℝ (YForest G) k:= fun x=> ∑' i, coverInk (A i) k x
lemma summable_pet {V:Type*}[NormedAddCommGroup V][CompleteSpace V]{P:ℕ→V}{t:ℕ→ℝ} (h:Summable t)(e:∀ i,‖P i‖ ≤ t i): Summable P:=Summable.of_norm_bounded h e
lemma sponsored (h:0<s)(hw: SumBudget (fun i=>(A i).budget s) a)(k): Yields (fun n=> rye (seriesScore n A) (k+1)) (spreadW A (k+1)):=by
   let v:=steep s; have hp:0<v:=div_pos h (by norm_num)
   let T:= garden G s t (k+1); have ht:0≤ T:=garden_nn G h t (k+1)
   let R i:=(A i).budget s*T
   have H: SumBudget R (a*T):= ⟨fun i=>mul_nonneg (hw.1 i) ht,hw.2.1.mul_right T, by unfold R; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hw.2.2 ht⟩
   have Hᵣ n i: Amber (tor n) v (R i) (archInk (A i) n (k+1)) := artical (A i) h n k
   refine ⟨fun x=> ?_, Eventually.of_forall (fun i=>led h hw i _),v,a*T,hp, Eventually.of_forall fun n=>?_⟩
   · have ht i: Tendsto (fun n=> archInk (A i) n (k+1) (foldUnder n ∘ x)) atTop (𝓝 (coverInk (A i) (k+1) x)):=by
        have he:=(orchid (A i) (k+1)).point x; simpa only [dilute, Nat.succ_ne_zero,↓reduceIte] using he
     simp only [dilute,Nat.succ_ne_zero,↓reduceIte]; have HZ n:= (crownS h hw (foldUnder n ∘ x)).tsum_eq; simp_rw [← HZ]
     apply tendsto_tsum_of_dominated_convergence H.2.1 ht (Eventually.of_forall (fun n i=>?_))
     exact ((Hᵣ n i).2 _).trans (mul_le_of_le_one_right (H.1 i) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))))
   refine ⟨cap_nn H,fun x=>?_⟩
   rw [dilute,if_neg (Nat.succ_ne_zero _),←(crownS h hw x).tsum_eq]
   apply (norm_tsum_le_tsum_norm ?hc).trans
   case hc=>exact summable_norm_iff.mpr (crownS h hw x).summable
   let u:=Real.exp (-v*soar (tor n) x)
   apply (Summable.tsum_le_tsum (fun i=> (Hᵣ n i).2 x) (summable_norm_iff.mpr (crownS h hw x).summable) (H.2.1.mul_right u)).trans; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right H.2.2 (by positivity)
lemma coronation (h:0<s)(hw: SumBudget (fun i=>(A i).budget s) a) (k:ℕ): Amber terrain (steep s) (a*garden G s t (k+1)) (spreadW A (k+1)):=by
    let Z:= garden G s t (k+1); let F i:=(A i).budget s * Z; have he:0≤Z:= garden_nn G h _ _
    refine ⟨mul_nonneg (cap_nn hw) he,fun x=>?_⟩
    let u:= Real.exp (-(steep s)*soar terrain x); have hu:0≤u:=by unfold u; positivity
    have hh := (hw.2.1.mul_right Z).mul_right u
    have H i: ‖coverInk (A i) (k+1) x‖≤ F i*u:= (rocksA (A i) h k).2 _
    have hx:=hh.of_nonneg_of_le (fun i=>norm_nonneg _) H
    exact (norm_tsum_le_tsum_norm hx).trans ((hx.tsum_le_tsum H hh).trans (by unfold F; rw [tsum_mul_right, tsum_mul_right]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw.2.2 he) hu))
end YM.WilsonCoeffUV.Bank.Mosaic
