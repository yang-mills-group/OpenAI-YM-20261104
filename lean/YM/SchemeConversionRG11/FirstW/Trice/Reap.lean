import YM.SchemeConversionRG11.FirstW.Trice.Legend
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck
open scoped ContDiff BigOperators Classical Topology
variable {n:Side}{G:Gauge}{T: Itinerary}{x o:StepPath T}{v w:E4}
def chalk (d:Axis)(g:Axis→ℝ)(a:G.Color) : Axis→ Axis → G.Color:= fun i k=> if k=d then g i • a else 0
lemma chalkS (d:Axis)(g:Axis→ℝ)(a:G.Color)(h:Bool)(t:Fin 3): fanReading h t (Bare.radialMap (door (fun i j=>chalk d g a i j-chalk d g a j i)))= (∑ i:Axis, fan h t i d*g i) • a := by
 let X:=chalk d g a
 rw [vector_at _ (fun i j=>by rw [neg_sub]) h t]
 have H(i j:Axis): fan h t i j • (X i j-X j i)= fan h t i j • X i j+fan h t j i • X j i:=by rw [fan_flip _ t j]; simp only [neg_smul,smul_sub]; abel
 have e(i:Axis) : ∑ j:Axis, fan h t i j • X i j= (fan h t i d*g i) • a:= by rw [Finset.sum_eq_single_of_mem d (Finset.mem_univ _)]; simp [X,chalk,smul_smul]; intro b _ hb; simp [X,chalk,hb]
 change (2:ℝ)⁻¹ •(∑ i:Axis,∑ j:Axis,fan h t i j • (X i j-X j i))=_; simp only [H,Finset.sum_add_distrib]; rw [Finset.sum_comm (f:=fun i j=> fan h t j i • X j i)]; simp_rw [e,← Finset.sum_smul,←two_smul ℝ,inv_smul_smul₀ (show (2:ℝ)≠0 by norm_num)]
lemma inkL {f:ℕ→G.Color}{p:G.Color}(h:∀ v:G.ColorIndex,Tendsto (fun i=>inner ℝ (unitColor G v) (f i)) atTop (𝓝 (inner ℝ (unitColor G v) p))): Tendsto f atTop (𝓝 p):= by
 have ht:= tendsto_finsetSum Finset.univ (fun i _=> (h i).smul_const (unitColor G i)); rw [← inkSum p] at ht; exact ht.congr fun i=> (inkSum _).symm
-- ghost scaled field, test calc root and axes derivative. no assumption all stencils commute away
variable (T) (a:G.Color)(i:Axis)
def ghostM (T:Itinerary) (a:G.Color)(i:Axis)(k:ℕ)(x:Site (T.period k)): FullT G (T.period k):= (T.gap k^2)⁻¹ • Orb.ghostLink (x,i) a
lemma ghost_value (k:ℕ)(x y:Site (T.period k))(t:Axis): ghostM T a i k x (y,t)= capG T k (y-x) • (if t=i then a else 0):=by simp only [ghostM,Orb.ghostLink,capG,Pi.smul_apply]; by_cases h:t=i <;> simp [h,smul_smul,linGreen]
lemma arbitrary_t (a:G.Color)(Y:FullT G n)(x:Site n)(t:ℝ)(b:Badge G)(h:Bool)(hy:Y=(t^2)⁻¹ • Orb.ghostLink (x,i) a) : inner ℝ a (t⁻¹ • Stele b h 0 t (x,i))= lineReader h b.1 b.2 (consoleS n t⁻¹ Y):= by rw [stele_eq,Pi.smul_apply,real_inner_smul_right,real_inner_smul_right,branch_elem]; simp only [consoleS,LinearMap.smul_apply,hy,map_smul,LinearMap.comp_apply, smul_eq_mul]; rw [mul_left_comm]
lemma la_ghost (k:ℕ)(x:Site (T.period k))(b:Badge G)(h:Bool): inner ℝ a (Laurel b h T 0 k (x,i))= lineReader h b.1 b.2 (consoleS (T.period k) (T.gap k)⁻¹ (ghostM T a i k x)):= by
   unfold Laurel; simp only [Pi.smul_apply,Pi.zero_apply]; exact arbitrary_t i a _ _ _ _ _ rfl
variable {T}
def conduit (T:Itinerary) (A:Sight T G)(k:ℕ): Labels.Taylor G 0:= consoleS (T.period k) (T.gap k)⁻¹ (A k)
lemma handover (f:Axis→Axis→G.Color)(A:Sight T G)(h:∀ i j:Axis,∀ x:Cover,Tendsto (fun k=> ray i (stalkH T A j) k (wrap (T.period k) x)) atTop (𝓝 (f i j)))(b: Badge G)(u:Bool)(r:ℕ→ℝ)(e:∀ k,r k=lineReader u b.1 b.2 (conduit T A k)) : Tendsto r atTop (𝓝 (lineReader u b.1 b.2 (Bare.radialMap (door fun i j=> f i j-f j i)))):= by
 let L:= lineReader u b.1 b.2; have he:= L.continuous_of_finiteDimensional.continuousAt.tendsto.comp (show Tendsto (conduit T A) atTop _ from ray_life f h)
 exact he.congr fun i=> (e i).symm
def RootAns (T:Itinerary)(a:G.Color)(i:Axis)(x:StepPath T): Sight T G:=fun k=> ghostM T a i k (x k)
lemma raises (hp:sails T x v)(hv:v≠0)(j t:Axis)(s:Cover): Tendsto (fun k=> ray j (stalkH T (RootAns T a i x) t) k (wrap (T.period k) s)) atTop (𝓝 (chalk i (fun j=>grad j Green (-v)) a j t)):= by
 let A:=RootAns T a i x; let W:=chalk i (fun j=>grad j Green (-v)) a; change Tendsto (fun k=> ray j (stalkH T A t) k (wrap (T.period k) s)) _ (𝓝 (W j t))
 let C: G.Color:= if t=i then a else 0
 have eq(k:ℕ)(y): ray j (stalkH T A t) k y= ray j (capG T) k (y-x k) • C:= by
    simp only [ray,surface,Pi.smul_apply, combine,up,stalkH,A,RootAns,ghost_value,← sub_smul,smul_smul,C]; rw [add_sub_right_comm];rfl -- equality mul scalar
 let w:StepPath T:= fun k=> wrap (T.period k) s-x k
 have hz : sails T w (-v):=zero_sub v ▸ sails_sub (sails_step s) hp
 have h1:Tendsto (fun k=> ray j (capG T) k (w k)) atTop (𝓝 (grad j Green (-v))):= Score.origin [j] id tendsto_id (-v) (neg_ne_zero.mpr hv) w hz
 simp_rw [eq]; rw [show W j t=(grad j Green (-v)) • C from by unfold W chalk C; split <;> simp]; exact h1.smul_const _
lemma console_pt (A:Sight T G)(i:ℕ): conduit T A i= consoleS (T.period i) (T.gap i)⁻¹ (A i):= rfl
lemma root_answ (k:ℕ): RootAns T a i x k=ghostM T a i k (x k):= rfl
lemma verify1 (b:Badge G)(h:Bool)(k:ℕ) : inner ℝ a (Laurel b h T 0 k (x k,i))= lineReader h b.1 b.2 (conduit T (RootAns T a i x) k):= by
 rw [console_pt,root_answ]; exact la_ghost T a i k (x k) b h
lemma corn (b:Badge G)(h:Bool)(hp:sails T x v)(hv:v≠0): Tendsto (fun k=>inner ℝ a (Laurel b h T 0 k (x k,i))) atTop (𝓝 ((∑ j: Axis,fan h b.1 j i * grad j Green (-v)) * a b.2)):= by
 let W:= chalk i (fun j=>grad j Green (-v)) a; let L:=lineReader h b.1 b.2
 have hx: L (Bare.radialMap (door (fun i j=>W i j - W j i)))=(∑ j: Axis,fan h b.1 j i * grad j Green (-v)) * a b.2:= by unfold L lineReader W; rw [LinearMap.comp_apply,chalkS]; rfl
 rw [←hx]; unfold L; refine handover W _ (raises a i hp hv) b h _ ?_; intro k; exact verify1 (x:=x) a i b h k
end YM.RG11.FirstW
