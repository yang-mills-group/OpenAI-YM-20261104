import YM.OPE.Compatible.Plains.File
/-!
# Leading finite Wick polynomial. transport H⊆...
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell FreeResolvent Paver Rill Saga Shrew
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {N:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{U:Gloam}{d k j r w e m:ℕ}{I:Type}[Fintype I] {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
variable {F:ℕ→Type}[∀ i,NormedAddCommGroup (F i)][∀ i, NormedSpace ℝ (F i)]
omit [BorelSpace E][MeasurableSpace E][FiniteDimensional ℝ E] in
lemma phi_j (p:Saga G e k){V: Reed G→ Module.Dual ℝ E}{A: (i:ℕ)→ Reed G→ Module.Dual ℝ (F i)}{x:(i:ℕ)→ F i}{y:E}{T: Reed G→ Reed G→ℝ}{B:ℕ→ Reed G→ Reed G→ℝ}(hp:∀ j:Reed G, Tendsto (fun i=> A i j (x i)) atTop (𝓝 (V j y))) (hb:∀ i j,Tendsto (fun a=> B a i j) atTop (𝓝 (T i j))) :
   Tendsto (fun i=> Phi p (B i) (A i) (x i)) atTop (𝓝 (Phi p T V y)) :=by
   induction p with
   | @mon i v h hs=>
       have he(s:Finset (Fin i)):Tendsto (fun i=> fauna (fun a b=>B i (v a) (v b)) ((A i)∘ v) s (x i)) atTop (𝓝 (fauna (fun a b=>T (v a) (v b)) (V∘v) s y)):=by
          induction s using Finset.strongInduction with | _ s ih
          obtain rfl|hh:=s.eq_empty_or_nonempty; simp_rw [fanE]; exact tendsto_const_nhds
          let a:=s.min' hh; let t:=s.erase a; have hT:t ⊂ s:= Finset.erase_ssubset (innerA hh).1
          simp_rw [pier _ _ (innerA hh),Pi.sub_apply, Pi.mul_apply,Finset.sum_apply,Pi.smul_apply]; refine Tendsto.sub ((hp (v a)).mul (ih _ hT)) (tendsto_finsetSum t (fun i _=>?_)); exact (hb (v a) (v i)).smul (ih _ (Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset i t) hT))
       exact he _
   | empty=>exact tendsto_const_nhds
   | add _ _ he hh=>exact he.add hh
   | sml c _ hh=> exact (tendsto_const_nhds (x:=c)).smul hh
variable {S:Side}
lemma billTip (hp:S.val∣N.val)(u:Ice G S)(x:Site N)(p:Reed G):fence p x (fun i=>u (trimT _ _ hp i.1,i.2))=fence p (trimT _ _ hp x) u:=by
     rw [fee, fee, zine_tent, zine_tent]; simp only [map_sub, lease]
lemma knownV (x:Site N)(p:Seat k m (Shade G))(hp:S.val∣N.val)(u:Ice G S): Strike k (worldR _ k x _ p) (fun i=>u (trimT _ _ hp i.1,i.2))=Strike k (worldR m k (trimT _ _ hp x) _ p) u:=by
     simp_rw [← cadillac]; unfold Flair Flume.Script.value scribe; apply Finset.sum_congr rfl; intro i _; apply tsum_congr; intro j; apply congr_arg; unfold render;simp only [map_add,lease]
lemma stanceV (x:Site N)(u:Ice G N):Continuous (fun p:Seat k m (Shade G)=> Strike k (worldR _ k x _ p) u):=by
   apply continuous_finsetSum _; intro i _; let Z:=reading (I:=Shade G) m i x; let V:= Z ∘L moduleAt m k i _; exact Continuous.comp (g:=ContinuousMultilinearMap.apply ℝ (fun _:Fin i=>Ice G N) ℝ (fun _=>u)) (f:=V) (ContinuousLinearMap.continuous ..) (V.continuous)
lemma exhibits (q:bed G k m)(p:Saga G e k)(h:∀ n:Side,∀ x:Site n,Strike k (worldR m k x _ q.val)=p.plain x)(r:ℕ)(L:KernelChoices)(hp:r≥4)(x: Site N): Strike k (worldR m k x _ (boostS (atlasF G (Train.top r) hp L) (-(1/2)) m k q.val))= Phi p firm (fun v=> fence v x):=by
    let T(i:ℕ):Side:=⟨N.val*(2*(i+1)),mul_pos N.pos (by omega)⟩; have hv(i:ℕ):N.val∣(T i).val:=dvd_mul_right ..; let X(i):=wrap (T i) (Lattice.lift x); have he(i):trimT _ _ (hv i) (X i)=x:=(lease _ _).trans (wrap_lift ..); have ht:Tendsto (fun i=>(T i).val) atTop atTop:=tendsto_atTop_mono (fun i=> Nat.le_trans (show i≤ 2*(i+1) by omega) (Nat.le_mul_of_pos_left _ N.pos)) tendsto_id
    let R(i):=boostS (pointAt G (Train.top r) hp L (T i)) (-(1/2)) m k q.val; let B:= boostS (atlasF G (Train.top r) hp L) (-(1/2)) _ _ q.val; have hz:Tendsto R atTop (𝓝 B):= fixStrong (loreLap (farN G T (Train.top r) hp L ht)) _ _ tendsto_const_nhds
    funext y; let V(i:ℕ):Ice G (T i):=fun b=> y (trimT _ _ (hv i) b.1,b.2); let b:ℕ→ℝ:= fun i=> Strike k (worldR m k (X i) _ (R i)) (V i); have hh:Tendsto b atTop (𝓝 (Strike k (worldR m k x _ B) y)):=by
         rw [show b=(fun p:Seat k m (Shade G)=>Strike k (worldR _ k x _ p) y) ∘ R from funext fun i=>by rw [show b i= _ from knownV (X i) (R i) (hv i) y,he];rfl]; exact ((stanceV x y).tendsto _).comp hz
    apply tendsto_nhds_unique hh; rw [show b=(fun i=>Phi p (evenCov r L (T i) (X i)) (fun v=> fence v (X i)) (V i)) from ?_]; swap; · funext i; unfold b R; rw [cactus q _ _ (h (T i) (X i)) hp]
    apply phi_j; · intro j; simp_rw [show ∀ i:ℕ,fence j (X i) (V i)= _ from fun i=> billTip (hv i) y (X i) j,he]; exact tendsto_const_nhds
    intro i j; apply barometer _ _ _ _ ht _ hp; filter_upwards with k; exact (even_two_mul _).mul_left _
end YM.OPE.Prairies
