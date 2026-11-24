import YM.FormalBulk08.Pose.Ice

/-! Prove Color of weighted lens before interpreting as invariant polynomials. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Pose
open Filter Function Lattice Laurent Gauge Wilson Exterior Stationary
open Lava Lotus Mesa Gorge Shore City Kemp Rift Reef
open Planned.PrimaryIntegral295 Place Carrier Film Labels Source Source.Drops Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {r d n D u:ℕ}{η A : ℝ} (H: Source.Hol G)

-- regroup indices by color with explicit `Jot` to use Lust.
abbrev Stoop := Cover × TypeFace 1
def arctic (G:Gauge)(r:ℕ): chain Stoop r × chain (hue G) r ≃ chain (edgeL G) r where
    toFun x i:=((x.1 i).1,(x.1 i).2,x.2 i)
    invFun v:= (fun i=> ((v i).1,(v i).2.1),fun i=> (v i).2.2)
    left_inv _ := rfl
    right_inv _:=rfl
lemma slump {E F:Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E][NormedSpace ℝ F]
    (L:E→L[ℝ]F){f : F → ℝ}(hs:ContDiffAt ℝ n f 0) (x: Fin n→E) : Tensor.coeff (f ∘ L) n 0 x=Tensor.coeff f n 0 (L ∘ x):= by
    unfold Tensor.coeff; rw [Next.Foundations.jets_linear L hs]; rfl -- general
lemma slate_arctic (b: Loc G 1)(T:Tile (edgeL G) r)(L: Fin n→Snap G d)(hs:0<η)(ht: Knoxville (fame _) η (0,b) T A): slate T d n L=∑' v:chain Stoop r, ∑ i,T (arctic G r (v,i))*Tensor.coeff (tier (arctic G r (v,i))) n 0 L:=by
    rw [slate_read b T L hs ht,←Equiv.tsum_eq (arctic G r)];
    have he:= (arctic G r).summable_iff.mpr (slate_wind b T L hs ht); simp only [Function.comp_def] at he; rw [Summable.tsum_prod he]; exact tsum_congr fun v=> tsum_fintype _
lemma stack_val {I E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] (S:Finset I)(c:I→ℝ)(F:I→ E→ℝ) (x:Fin n→E)(h:∀ i∈S,ContDiffAt ℝ n (F i) 0):
   Tensor.coeff (∑ i∈S,c i • F i) n 0 x=∑ i∈S,c i*Tensor.coeff (F i) n 0 x:= by
    rw [Tensor.coeff_sum _ _ (fun i=>c i • F i) S (fun i hi=> (h i hi).const_smul (c i)), _root_.sum_apply]; apply Finset.sum_congr rfl; intro i hi; rw [Tensor.coeff_smul _ (h i hi)];rfl
include H
lemma colors_ark (T:Tile (edgeL G) r)(h:Lust T)(g:G.El)(w:chain Stoop r):
    (fun x:Snap G d=>∑ i:chain (hue G) r,(T (arctic G r (w,i))) * tier (arctic G r (w,i)) (colorIn G d g x)) =ᶠ[𝓝 0] fun x=>∑ i,T (arctic G r (w,i))* tier (arctic G r (w,i)) x := by
   let X (b : Stoop)(x:Snap G d):= Film.lane (Place.seat b.1) (axisEquiv.symm b.2) x
   have hh (i:Fin r) := Film.light (d:=d) H g ((w i).1,axisEquiv.symm (w i).2)
   filter_upwards [eventually_all.mpr hh] with p hp
   let A j (i:hue G):= X (w j) p i
   let V(i:chain (hue G) r):= arctic G r (w,i)
   have he (i:chain (hue G) r) (j:Fin r): curtain (V i j) (colorIn G d g p)=∑ x:hue G,suit g (i j) x * A j x:= by
      change X (w j) (colorIn G d g p) (i j)=_
      rw [show X (w j) (colorIn G d g p)=_ from hp j]; exact (congr_fun (shy g (X (w j) p)) (i j)).symm
   change (∑ i, T (V i)*∏ j, curtain (V i j) _) = (∑ i,T (V i)* ∏ j,A j (i j)); simp_rw [he,Fintype.prod_sum,Finset.prod_mul_distrib,Finset.mul_sum,←mul_assoc]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> ?_; rw [←Finset.sum_mul]; congr 1; exact (h g (V i)).symm
set_option maxHeartbeats 600000 in
lemma color_slate (b:Loc G 1)(T:Tile (edgeL G) r)(h:Lust T)(hs:0<η)(ht: Knoxville (fame _) η (0,b) T A)(g:G.El) (x:Fin n→Snap G d): slate T d n (colorIn G d g ∘ x)=slate T d n x:= by
   rw [slate_arctic b T _ hs ht,slate_arctic b T x hs ht]; apply tsum_congr; intro v
   let X i:=arctic G r (v,i); let f i : Snap G d→ℝ:= T (X i) • tier (X i);let L:=colorIn G d g
   have he i : ContDiffAt ℝ _ (tier (X i) (d:=d)) 0:=(tier_diff ..).of_le (show (n:WithTop ℕ∞)≤ω from le_top)
   have hS i: ContDiffAt ℝ n (tier (X i) ∘ L) 0:= ((map_zero L).symm ▸ he i).comp (f:=L) _ L.contDiff.contDiffAt
   have hF := colors_ark H T h g v (d:=d); have hz:(∑ i, T (X i) • (tier (X i) ∘ L)) =ᶠ[𝓝 0] (∑ i,f i):= by
       filter_upwards [hF] with p hp; rw [Finset.sum_apply,Finset.sum_apply]; exact hp
   have ht := DFunLike.congr_fun (Tensor.GermCoeff n hz) x
   have hp:= ((stack_val Finset.univ (fun i=> T (X i)) (fun i=>tier (X i) ∘ L) x (fun i _=>hS i)).symm.trans (ht.trans (stack_val Finset.univ (fun i=> T (X i)) _ x (fun i _=>he i))))
   refine Eq.trans (Finset.sum_congr rfl ?_) hp; intro i _; exact congr_arg (T (X i)*·) (slump L (he i) x).symm
omit H
lemma perfumed (Y : Anthem D G){b:Loc G 1}(hp:Clef b Y u)(f:Dawn.Studio D)(a r): Lust (Y f a r):= by -- auto b
   have hv:=hp.fare; obtain ⟨s,C,hs,-,H⟩:=hv.2.2 a r; let T:= _root_.YM.FormalBulk08.Kemp.banner u (Y f)
   refine stainedL (Y f a r) T a ?_ (.of_forall (fun n=>(solo_iff Y).mp hp.ward n f)); unfold T; simp_rw [badge (Y f) (hv.1 f) (hv.2.1 f) le_rfl]; exact (sieve_kalm _ (H f) hs.le).1
end YM.FormalBulk08.Pose
