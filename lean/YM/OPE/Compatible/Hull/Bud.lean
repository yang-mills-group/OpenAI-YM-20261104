import YM.OPE.Compatible.Hull.Flight
import YM.OPE.Compatible.Vines.Icing
/-! # polynomial reading low along link-integral ray. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set Lattice MeasureTheory RG Wilson Flume Flume.Page Flume.Script Gauge
open Source Labels Source.Drops Next.Rank Next.Rank.Spindle Tensor WilsonStartup
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
attribute [local instance] Drops.instNormedSpaceRealSnap
variable {G:Gauge}{d m n b:ℕ}(H:Hol G)
def FolkU (F:Lieu Axis→ℝ)(g:ℝ→ℝ)(u:E4)(v:Lieu Axis):= ∫ x in (0:ℝ)..1,g x*F (invertX (fromX v+x • u))
lemma goldF (F:Lieu Axis→ℝ)(h:F∈Flavor Axis d)(u:E4)(v:Lieu Axis): Continuous (fun x:ℝ=> F (invertX (fromX v+x • u))):=(jig h).continuous.comp (by fun_prop:Continuous (fun x:ℝ=> fromX v+x • u))
lemma spices (F:Lieu Axis→ℝ)(h:F∈Flavor Axis d)(g:ℝ→ℝ)(hg:Continuous g)(u:E4): FolkU F g u ∈ Flavor Axis d:=by
    apply flavor_elim h _ ?_ ?_ ?_ ?_
    · intro l hl; have hh(l:List Axis)(g:ℝ→ℝ)(hg:Continuous g): FolkU (tasting l) g u∈ Flavor Axis l.length :=by
           induction l generalizing g with
           | nil=> change (fun v: Lieu Axis=> ∫ x in (0:ℝ)..1, g x* tasting [] _)∈ _; simp only [tasting,List.map_nil,List.prod_nil]; exact flavor_cast _ _
           | cons i l ih=>
                let f:ℝ→ℝ:=fun x=> x*g x; have hf:Continuous f:= continuous_id.mul hg; let Rv(v:Lieu Axis):=v i; let L:=tasting l; let P:= FolkU L g u; let Q:= FolkU L f u; have he:FolkU (tasting (i::l)) g u=Rv*P+(u i) • Q:=by
                    funext v; let E(x:ℝ):= L (invertX (fromX v+x • u)); have hE:Continuous E:=goldF L (flavor_part _ _ le_rfl) u v; change (∫ x in (0:ℝ)..1, g x*((v i+x*u i)* E x))= _*P v+ u i* Q v; rw [show (fun x=> g x*((v i+x*u i)* E x))=(fun x=>v i * (g x * E x))+ (fun x=>u i*(f x* E x)) from funext fun x=>by unfold f; change _ = v i*_+u i*_; ring]; apply (intervalIntegral.integral_add (((show Continuous (fun _ :ℝ => v i) from continuous_const).mul (hg.mul hE)).intervalIntegrable 0 1) (((show Continuous (fun _:ℝ=>u i) from continuous_const).mul (hf.mul hE)).intervalIntegrable 0 1)).trans; change (∫ x in (0:ℝ)..1, v i * (g x * E x))+(∫ x in (0:ℝ)..1, u i*(f x* E x))= _; rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]; rfl
                rw [he,List.length_cons]; refine (Flavor Axis _).add_mem (flavor_up (show (1+l.length)≤ l.length+1 from by omega) (flavor_prod (flavor_position i) (ih _ hg))) ((Flavor Axis _).smul_mem _ (flavor_up (Nat.le_succ _) (ih f hf)))
      exact flavor_up hl (hh l g hg)
    · have ht : FolkU (0:Lieu Axis→ℝ) g u=0:=by funext v; simp [FolkU]
      rw[ht]; exact (Flavor Axis d).zero_mem
    · intro p q hp hh hv hw; rw [show FolkU (p+q) g u=FolkU p g u+FolkU q g u from funext fun v=>by change (∫ x in (0:ℝ)..1,g x * (p _+q _))= _; simp only [mul_add]; exact intervalIntegral.integral_add ((hg.mul (goldF p hp u v)).intervalIntegrable 0 1) ((hg.mul (goldF q hh u v)).intervalIntegrable 0 1)]; exact (Flavor Axis _).add_mem hv hw
    intro r p hp hv; rw[show FolkU (r • p) g u=r • FolkU p g u from funext fun i=>by unfold FolkU; simp only[Pi.smul_apply,smul_eq_mul,mul_left_comm (g _),intervalIntegral.integral_const_mul]]; exact (Flavor Axis _).smul_mem _ hv
lemma hymn (x:Snap G d)(hx:∀ i, n < i.val+1→ x i=0): Low (Sie x) n:=by
    intro i; let q:G.Color→L[ℝ]ℝ:= EuclideanSpace.proj i.2; let F (j:ℕ) : Lieu Axis→ℝ:=diagonal (q.compContinuousMultilinearMap ((expand d x j).val i.1))∘fromX; let f(j:ℕ):=FolkU (F j) (fun _=>1) (basis i.1); let T: Finset ℕ:= Finset.range (d-1); have hf(j:ℕ)(he:j∈T): f j∈Flavor Axis n:=by
            have hz:j<d-1:=Finset.mem_range.mp he; apply spices _ _ _ continuous_const; by_cases h:j+1 ≤ n; exact flavor_up h (tgon _); let I:Fin (d-1):=⟨j,hz⟩; rw [show F j=0 from funext fun v=>by change q ((expand d x j).value i.1 (fromX v))=_; rw [expand,dif_pos hz,hx I (lt_of_not_ge h)]; exact q.map_zero]; exact (Flavor _ _).zero_mem
    refine ⟨_, (Flavor Axis _).sum_mem hf, ?_⟩; intro y; let z:E4:= fromX (translit y); let E(j:ℕ)(s:ℝ):G.Color:= (expand d x j).value i.1 (z+s • basis i.1); have he(j):Continuous (E j):=(diag_smooth _ 1).continuous.comp (by fun_prop:Continuous (fun s:ℝ=>z+s • basis i.1)); change q (∫ s : ℝ in 0..1, partConnection d (expand d x) 1 (y,i.1) s)= _; simp_rw[partConnection, one_smul]; change q (∫ s : ℝ in 0..1,∑ j∈T,E j s)= (∑ j∈T,f j) (translit y); rw [intervalIntegral.integral_finsetSum (fun i hi=> (he i).intervalIntegrable _ _),_root_.map_sum,Finset.sum_apply]; refine Finset.sum_congr rfl fun j _=>?_ ; unfold f FolkU; simp_rw [one_mul]; exact (q.intervalIntegral_comp_comm ((he j).intervalIntegrable 0 1)).symm -- orientation
-- rank of Flash directions
private lemma scalarRayDerivative {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : V) (k r : ℕ) :
    iteratedDeriv r (fun t : ℝ => t ^ k • v) 0 =
      (k.descFactorial r * (0 : ℝ) ^ (k - r)) • v := by
  let L : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  change iteratedDeriv r (L ∘ fun t : ℝ => t ^ k) 0 = _
  erw [guiding L _ r 0 (show ContDiffAt ℝ r _ _ from contDiffAt_id.pow _), iteratedDeriv_pow]
  rfl

private lemma flashDerivativeAt (x : Snap G d) (i : Fin (d - 1)) (r : ℕ) :
    (iteratedDeriv r (flash x) 0) i =
      ((i.val + 2).descFactorial r * (0 : ℝ) ^ (i.val + 2 - r)) • x i := by
  let L : Snap G d →L[ℝ] Taylor G i.val := ContinuousLinearMap.proj i
  have project : L ∘ flash x = fun t : ℝ => t ^ (i.val + 2) • x i := by
    funext t
    change flash x t i = _
    unfold flash Drops.trunk scaleJet expand
    rw [dif_pos i.isLt]
  calc
    (iteratedDeriv r (flash x) 0) i = iteratedDeriv r (L ∘ flash x) 0 :=
      (@guiding (Taylor G i.val) (Snap G d) _ _ _ Drops.instNormedSpaceRealSnap
        L (flash x) r 0 (flashDiff x).contDiffAt).symm
    _ = _ := by rw [project, scalarRayDerivative]

lemma Sea (x:Snap G d)(r:ℕ): Low (Sie (iteratedDeriv r (flash x) 0)) (r-1):=by
  apply hymn
  intro i hi
  rw [flashDerivativeAt, zero_pow (show i.val + 2 - r ≠ 0 by omega), mul_zero, zero_smul]
end YM.OPE.Spells
