import YM.OPE.Compatible.Plains.Hope
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
local notation "Λ"=> PAD I
abbrev ProbeCov (M:Silt.Mat I)(a b:Module.Dual ℝ Λ):= ∑ i, ∑ j, M i j * a (Pi.single i 1) * b (Pi.single j 1)
lemma axisCash (a:Module.Dual ℝ Λ)(z:Λ): a z= ∑ i,z i*a (Pi.single i 1):=by
   have hp: z=∑ i:I,z i • Pi.single (M:=fun _=>ℝ) i 1:=by ext q; simp [Pi.single_apply, mul_ite]
   nth_rw 1 [hp];simp
omit [BorelSpace E] [MeasurableSpace E] in
lemma devote (A:Law E)(Z:E→L[ℝ] Λ)(a b: Module.Dual ℝ Λ): A.wick (a ∘ₗ Z.toLinearMap) (b ∘ₗ Z.toLinearMap)= ProbeCov (chamber A Z) a b:=by
     let K:=chamber A Z; have he(g:Module.Dual ℝ Λ): g ∘ₗ Z.toLinearMap=∑ i,g (Pi.single i 1) • coQ Z i:=by
         apply LinearMap.ext; intro x; change g (Z x)= _; rw [axisCash,LinearMap.sum_apply]; exact Finset.sum_congr rfl (fun i _=> mul_comm ..)
     rw [he,he,Law.wick]; simp_rw [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]; simp only[smul_eq_mul, Finset.mul_sum, ProbeCov]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; change a _*(b _*(K i j))=K i j *_ *_; ring
abbrev evenCov (r:ℕ)(L:KernelChoices)(N:Side)(x:Site N)(p q:Reed G) := ProbeCov (Cot L G (Train.top r) N) (fence p x) (fence q x)
def Phi (p: Saga G e k)(W:Reed G→ Reed G→ℝ)(V: Reed G→ Module.Dual ℝ E): E→ℝ:= match p with
| Saga.mon l _ _=> fauna (fun i j=>W (l i) (l j)) (V ∘ l) Finset.univ
| Saga.empty=>0
| Saga.add Y Z=>Phi Y W V+Phi Z W V
| Saga.sml c X=> c • Phi X W V
omit [BorelSpace E][MeasurableSpace E][FiniteDimensional ℝ E] in
lemma phiB (p:Saga G e k)(W:Reed G→Reed G→ℝ)(V: Reed G→ Module.Dual ℝ E): Bond (Phi p W V):=by
   induction p with
   | mon => exact incense ..
   | add x y a b=> exact a.add b
   | empty=> exact Bond.zero
   | sml a b ht=> exact Bond.scale a ht
lemma chant_rule (p: Saga G e k)(A:Law E)(Z:E→L[ℝ] Ice G N)(μ:Measure E)[μ.IsAddHaarMeasure](g:Ice G N)(x:Site N) (h: Cot L G (Train.top r) N = chamber A Z):
   let f(v:Reed G):= fence v x
   A.average μ (fun y=>Phi p (evenCov r L N x) f (g+Z y))= p.plain x g:=by
       intro f; induction p with
       | @mon i v h' _=>
           have hv(a b: Reed G):evenCov r L N x a b=A.wick (f a ∘ₗ Z.toLinearMap) (f b ∘ₗ Z.toLinearMap):=by rw [devote,← h]
           unfold Phi; simp_rw [hv]; exact sing_after μ A Z _ g Finset.univ -- f∘v
       | empty=>exact singleConst ..
       | add a b I H=> exact (sun μ A (stayBond Z (phiB a (evenCov r L N x) f) g) (stayBond Z (phiB b (evenCov r L N x) f) g)).trans (congr_arg₂ (·+·) I H)
       | sml a b hB=> exact (scooted μ A a (fun y=>Phi b (evenCov r L N x) f (g+Z y))).trans (congr_arg (a * ·) hB)
lemma W_step (q: bed G k m)(x:Site N): worldR m k x _ q.val ∈ harmon (Ice G N) k:=by
     let R(i):= worldR m k x _ q.val i; let S:=lilies m k (Shade G) q.val; have hv(i:ℕ)(z:Fin i→Ice G N): R i z=scribe x (S i) z:=by
        rw [show R i= orchestra (S i) x from toScript ..]; exact (instruments _ (Silt.Float.tiller m (moduleAt m k i _ q.val)) x _).tsum_eq.symm
     refine ⟨fun i hi=>?_ ,fun i z p=>?_⟩ ; change R _= _ ; ext1 a; rw [hv,show S i=0 from (sproutV ..).1 _ hi]; simp [scribe]; change R i _= R i _; rw [hv, hv,← rotating p,show swing p (S i)= _ from (merit (p:=q.val) q.property i).2.1 p]
lemma cactus (q:bed G k m)(p:Saga G e k)(x:Site N)(h:Strike k (worldR m k x _ q.val)=p.plain x)(hp:r≥4): Strike k (worldR m k x _ (boostS (pointAt G (Train.top r) hp L N) (-(1/2)) m k q.val))= Phi p (evenCov r L N x) (fun v=> fence v x):=by
     obtain ⟨A,Z,hA⟩:= realise (Cot L G (Train.top r) N) (cotSem hp); let μ:= (MeasureTheory.volume:Measure (EuclideanSpace ℝ (Tab (Shade G) N))); rw [boostS,flareV x _ (formsC (v:=Train.top r) hp x),hA]; exact heaters μ A Z _ (W_step q x) _ (phiB ..) (fun y=>by rw [h]; exact chant_rule _ A Z μ y x hA)
end YM.OPE.Prairies
