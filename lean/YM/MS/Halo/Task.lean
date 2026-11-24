import YangMills.WilsonProof.NativeSupport.YM.MS.Halo.Air
/-!
# D Surf covariance. Master action separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Halo.Surf
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Emit Rock Path Oceans
open _root_.YM.MS.Shine Hem Mell Motif Alps
open scoped Topology ContDiff InnerProductSpace
variable {J:Type}{G:Gauge} {m n k:ℕ}{flag:Bool}{z:ℂ}{X F H: Rack G n}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 "⋄"=> product S
variable (P:Surf G m n)
private def pass (E:Type)[AddCommMonoid E][Module ℂ E](a:Arts.L n) : (Arts.L m→E)→ₗ[ℂ] E where
    toFun U:= ∑ i:Arts.L m, P.profile i a • U i
    map_add' U V:= by simp only [Pi.add_apply,smul_add,Finset.sum_add_distrib]
    map_smul' z U:= by simp only [Pi.smul_apply,RingHom.id_apply, Finset.smul_sum, smul_comm z _]
abbrev air (P:Surf G m n) : Mield G n→ₗ[ℂ] Mield G m where
    toFun F i:= P.run (F i)
    map_add' F J:= funext fun i=> map_add _ (F i) (J i)
    map_smul' s U:= funext fun i=> map_smul _ s (U i)
lemma onAir (F:Mield G n)(i:G.ColorIndex) : P.air F i=P.run (F i):= rfl
lemma jaw (U Y:Mield G n) : P.air (Motif.jaw G n U Y)= Motif.jaw G m (P.air U) (P.air Y):= by
    funext i; simp_rw [onAir, chew,map_sum,map_smul,P.prod]; rfl -- rb uses bite def
lemma vect (flag:Bool)(a:Arts.L n): P.air (lip flag (some a))= ∑ j:Arts.L m, P.profile j a • lip flag (some j):= by funext i; simp only [ onAir, Finset.sum_apply, Pi.smul_apply]; exact P.vec ..
lemma γc (flag:Bool): P.air (lip flag none)=lip flag none:= funext fun _=> P.noneC ..
lemma runA (a:Arts.L n): P.air (Motif.A n G a)= ∑ j:Arts.L m, P.profile j a • Motif.A m G j := P.vect false a
lemma axis (a:Arts.L n)(F:Mield G n): P.air (axisP a F)= ∑ i:Arts.L m,P.profile i a • axisP i (P.air F) := by funext j; simp only [onAir,axisP,lock,Finset.sum_apply,Pi.smul_apply,P.drv]
lemma grip (z:ℂ)(a:Arts.L n)(F:Mield G n): air P (convoke z a F)=∑ i:Arts.L m,P.profile i a • convoke z i (P.air F) := by
    simp only [convoke,LinearMap.add_apply,map_add,map_smul,axis, P.jaw,runA,LinearMap.smul_apply, map_sum,LinearMap.sum_apply, Finset.smul_sum, smul_add,Finset.sum_add_distrib]; simp_rw [smul_comm z _]
-- curvature.Double
variable (z:ℂ)
lemma earth (a b:Arts.L n): P.air (cur z a b)=∑ i:Arts.L m, P.profile i a • ∑ j: Arts.L m, P.profile j b • cur z i j:= by
    simp only [cur,F₀,map_add,map_sub,map_smul,axis,runA,P.jaw,map_sum,LinearMap.smul_apply,LinearMap.sum_apply,smul_add,smul_sub, Finset.sum_add_distrib,Finset.sum_sub_distrib]; -- P.jaw before runA may require simp?
    simp_rw [Finset.smul_sum,smul_comm z _]; congr! 1; · rw [Finset.sum_comm (f:=fun j i=>P.profile j b • P.profile i a • axisP j ( A m G i ))]; simp_rw [smul_comm (P.profile _ b) ]
    rw [ Finset.sum_comm]; simp_rw [smul_comm (P.profile _ b)]
-- iso lemma for collapsing
lemma right {E U V:Type}[AddCommMonoid E][Module ℂ E][AddCommMonoid U][Module ℂ U][AddCommMonoid V][Module ℂ V] (L:E→ₗ[ℂ] U→ₗ[ℂ] V) (x:Arts.L m→E ) ( y:Arts.L m→U): (∑ i: Arts.L n,L (∑ j:Arts.L m,P.profile j i • x j ) ( ∑ j:Arts.L m,P.profile j i • y j))=∑ i:Arts.L m,L (x i) (y i):= by
    simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,Finset.smul_sum,smul_smul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; simp_rw [← Finset.sum_smul,P.iso]; simp [ite_smul]
lemma printZ (x y:Mield G n): P.run (sume x y)=sume (P.air x) (P.air y):= by unfold sume; simp_rw [map_sum,P.prod,onAir]
def rim (G:Gauge)(n:ℕ): Mield G n →ₗ[ℂ] Mield G n→ₗ[ℂ] Rack G n:= LinearMap.mk₂ ℂ ( Motif.sume ) ( fun a b c=> by simp only [ sume,map_add,Pi.add_apply,LinearMap.add_apply,Finset.sum_add_distrib]) (fun a b c=> by simp only [sume,Pi.smul_apply,map_smul,LinearMap.smul_apply, Finset.smul_sum]) (fun a b c=> by simp only [sume, map_add,Pi.add_apply,Finset.sum_add_distrib]) (fun a b c=> by simp only [sume,Pi.smul_apply,map_smul, Finset.smul_sum])
private lemma forward (x y:Arts.L m →Arts.L m → Mield G m ) ( b:Arts.L n): ∑ a:Arts.L n,sume (∑ i:Arts.L m,P.profile i a • ∑ j:Arts.L m,P.profile j b • x i j ) ( ∑ i: Arts.L m,P.profile i a • ∑ j:Arts.L m,P.profile j b • y i j)=∑ a:Arts.L m,sume (∑ j:Arts.L m,P.profile j b • x a j ) ( ∑ j:Arts.L m,P.profile j b • y a j):= right P (rim G m) (fun a:Arts.L m=> ∑ j:Arts.L m,P.profile j b • x a j) _ -- defeq
lemma sunk : P.run (Motif.core G n z)=Motif.core G m z:= by
    unfold Motif.core; simp_rw [map_smul,map_sum,P.printZ,P.earth]; congr 1; rw [Finset.sum_comm]; simp_rw [forward]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _=>?_ ; exact P.right (rim G m) _ _
-- cape factor rewrite
lemma reach (G:Gauge)(n:ℕ): cape (applyS z G n)= (∑ a:Arts.L n,sume (lip true (some a)) ( convoke z a ( cwave n G ))) - sume (lip true none) ( Sc z G n ):= by
   unfold cape applyS; simp only [ Chan, Fintype.sum_prod_type,Fintype.sum_option,phase, Option.some_ne_none,if_false,one_smul, if_true,neg_one_smul,Finset.sum_neg_distrib]; change -sume (lip true none) ( Sc z G n ) + (∑ a:Arts.L n,sume (lip true (some a)) ( convoke z a ( cwave n G ))) =_; abel -- P arg implicit? `include` not used
lemma merit : P.run (ploy G z n)= ploy G z m:= by
    have he: P.air ( cwave n G )= cwave m G:= γc P false; simp only [ploy,reach,map_add,map_sub,map_sum,sunk,P.printZ, Sc, map_smul,P.jaw, he,vect,grip,γc]; -- burde bu
    congr! 2; exact P.right (rim G m) _ _
lemma levy : Sturdy true (ploy G z):= ⟨fun _ X _=> merit (orbit X G) z, fun v w=> congr_fun (merit (border G v) z) w ⟩
-- B₁ & B₂ invariant via odd/even parts or coefficient parse. extract value via linear equality at true
lemma eu (k:ℕ): Sturdy true (pulseX G k):= by
    let K:=χ G; have hf(z:ℂ): Sturdy true (Literal.value (Mob G) z K):= by rw [Class_at]; rw [sub_eq_add_neg,← neg_one_smul ℂ]; exact Sturdy_plus (levy z) ( Sturdy_scale (levy 0) _ ); -- coeff parameter Hym
    constructor
    · intro i s hs; funext l; let f: Mob G →ₗ[ℂ] ℂ:= ( (LinearMap.proj l: Rack G i→ₗ[ℂ] ℂ).comp ((flagS s G).beam)).comp (LinearMap.proj i); let g:=Garment.Wave.slice l; exact sub_eq_zero.mp (valuedZ K (f-g) (fun z=>sub_eq_zero.mpr (congr_fun ((hf z).turn i s hs ) l)) k)
    intro i j hi w; exact sub_eq_zero.mp (valuedZ K ( Garment.Wave.slice (Arts.lift hi w)-Garment.Wave.slice w ) (fun z=> sub_eq_zero.mpr ((hf z).grows hi w)) k)
end YM.MS.Halo.Surf
