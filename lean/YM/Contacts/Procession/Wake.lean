import YM.Contacts.Shuttle.Vienna
/-!
# Coefficient differential of the compact unmarked PT recursion

Shift marker announcing time in the count algebra before recombining,
works for any number of formal valencies. Exact polynomial.Gather
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Sun
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open MeasureTheory Analysis Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Pulse.Spine Origin
open Milling Milling.Steam Milling.Forge Pulse.Form
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff
variable {X Y α E : Type}{n i v w r t k:ℕ} [Fintype α]
-- Billing finite.
abbrev St (α: Type):= Pulse.Rack α
section
variable (g:α→α→ℝ)
def brillo : (St α)→ₗ[ℝ] St α where
   toFun x j:= Pulse.degree g (x (j+2))
   map_add' x y:= by ext1 i; ext1 f; simp [Pulse.degree,printRun,reorder,Pulse.loop,sway,tsum_fintype,mul_add, sum_add_distrib, smul_eq_mul]
   map_smul' a x:= by ext1 i; ext1 f; simp [Pulse.degree,printRun,reorder,Pulse.loop,sway,tsum_fintype, smul_eq_mul,mul_left_comm _ a, mul_sum]
def greet (f h: St α): St α:= fun j=> listPay g f h j
private lemma l_add (f h y z:St α): light g n i r (f+y) (h+z)=light g n i r f h+light g n i r f z+(light g n i r y h+ light g n i r y z):= by
   unfold light; split
   next e=> subst n; dsimp only [takeRank]; ext1 a; simp [Pulse.meter,printRun,reorder,stitch,squeeze,tsum_fintype,mul_add, add_mul,sum_add_distrib,smul_eq_mul]; abel
   simp
private lemma l_scale (f h:St α)(a b:ℝ): light g n i r (a • f) (b • h)= (a*b) • (light g n i r f h):= by
   unfold light; split
   next e=> subst n; dsimp only [takeRank]; ext1 x; simp [Pulse.meter,printRun,reorder,stitch,squeeze,tsum_fintype,smul_eq_mul,mul_sum]; apply Finset.sum_congr rfl; intro t _; apply Finset.sum_congr rfl; intro i _; ring
   simp
@[simp] private lemma l_zero (f:St α): light g n i r f 0=0∧ light g n i r 0 f=0:= ⟨light_close_right g rfl,light_close_left g rfl⟩
def crossH : St α→ₗ[ℝ] St α→ₗ[ℝ] St α:=by
   refine LinearMap.mk₂ ℝ (greet g) ?_ ?_ ?_ ?_
   all_goals intros; ext1 i; unfold greet listPay
   · simp_rw [Pi.add_apply]; let X:=Type; rename_i f p q; simp_rw [show ∀ a b, light g i a b (f+p) q=_ from fun a b=> (show _=light g i a b f q+light g i a b p q from (by simpa [(l_zero ..).1] using l_add (n:=i) (i:=a) (r:=b) g f q p 0)),sum_add_distrib] -- edit args
   · rename_i a p q; simp_rw [show ∀ i j k, light g i j k (a • p) q=_ from fun i j k=> (show _=a • light g i j k p q from by simpa using l_scale (n:=i) (i:=j) (r:=k) g p q a 1), Pi.smul_apply,smul_sum]
   · rename_i f p q; simp_rw [show ∀ i j k, light g i j k f (p+q)=_ from fun i j k=> (show _= light g i j k f p + light g i j k f q from by simpa [(l_zero ..).2] using l_add (n:=i) (i:=j) (r:=k) g f p 0 q),Pi.add_apply,sum_add_distrib]
   rename_i a f q; simp_rw [show ∀ i j k, light g i j k f (a • q)=_ from fun i j k=>(show _= a • light g i j k f q from by simpa using l_scale (n:=i) (i:=j) (r:=k) g f q 1 a), Pi.smul_apply, smul_sum] -- arg order
abbrev GridTime (α:Type):= ℕ→House α
-- define as linear to preserve arbitrary coefficients
def convK (F H: GridTime α) (i t:ℕ): St α:= ∑ j∈antidiagonal i,∑ q ∈ antidiagonal t, crossH g (F q.1 j.1) (H q.2 j.2)
lemma wake_comp (H:GridTime α): wake g H i t = brillo g (H t i) + convK g H H i t:= by ext1 r; simp_rw [convK,Pi.add_apply,Finset.sum_apply]; rfl
def indus (A Q:GridTime α)(i t):= brillo g (Q t i)+ convK g A Q i t +convK g Q A i t
def walk (A Y:House α):GridTime α
| 0=>Y
| t+1=> fun e=> ( ((t+1:ℕ):ℝ)⁻¹ ) • indus g (gathering g A) (fun i=> if _h:i < t+1 then walk A Y i else 0) e t
termination_by i=>i
private lemma protect (V W U L:GridTime α)(h:∀j≤t, V j=L j)(hh:∀j≤t,U j=W j): convK g L U v t= convK g V W v t:= by
   refine sum_congr rfl fun i _=> sum_congr rfl fun j hj=>?_ ; have hx:=mem_antidiagonal.mp hj; rw [h j.1 (by omega),hh j.2 (by omega)]
lemma respects (V W A:GridTime α)(h:∀j≤t,V j=W j): indus g A V i t=indus g A W i t:= by rw [indus,indus,protect g A W V A (fun _ _=>rfl) h, protect g W A A V (fun i hi=> (h i hi).symm) (fun _ _=>rfl),h t le_rfl]
lemma walk_start (A Y:House α): walk g A Y 0=Y:= by rw [walk]
lemma walk_step (A Y:House α): walk g A Y (t+1) i= ( ((t+1:ℕ):ℝ)⁻¹ ) • indus g (gathering g A) (walk g A Y) i t:= by rw [walk]; exact congr_arg (fun p: St α=> (((t+1:ℕ):ℝ)⁻¹) • p) (respects g _ _ _ fun i h=> dif_pos (Nat.lt_succ_iff.mpr h)) -- private expose soon
end
end YM.Contacts.Procession.Sun
