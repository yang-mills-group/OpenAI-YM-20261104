import YM.GradedFar.Round.Aspect
import YM.Work.A04
import YM.Work.B10

/-!
# Physical shape-coordinate derivatives at *all* r-H slots
 Actual derivative maps are already paid at g exponents not depending on B, even
 before proving they have full t-asymptotic. That's enough for moving value comparison.
-/
namespace YM.FVA2.GradedFar.Physical.Round
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh
open Moving Growth Pose Books
open Scale Dframe
open OPE Orbits Logged OPE.Logged.Deck Horizon
open Logged.Economy (Paint)
open OPE.Log (badge)
open Continuation Continuation.Window
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h t : ℕ} {I:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (J K : FramesH P) (θ : ℝ→ℝ) (hq : Earned N M U J K θ) (he : oriented U K) (hl: LogTrace U Q.port)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "Φ"=>spectator U
local notation "V"=>U.sector.derivatives
variable (D:Economy.Small I)
-- No full asymptotic statements on these here; Just power costs.
def bump (d:ℕ) (a:Axis) (r:ℝ) : Sec G d→ₗ[ℂ] Sec G (d+1):=
     (r:ℂ) • ((K r _).symm.toLinearMap ∘ₗ (U.sector.derivatives.deriv d a) ∘ₗ (K r d).toLinearMap)

include Q H hq he
set_option maxHeartbeats 600000 in
lemma crew (d:ℕ)(a:Axis)(x:I→Sec G d) (h : Paint D (fun _=>1) (fun i=> chair G d (x i))) :
    Paint D (fun _=>1) (fun i=> chair G (d+1) (bump U K d a (D.r i) (x i))) := by
    let t i:=K (D.r i) d (x i); let W (j:Fin (d+1)) i := U.sector.derivatives.deriv j.val a (Q.cutTest j.val d (t i)); let L (j:ℕ) i:=(mapK K (D.r i) (j+1)).symm.toContinuousLinearMap
    have hh j : Paint D (fun i=>(D.r i)^(j:ℕ)) (fun i=> Q.cutTest j d (t i)) := by
      have ht:= (accrued N M H U Q J K θ hq he D d j).times_cost (M:=P.Field j) (U:=fun _=>1) h
       (y:=fun i=>Q.cutTest j d (t i)) (Eventually.of_forall fun (i:I)=>by
         unfold t; rw [← mapK_apply]; exact ContinuousLinearMap.le_opNorm (extracted U Q K d j (D.r i)) (chair G d (x i)))
      simpa only [mul_one] using ht
    have hs : Paint D D.r (fun i=>(D.r i:ℂ)):= by refine ⟨1,zero_lt_one,0,?_⟩; filter_upwards with i; simp [Real.norm_eq_abs]
    let X (j:Fin (d+1)) i:= (D.r i:ℂ) • W j i
    have hX (j:Fin (d+1)): Paint D (fun i=>(D.r i)^(j.val+1)) (X j) := by
      apply Paint.eases ((Paint.linear_c _ (hh j.val)).scales hs)
      filter_upwards with i; rw [pow_succ',show D.r i*(D.r i)^j.val=D.r i*(D.r i)^j.val from rfl]
    have hw j : Paint D (fun i=> (D.r i)⁻¹^(j+1)) (L j) := by
      obtain ⟨p,C,hC,H⟩:= inverse_books N M H U J K θ hq he (j+1)
      refine Paint.from_cost C hC p ((D.leaps.eventually H).mono (fun i h=>?_)); rw [log_cost]; apply h.trans_eq; ring
    have hp (j:Fin (d+1)): Paint D (fun _=>1) (fun i=> L j.val i (X j i)):= by
       apply Paint.eases (Paint.times_cost (hw j.val) (hX j) (Eventually.of_forall (fun i=>(L j.val i).le_opNorm (X j i))))
       filter_upwards [D.positive] with i hi; rw [inv_pow, inv_mul_cancel₀ (pow_pos hi _ |>.ne')]
    let H' (j:Fin (d+1)):= Nat.succ_le_succ (Nat.le_of_lt_succ j.isLt)
    let E (j:Fin (d+1)): RowSpace G (j.val+1) →ₗ[ℂ] RowSpace G (d+1):= (chair G _).toLinearMap ∘ₗ up (H' j) ∘ₗ (chair G _).symm.toLinearMap
    let E' i := ∑ j:Fin (d+1), E j (L j.val i (X j i))
    have ht : Paint D (fun _=>1) E':= Paint.sum _ fun i _=> Paint.linear_c (E i) (hp i)
    apply ht.assists; have h : ∀ (j:Fin (d+1)),∀ᶠ i in D.p,∀ b:Sec G (j.val+1), K (D.r i) (d+1) (up (H' j) b)= _ :=
     (fun (j:Fin (d+1))=> D.leaps.eventually (he.raises _ _ (H' j)))
    filter_upwards [eventually_all.mpr h] with i hi
    apply (mapK K (D.r i) (d+1)).injective; unfold E'; rw [map_sum,mapK_apply]; unfold bump; change _= K _ _ ((D.r i:ℂ) • (K _ _).symm (U.sector.derivatives.deriv d a (t i))); rw [map_smul,LinearEquiv.apply_symm_apply,Logged.Trace.rise_cut U Q d (t i),map_sum,Finset.smul_sum]
    apply Finset.sum_congr rfl; intro j hj; unfold E; simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]; rw [mapK_apply, hi j, ← DiffPlan.commute_rise V U.room.kernel.laws.toSymmetric U.phase.transport.injection U.phase.transport.derivatives]; apply Eq.trans ?_ (map_smul ..); apply congr_arg; exact ContinuousLinearEquiv.apply_symm_apply (mapK K ..) _

section derivative
omit Q H hq he
variable (i:Fin n) {q:ℕ}
local notation "T"=>fun _:Fin n=> h
abbrev transferred (v:Tags G h n)(a:Axis)(r:ℝ) : Tags G (h+1) n := update ((up (Nat.le_succ h)) ∘ v) i (bump U K h a r (v i))
-- on `r*x` exact spatial derivative identity, *same* center
lemma fit_gradient (s:Viewers U) (r:ℝ)(u: Inputs G d) {x: Points n}(hp:r • x∈conf n):
    DifferentiableAt ℝ (fun z=> painted U K s d r z u) x := by
    simp_rw [tags_pay]; exact ((P.class_smooth (Φ s) (spectate U s).smooth _).differentiableOn (by norm_num)).differentiableAt ((conf_open n).mem_nhds hp) |>.comp (f:=fun x:Points n=>r • x) x (differentiableAt_id.const_smul r)

lemma fit_slot (s:Viewers U) {r:ℝ}(hr:0<r)(v:Tags G h n)(a:Axis) {x:Points n} (hh:x∈conf n)
    (hi:∀ j:Fin n,K r (h+1) (up (Nat.le_succ h) (v j))=U.sector.derivatives.rise (Nat.le_succ h) (K r h (v j))) :
    fderiv ℝ (fun z=> painted U K s T r z v) x (Points.direction i a) = painted U K s (fun _:Fin n=>h+1) r x (transferred U K i v a r):= by
   let p:=P.useAt (n:=n) (Φ s); let e : ℕ :=h+1; let u:Tags G e n:= (up (Nat.le_succ h)) ∘ v
   let t:= Orbits.tags (d:=fun _:Fin n=>e) (here K r u)
   let b:= K r h (v i)
   have hw:=present hr hh
   let t':= update t i ⟨h,b⟩
   let V':= U.sector.derivatives.deriv h a b
   let H' (z:Points n):=p z t'
   have ht : (fun z:Points n=>painted U K s T r z v)=ᶠ[𝓝 x] (fun z=>p (r • z) t') := by
      filter_upwards [(conf_open _).mem_nhds hh] with z hz
      have hσ := present hr hz
      rw [painted_rise U K s v hσ (d':=fun _=>e) (h:=fun _=> Nat.le_succ _) hi]; change p _ t=_
      have he:= U.sector.derivatives.inclusion_slot (spectate_ready U s) (spectate U s).laws.toSymmetric (Nat.le_succ h) hσ i t b
      change p _ (update t i _) = p _ t' at he
      rw [show (⟨_,U.sector.derivatives.rise (Nat.le_succ h) b⟩ : P.Tag)=t i from ?_, update_eq_self] at he
      · exact he
      exact congrArg (Sigma.mk e) (hi i).symm
   rw [ht.fderiv_eq]; change Points.gradient i a (fun z=> H' (r • z)) x = _; rw [Work.A04.gradient_scaled r H' x _ i a,← U.sector.derivatives.derivative_slot (spectate_evolution U s) (spectate U s).laws.toSymmetric (spectate U s).smooth hw i t b a]; swap; · exact ((P.class_smooth _ (spectate U s).smooth t').contDiffAt ((conf_open n).mem_nhds hw)).differentiableAt (by simp)
   unfold transferred bump
   change r • (p _ (update t i (⟨e,V'⟩:P.Tag)))= painted U K s (fun _=>e) r x (update u i ((r:ℂ) • (K r e).symm V'))
   rw [MultilinearMap.map_update_smul,Complex.real_smul,tags_pay]; refine congrArg ((r:ℂ)*·) ?_; change p (r • x) _= p (r • x) _; apply congr_arg
   funext j; by_cases h:j=i; · subst j; simp [t,Orbits.tags,here]
   rw [Function.update_of_ne h]; unfold Orbits.tags t here; rw [Function.update_of_ne h]; rfl
end derivative
end
end YM.FVA2.GradedFar.Physical.Round
