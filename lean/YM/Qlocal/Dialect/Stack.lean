import YM.Qlocal.Dialect.Compare
/-! # Authorization billing table for REAL mode collector He.Shape.Frame.Clock. Continue. 
 Algebra at fixed m or Replica.Emit_Data clock. Keep **true momentum** in higher Tale, even when evaluating on small period. All aliases opaque Meta.X.Attribute.Tensor.Template.C.Sphere.Shape.We.Actor`. No replacing representation on unmarked path. Coalescing BEFORE kink.We.Timestamp.Art.Eff.ensor.Budget is for nominal mask application.Intent.En.Cell.Property.ISK. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Dialect
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Push.AbsoluteSums RG3.Press
open scoped Topology ContDiff BigOperators Classical
open Publishing Parabola Integration.RiderTastePresentation Integration.LocalComparison Extra.Trajectories
variable {V Ω J J' J₀ K α:Type}[DecidableEq V]{G:Gauge}{n:Side}{N j k:ℕ} {R:Census V}
open Gauges Quipu Quipu.Sonnet Tern
namespace Stack
variable [Fintype J][Nonempty J]
variable {s:Senses R}
-- z.Gauge scope rank.N.Route Temp.Context transmitter choose World mask(s.F.Memory.Body). Support physique.He.Sem.Φ heights.AtURI.Consumer. also useful Omegaℂ by real&imag distinct marker forms. 
noncomputable def mark (b:ℝ)(A: Vase s G N):Vase s G N:= { A with ink:= b • A.ink, legal:=(YM.Stationary.paints G N).smul_mem b A.legal}
namespace Workers
set_option quotPrecheck false
variable (b:ℝ)(A:Vase s G N)(s':Site n) (U:Config G n)
lemma moves : (mark b A).read s' k U=b*A.read s' k U:= by unfold Vase.read Vase.draw; rw [Finset.mul_sum]; refine sum_congr rfl fun i _=>?_; change b*(_)*_=_*(_*_); rw [mul_assoc]; rfl -- maybe done
lemma rooms (a:ℝ): (mark b A).fare a=|b| *A.fare a:= by
 unfold Vase.fare; rw [show Vase.sizeC (mark b A)=|b| *Vase.sizeC A from ?_]; · rw [mul_assoc]; rfl
 unfold Vase.sizeC; simp only [mark,Pi.smul_apply,smul_eq_mul,abs_mul,Finset.mul_sum]
end Workers
set_option quotPrecheck false
noncomputable def linearize (J:Type)[Fintype J][Nonempty J]: ℕ ≃ J×ℕ := (@Denumerable.eqv (J×ℕ) (Classical.choice (nonempty_denumerable (J×ℕ)))).symm
local notation "U"=> linearize J
variable (F:J→Album ℕ s G N)(b:J→ℝ)
noncomputable abbrev batch (i:J×ℕ):Vase s G N:= Stack.mark (b i.1) (F i.1 i.2)
noncomputable abbrev crowd: Album ℕ s G N:= batch F b ∘ linearize J
variable {a:ℝ} {C:J→ℝ}
local notation "β"=> batch F b
local notation "Y"=> crowd F b
local notation "Ω₁"=> ∑ j:J,|b j| * C j
variable (hc:∀ i,(F i).Health a (C i))
include hc
lemma sumC : Album.Health (batch F b) a (∑ j:J,|b j| * C j):= by
 refine budget_rows _ (fun j=> |b j| * C j) ?_ (budget_finite (fun (j:J)=> mul_nonneg (abs_nonneg _) (budget_nonneg (hc j))) le_rfl); intro j; change SumBudget (fun i:ℕ=>Vase.fare (Stack.mark _ (F _ _)) a) _; simp_rw [Workers.rooms]; exact budget_scale (abs_nonneg _) (hc _)
lemma assembled : (crowd F b).Health a (∑ j:J,|b j| * C j):= budget_pull (linearize J) (linearize J).injective (sumC F b hc)
noncomputable abbrev history (g:ℕ→ Prop)(A: Album Ω s G N): Ω→Prop:=fun i=>g (A i).momentum
local notation "T"=> Sonnet.root s
-- preserve known observer.Ar.Shape.Actor.Curtain.We.Visibility true along λ.Packet.We.Root.Clock
variable (g:ℕ→Prop)(w:V→Site n)(x:Config G n)
include hc
lemma tenure (hp:0<a) (k:ℕ) : Album.picture (history g Y) Y w k x=∑ i:J,b i* Album.picture (history g (F i)) (F i) w k x:= by
 let z:=w T; let f(a:J×ℕ):=Album.readout (fun i=>history g β i∧ Bay.Hears (β i|>.stage) w) β z k a x; let H(i:J)(p:ℕ):= Album.readout (fun n:ℕ=>history g (F i) n∧Bay.Hears (F i n|>.stage) w) (F i) z k p x; have he(i:ℕ):f (U i)=Album.readout (fun i=>history g Y i∧Bay.Hears (Y i|>.stage) w) Y z k i x:=rfl
 have hf: Summable f:= Album.global_sum _ _ _ _ _ (sumC F b hc) hp
 have hz(i:J)(k':ℕ):f (i,k')=b i*H i k':=by
    unfold f H Album.readout; split
    next ht=> rw [if_pos (by exact ht)]; exact Workers.moves .. -- definitional
    next ht=> rw [if_neg (by exact ht)]; simp
 change (∑' i,f (linearize J i))=∑ i:J,b i* ∑' p,H i p; rw [Equiv.tsum_eq, Summable.tsum_prod hf, tsum_fintype]; simp_rw [hz,tsum_mul_left] -- defeq he may need

end Stack
end YM.Qlocal.Dialect
