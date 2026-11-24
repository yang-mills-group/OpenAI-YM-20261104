import YM.OPE.Compatible.Cum.Pinto
/-!
# script heat report.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix
variable {I J E:Type}{N:Side} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] {μ:Measure E}[μ.IsAddHaarMeasure]{L:Law E} [Fintype I]
local notation "Q!"=> deck I N
local notation "K!"=> Flume.Script.Tab I N
variable [DecidableEq J] {s:Finset J}{v w:J→ℕ}{Q:∀ i:J,Script I (w i+v i)}{X:J→Option (Site N)} {ρ:J→Bool} {a b:Site N}{c y:ℝ}{Z:E→L[ℝ] deck I N}{Ω:Row I I}{C:ℕ→ℝ}{p e k d t n m:ℕ}{F H: Curtain I}
-- State values finite pencils
omit [DecidableEq J] in
abbrev Bins (F:Curtain I):Prop:=∀ i,Summable (F i)
omit [Fintype I][DecidableEq J] in
lemma Bins.falls (f:J→Curtain I)(h:∀ i∈s,Bins (f i)): Bins (∑ i∈s,f i):=by intro i; rw [Finset.sum_apply,show (∑ j∈s,f j i)=fun b=>∑ j∈s,f j i b from funext fun b=> Finset.sum_apply ..]; exact summable_sum fun j hj=>h j hj i
omit [Fintype I][DecidableEq J] in
lemma Bins.along (h:Bins F)(hp:Bins H): Bins (F+H):= fun i=> (h i).add (hp i)
omit [Fintype I][DecidableEq J] in
lemma binZ : Bins (0:Curtain I):= fun _=> summable_zero
omit [Fintype I] in
lemma Hall_bins (η K:ℝ)(hp:Ω.strip η K)(hs:0<η)(hd:0≤K){c:J→ℝ}(he: coversB v w Q m c s)(R:Script I (e+d))(hx: soot m R y):Bins (Shell.Hall Ω v w Q ρ s d e R):=by
     obtain ⟨a,h,H⟩:= payrollX (I:=I) (s:=s) (v:=v) (w:=w) (d:=d) (e:=e) (m:=m) hs hd; exact fun i=>sootS (H Ω hp ρ Q c he R y hx i)
def Flair (F:Curtain I)(K:ℕ)(x:deck I N)(z:Site N):ℝ:= ∑ i∈range (K+1),Flume.Script.value z (F i) x
omit [Fintype I] in lemma flair0 (K:ℕ)(x:deck I N)(z:Site N): Flair 0 K x z=0:=by apply Finset.sum_eq_zero; intro i _; simp only [Flume.Script.value,scribe,Pi.zero_apply, zero_mul,tsum_zero]
omit [DecidableEq J] in lemma flairA (K:ℕ)(x:deck I N)(z:Site N)(ha:Bins F)(hv:Bins H): Flair (F+H) K x z=Flair F K x z+Flair H K x z:=by
     unfold Flair; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold Flume.Script.value scribe; simp_rw [Pi.add_apply,add_mul]; exact (instruments _ (ha _) ..).summable.tsum_add (instruments _ (hv _) ..).summable
lemma flairS (K:ℕ)(x:deck I N)(z:Site N)(R:J→Curtain I)(hs:∀ i∈s,Bins (R i)): Flair (∑ i∈s,R i) K x z=∑ i∈s, Flair (R i) K x z:=by
     induction s using Finset.induction_on with
     | empty=>rw [Finset.sum_empty,Finset.sum_empty,flair0]
     | insert i s hi ih=> simp only [Finset.sum_insert hi]; rw [flairA _ _ _ (hs _ (mem_insert_self ..)) (Bins.falls _ fun j hj=>hs j (mem_insert_of_mem hj)),ih fun i hi=> hs _ (mem_insert_of_mem hi)]
omit [Fintype I] in
lemma throw_flair (x:deck I N)(h:e ≤ k)(P:Script I e)(v:Site N): Flair (Shell.throw P) k x v=Script.value v P x:=by unfold Flair; rw [sum_eq_single e]; rw [show Shell.throw P e=P from Pi.single_eq_same _ _]; intro i _ hi; simp [hubbub hi,Script.value,scribe]; intro he; exact False.elim (he (mem_range.mpr (by omega)))
-- payer estimate property
structure Buds (Ω:Row I I)(L:Law E)(x:deck I N)(C:ℕ→ℝ)(Z:E→L[ℝ] deck I N)(Q:∀ i:J,Script I (w i+v i))(i:Site N)(s:Finset J) (t: J→ Option (Site N))(m:ℕ)(c:ℝ) : Prop where
   amp : ‖c‖≤ 1
   fee : Fund m i Ω L C Z
   alpha l (h:l∈s): Globe (w l+v l) (t l) x (Q l) Ω L C Z i c m
omit [MeasurableSpace E][BorelSpace E][DecidableEq J] in
lemma Buds.nat (x:Q!)(hp:Buds Ω L x C Z (w:=w) (v:=v) Q a s X m c) {t:Finset J} (h:t⊆s):Buds Ω L x C Z (w:=w) (v:=v) Q a t X m c:=⟨hp.amp,hp.fee,fun _ H=> hp.alpha _ (h H)⟩
-- Θ Bill with pol weight cota. k chooses extra stamp
-- Finite compare
abbrev Mold (A B:ℝ)(w:ℝ)(N: Side)(m:ℕ):Prop:= grain N m * ‖A-B‖≤ w
def Scripture (v w:J→ℕ)(Ω:Row I I)(Q:∀ i:J,Script I (w i+v i))(p: Script I (e+d))(μ:Measure E)(L:Law E)(x:deck I N)(Z:E→L[ℝ] deck I N)(X:J→Option (Site N))(a:Site N)(c:ℝ)(s:Finset J)(t alpha:ℕ)(b:ℝ): Prop:=
    Mold (Tap μ L (Fig v w Q X c x Z) (SX x x Z (orchestra p a) (d:=d) (e:=e)) s) (Flair (Shell.Hall Ω v w Q (LightX ∘ X) s d e p) t x a) (b * (1+‖x‖)^(Rollup v w s d e)) N alpha
end YM.OPE.Libra.Shell
