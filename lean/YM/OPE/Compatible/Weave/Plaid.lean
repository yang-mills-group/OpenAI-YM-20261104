import YM.OPE.Compatible.Blaze.Lions
/-! # Page reflection. CL on solar -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix Tree
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir Stationary
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Pilot Woody Virgin Work.F08 Flume.Page
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
open YM.AnalyticNext.QuarticMatch.Joint
variable {n c f:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I J:Type} (a:Axis)
local notation "Z"=> Wm a
abbrev φ (p:Axis):ℝ:=if p=a then -1 else 1
lemma φ_zt (p:Site n): dart a (dart a p)=p:= (Wm a).act_inv _
lemma φ_step (v:Axis): dart a (step v:Site n)=if v=a then -(step v:Site n) else step v:=by simpa [dart] using norm_step a v (0:Site n)
lemma same_charge (p q:Site n): Pert.Full.char (dart a p) (dart a q)= Pert.Full.char p q:=by
      unfold Pert.Full.char Pert.Full.dot; unfold dart; simp_rw [run_axis]; apply congr_arg; apply congr_arg; funext i; split <;> simp
lemma same_Δ (p:Site n) : Pert.Full.delta (Pert.Full.moment (dart a p))=Pert.Full.delta (Pert.Full.moment p):=by
      have hp:= Pert.Full.char_lap p 0; have ht:= Pert.Full.char_lap (dart a p) 0; simp_rw [Pert.Full.char_zero, one_mul,zero_add,zero_sub] at hp ht; apply neg_injective; apply Complex.ofReal_injective; rw [← hp,← ht]; apply Finset.sum_congr rfl; intro i _
      have hh:=same_charge a p (step i); have hv:= same_charge a p (-(step i)); have hz:dart a (-(step i:Site n))= -dart a (step i):= Signed.act_neg ..; rw [hz, φ_step] at hv; rw [φ_step] at hh; by_cases he:i=a
      · rw [if_pos he] at hh hv; rw [hh]; rw [neg_neg] at hv; rw [hv,add_comm (Pert.Full.char p (step i))]
      rw [if_neg he] at hv hh; rw [hh,hv]
lemma field_sym (v:Site n): mildX [] (dart a v)=mildX [] v:=by
     simp_rw [mild_tip, toroid]; apply congr_arg; let E:=Equiv.mk (dart a (N:=n)) (dart a) (φ_zt a) (φ_zt a)
     rw [← Equiv.sum_comp E (g:= fun i=> topWeight n i* Pert.Full.char i (dart a v))]; apply Finset.sum_congr rfl; intro i _; rw [show E i=dart a i from rfl,same_charge,topWeight,same_Δ];rfl --];
open Prairies
local notation "I!"=> Ice G n
abbrev Frost (b:Site n × Shade G) : Site n ×Shade G:= ((Wm a).act b.1+dust a b.2.1,b.2)
lemma F_form (M: KernelChoices)(h:4≤r)(x y: Site n×Shade G):
     Cot M G (Train.top r) n x y= φ a x.2.1 * φ a y.2.1 * Cot M G (Train.top r) n (Frost a x) (Frost a y) :=by
     obtain ⟨x,i,c⟩:=x; obtain ⟨y,j,d⟩:=y; have hp(v t:Site n)(i j:Axis) (a b:G.ColorIndex): Cot M G (Train.top r) n (v,i,a) (t,j,b) = if a=b then if i=j then mildX [] (v-t) else 0 else 0:=by change (if a=b then lineC _ _ (v, Exterior.coord i) (t,Exterior.coord j) else 0)=_; simp_rw [strip_field (C:=M) h]; simp only [Exterior.coord_iff]
     rw [hp]; change _= φ a i * φ a j* Cot M G (Train.top r) n ((Wm a).act x+dust a i,i,c) ((Wm a).act y+dust a j,j,d); rw [hp];
     all_goals split_ifs with he ht
     all_goals first|subst j;rw [add_sub_add_right_eq_sub,←Signed.act_sub, show mildX _ _= _ from (show mildX [] (dart a (x-y))= _ from field_sym a _)]; unfold φ; split_ifs<;>ring|ring
lemma F_ζζ (x:Site n× Shade G): Frost a (Frost a x)=x:=Prod.ext (offsets a _ _) rfl
noncomputable def flo : I!→L[ℝ] I!:= ContinuousLinearMap.pi fun i=>φ a i.2.1 • ContinuousLinearMap.proj (Frost a i)
lemma F_leg (x:I!)(i z b):flo a x (i,z,b)= φ a z*x ((Wm a).act i+dust a z,z,b):=rfl
lemma F_legB (x:Bid.Dir G n): spool G n (streak a G n x)=flo a (spool G n x):=by
   funext i; obtain ⟨i,z,b⟩:=i; rw [F_leg]; change streak a _ _ x (i,Exterior.coord z) b= _; simp_rw [α_line]; unfold φ; split <;> simp only [neg_one_mul, PiLp.neg_apply,one_mul] <;>rfl
lemma score_flo (A B:Module.Dual ℝ I!)(M:KernelChoices)(h:4≤r): ProbeCov (Cot M G (Train.top r) n) (A ∘ₗ (flo a).toLinearMap) (B ∘ₗ (flo a).toLinearMap)=ProbeCov (Cot M G (Train.top r) n) A B:=by
     letI dI : DecidableEq (Tab (Shade G) n):=Classical.decEq _ -- may harm!
     let E: Equiv.Perm (Site n×Shade G):=⟨Frost a,Frost a,F_ζζ a,F_ζζ a⟩; let Q:= Cot M G (Train.top r) n; unfold ProbeCov; let f(i j):= Q i j * ((A ∘ₗ (flo a).toLinearMap) (Pi.single i 1)) * ((B ∘ₗ (flo a).toLinearMap) (Pi.single j 1))
     change (∑ i,∑ j,f i j)= _; rw [← Equiv.sum_comp E (g:=fun i=>∑ j,f i j)]; simp_rw [← Equiv.sum_comp E (g:=fun j=> f _ j)] -- ambiguity
     have hh(i):flo a (Pi.single (E i) (1:ℝ))=φ a i.2.1 • Pi.single i (1:ℝ):=by
         funext j; by_cases hp:j=i; subst j; change φ a i.2.1*(Pi.single (E i) (M:=fun _=>ℝ) 1 (E i))= _; simp
         change _*Pi.single (M:=fun _=>ℝ) (E i) _ (E j)= _ *Pi.single (M:=fun _=>ℝ) i _ j; rw [Pi.single_eq_of_ne hp, Pi.single_eq_of_ne (E.injective.ne hp),mul_zero,mul_zero]
     apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; unfold f; rw [show Cot M G (Train.top r) n i j=_ from F_form a M h i j]; change Q (E i) (E j)* A (flo a (Pi.single (E i) 1))*B (flo a (Pi.single (E j) 1))=φ a i.2.1* φ a j.2.1*Q (E i) (E j)*A (Pi.single i 1)*B (Pi.single j 1); erw [hh i,hh j,map_smul,map_smul]; ring
end YM.OPE.Quit
