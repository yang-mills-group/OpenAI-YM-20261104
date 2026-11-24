import YM.Integration.ActualTrajectoryTransport
import YM.OPE.Therm.Law
/-! # shared F6 conditioning. Real older k expectation on original action, not independent marginal. Includes conditional proper pairs (with both of their means), conditional cumulant and inherited products. -/
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.Integration.Logwood
open Function Lattice RG Wilson MeasureTheory
open OPE.Therm
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge}{I:Type*} [MeasurableSpace I] {f g:I→ℂ}

lemma intE (F:Envelope f)(μ:Measure I) [IsFiniteMeasure μ] : Integrable f μ:=Integrable.of_bound F.meas.aestronglyMeasurable F.cost.choose (Filter.Eventually.of_forall F.cost.choose_spec)
lemma envP (p:Envelope f)(q:Envelope g):Envelope (f*g):=⟨p.meas.mul q.meas,p.cost.choose*q.cost.choose,fun x=> by rw [Pi.mul_apply,norm_mul]; exact mul_le_mul (p.cost.choose_spec x) (q.cost.choose_spec x) (norm_nonneg _) ( (norm_nonneg _).trans (p.cost.choose_spec x))⟩
lemma envN (p:Envelope f)(q:Envelope g):Envelope (f-g):=⟨p.meas.sub q.meas,p.cost.choose+q.cost.choose,fun x=> (norm_sub_le ..).trans (add_le_add (p.cost.choose_spec x) (q.cost.choose_spec x))⟩
lemma envA (p:Envelope f)(q:Envelope g):Envelope (f+g):=⟨p.meas.add q.meas,p.cost.choose+q.cost.choose,fun x=> (norm_add_le ..).trans (add_le_add (p.cost.choose_spec x) (q.cost.choose_spec x))⟩
-- submodel total decomposition usable for all Ω index spaces
variable {C:Family G}{i j N p:ℕ}
abbrev tally (C:Family G)(N p i:ℕ)(F:Config G (C.side i p)→ℂ):ℂ:= ∫ U,F U∂scene C.path N p i
variable (F:Config G (C.side (i+1) p)→ℂ) (Y:C.Makes)(hi:i<N)(v:Envelope F)
include Y hi v in
lemma vote_lodge : Envelope (actualAverage C (N:=N) F):=by
   let T:= (C.path.levels.clock.op i p); let t:= C.path.β N p (i+1); let d:= (C.path.rep N p (i+1)).eval; let D:= (C.path.rep N p i).eval
   have hQ : T.IsKernel t G:= C.path.levels.transition_mass ..; have hp:= ((C.path.rep N p i).envelope (Y.wilson.represents N p i hi.le).good).meas; have hx:= ((C.path.rep N p (i+1)).envelope (Y.wilson.represents N p (i+1) hi).good).meas
   have hh:Measurable fun V: Config G (C.side i p) × Config G (C.side (i+1) p)=> (actualConditionalDensity C N p i V.1 V.2) • F V.2 := (((hQ.meas.comp measurable_swap).mul (hx.comp measurable_snd)).div (hp.comp measurable_fst)).smul (v.meas.comp measurable_snd)
   exact ⟨hh.stronglyMeasurable.integral_prod_right'.measurable, v.cost.choose, actualAverage_norm_le C Y hi v.cost.choose_spec⟩
include Y hi v in
lemma lodge_mass : tally C N p (i+1) F=tally C N p i (actualAverage C (N:=N) F):=by
    unfold tally; rw [violet Y.wilson hi, violet Y.wilson hi.le]; apply congr_arg (· / _); simp_rw [←Complex.real_smul]; have h:= actualTransport_mass (N:=N) (I:=F) C Y hi v.meas.aestronglyMeasurable v.cost.choose_spec i.le_succ; rw [actualTransport_step C Y hi F i.lt_succ_self, actualTransport_base C Y hi F] at h; exact h.symm
section
variable {μ:Measure I}[IsFiniteMeasure μ]
abbrev Slate (μ:Measure I)(A:I→ℂ):= ∫ x,A x∂μ
abbrev Cov (μ:Measure I)(A B:I→ℂ):ℂ:= Slate μ (A*B)- Slate μ A * Slate μ B
open Finset
def tri (U A B C x y z:ℂ):= U-A*z-B*y-C*x+x*y*z+x*y*z
abbrev Cumu (R:(I→ℂ)→ℂ)(A B C:I→ℂ) := tri (R (A*B*C)) (R (A*B)) (R (A*C)) (R (B*C)) (R A) (R B) (R C)
structure Mood {U:Type*}[MeasurableSpace U](ν:Measure U)(μ:Measure I)(M:(U→ℂ)→ I→ℂ): Prop where
    around : ∀ f,Envelope f→ Envelope (M f)
    salary : ∀ f,Envelope f→ Slate μ (M f)= Slate ν f
    unit : ∀ z:ℂ,M (fun _=> z)=fun _=>z
variable {U:Type*}[MeasurableSpace U]{ν:Measure U}(M:(U→ℂ)→ I→ℂ)(pay:Mood ν μ M)(A B D:U→ℂ)
include pay in
lemma conditional (a:Envelope A)(b:Envelope B)(c:Envelope D):
    let Q:= fun F H=> M (F*H)-M F*M H
    Cumu (Slate ν) A B D=
    Slate μ (fun i=> Cumu (fun f=>M f i) A B D)+ Cov μ (Q A B) (M D)+ Cov μ (Q A D) (M B)+ Cov μ (Q B D) (M A) + Cumu (Slate μ) (M A) (M B) (M D):=by
    intro Q; unfold Cumu Cov tri; rw [←pay.salary _ (envP (envP a b) c),←pay.salary _ (envP a b),←pay.salary _ (envP a c),←pay.salary _ (envP b c), ←pay.salary _ a,←pay.salary _ b,←pay.salary _ c]
    let e1:= M A; let e2:= M B; let e3:= M D; let R:= e1*e2*e3; let a1:=M (A*B); let a2:= M (A*D); let a3:=M (B*D); let T:= M (A*B*D)
    have hR11:Envelope e1:= pay.around _ a; have hR12:Envelope e2:= pay.around _ b; have hR13:Envelope e3:= pay.around _ c
    have h1:= pay.around _ (envP a b); have h2:= pay.around _ (envP a c); have h3:= pay.around _ (envP b c); let t1:=a1*e3; let t2:=a2*e2; let t3:=a3*e1
    have hR : Envelope R:= envP (envP hR11 hR12) hR13; have ht: Envelope T:= pay.around _ (envP (envP a b) c); have ht1:Envelope t1:=envP h1 hR13; have ht2: Envelope t2:= envP h2 hR12; have ht3:Envelope t3:= envP h3 hR11
    let F:=Slate μ; let K:=T-t1-t2-t3; have s (A B:I→ℂ)(a:Envelope A)(b:Envelope B): F (A-B)= F A-F B:= integral_sub (intE a μ) (intE b μ); have x (A B:I→ℂ)(a:Envelope A)(b:Envelope B): F (A+B)= F A+ F B:= integral_add (intE a μ) (intE b μ)
    have he:Envelope K:=envN (envN (envN ht ht1) ht2) ht3
    change _=F (K+R+R)+(F ((a1-e1*e2)*e3) - F (a1-e1*e2)*F e3)+(F ((a2-e1*e3)*e2)- F (a2-e1*e3)*F e2)+(F ((a3-e2*e3)*e1)-F (a3-e2*e3)*F e1)+(F R- F (e1*e2)*F e3 - F (e1*e3)*F e2- F (e2*e3)*F e1+ F e1*F e2*F e3+ F e1*F e2*F e3)
    rw [ show (a1- _)*e3=t1-R from sub_mul .., show (a2-e1*e3)*e2=t2-R from by unfold t2 R; ring, show (a3-e2*e3)*e1=t3-R from by unfold t3 R; ring, s _ _ h1 (envP hR11 hR12), s _ _ h2 (envP hR11 hR13), s _ _ h3 (envP hR12 hR13), x _ _ (envA he hR) hR,x _ _ he hR,s _ _ ht1 hR,s _ _ ht2 hR,s _ _ ht3 hR,show K= T-t1-t2-t3 from rfl,s _ _ (envN (envN ht ht1) ht2) ht3, s _ _ (envN ht ht1) ht2,s _ _ ht ht1]; change F T-F a1*F e3-F a2*F e2-F a3*F e1+F e1*F e2*F e3+F e1*F e2*F e3=_; ring
end
include Y hi in
lemma older : Mood (scene C.path N p (i+1)) (scene C.path N p i) (actualAverage C (N:=N)):= ⟨fun T v=>vote_lodge T Y hi v,fun f v=>(lodge_mass f Y hi v).symm,fun z=>funext fun V=>actualAverage_const C Y hi z V⟩
end YM.Integration.Logwood
