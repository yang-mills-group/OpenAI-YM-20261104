import YM.MS.City.Mood
/-!
# hypercubic group spectral action

Orientation on net needed for classification; not assumed even from period
 sym. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.City
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color Detect
open Complex (I)
open scoped Topology ContDiff Pointwise
variable {G:Gauge} (s:Signed) (p:QP)(a b:Axis)
-- measurable equivs.
private lemma atm (s:Signed) : Continuous (s.act:QP→QP):= by unfold Signed.act; apply continuous_pi; intro i; cases hv:s.flip (s.perm.symm i) <;> simp <;> fun_prop
def seat (s:Signed): QP≃ᵐ QP := {
 s.actEquiv.toEquiv with
   measurable_toFun:= (atm s).measurable
   measurable_invFun:= (atm s⁻¹).measurable }
private instance : Measure.IsNegInvariant cap:= by
   rw [cap, show Set.Icc (-π) π= Metric.closedBall (0:ℝ) π from by ext; simp [abs_le] ] -- double bracket lint
   let Y := Metric.closedBall (0:ℝ) π; let N: ℝ≃ᵐ ℝ:=(Homeomorph.neg ℝ).toMeasurableEquiv; constructor
   show Measure.map N ((volume:Measure ℝ).restrict Y)= _
   nth_rw 1 [show Y= N ⁻¹' Y from by ext; simp [N,Y,Metric.mem_closedBall]]; rw [← N.measurableEmbedding.restrict_map]; exact congr_arg (fun μ:Measure ℝ=>μ.restrict Y) (Measure.measurePreserving_neg (volume:Measure ℝ)).map_eq
lemma measureVeh : MeasurePreserving (seat s) μzone μzone:= by
   rw [μview];
   let f (i:Axis)(p:ℝ):ℝ:= if s.flip i then -p else p; let N := MeasurableEquiv.piCongrLeft (fun _:Axis=>ℝ) s.perm
   have he : MeasurePreserving N vol vol:= measurePreserving_piCongrLeft (fun _: Axis=> cap) s.perm
   have hf i: MeasurePreserving (f i) cap cap:= by
       unfold f; cases h:s.flip i; · convert MeasurePreserving.id cap using 1; simp [Function.id_def]
       convert Measure.measurePreserving_neg cap using 1; simp
   have hs : MeasurePreserving (seat s) vol vol:= by
       convert he.comp (measurePreserving_pi (fun _:Axis=>cap) (fun _:Axis=>cap) hf) using 1; funext x; ext i; obtain ⟨i,rfl⟩:=s.perm.surjective i; simp [seat,N, Signed.actEquiv,f, MeasurableEquiv.coe_piCongrLeft];
       rfl
   exact hs.smul_measure _

-- pullback line and vertex. sign weights include color orientation.
def passN (s:Signed): BH G ≃ BH G := (Equiv.prodCongr (Equiv.prodCongr (Equiv.optionCongr s.perm) (Equiv.refl _)) (Equiv.refl _))
abbrev tick (s:Signed)(a:BH G):ℂ := negateField s (a,0)
lemma passenger (a:BH G): permute s (a,p)=(passN s a,s.act p):= by rcases a with ⟨⟨_|a,_|_⟩,c⟩ <;> rfl
lemma wTurn : wave (s.act p)=s.act (wave p):= by
    ext i; obtain ⟨i,rfl⟩:= s.perm.surjective i; simp only [wave,Function.comp_apply,Signed.act_at]; cases hv:s.flip i <;> simp [theta]
lemma wSeat : Momentum.sq (s.act p)=Momentum.sq p:= by unfold Momentum.sq; rw [← Equiv.sum_comp s.perm]; apply Finset.sum_congr rfl; intro i _; cases hv:s.flip i <;> simp [hv]
lemma spin_P : precision (s.perm a) (s.perm b) (s.act p)= cross (s.flip a) true*cross (s.flip b) true*precision a b p:= by unfold precision; rw [wSeat]; by_cases he:a=b <;> (cases hk:s.flip a <;> cases hv:s.flip b <;> simp_all [delta])
lemma tick1 (a:BH G)(p:QP): negateField s (a,p) = tick s a:= rfl
lemma tick2 (a:BH G): tick s a * tick s a=1:= by rcases a with ⟨⟨_|i,t⟩,j⟩ <;> first| exact one_mul _| exact cross_cross ..
lemma turn_p (t:ℝ)(i j:BH G) : Cpu G t (passN s i) (passN s j) (s.act p) = tick s i*tick s j*Cpu G t i j p:= by
    let X := fun k:BH G=> k.2; have hx (i:BH G) : X (passN s i)=i.2:=rfl
    unfold Cpu LegsK Landau.choir; by_cases hh:i.2=j.2; swap; · simp only [hh,show (passN s i).2≠(passN s j).2 from hh,↓reduceIte,mul_zero]
    simp only [show (passN s i).2=(passN s j).2 from hh,if_pos hh]; -- inspect
    rw [wTurn]; rcases i with ⟨⟨_|i,_|_⟩,t'⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,v⟩ <;> first| (solve| simp [passN,L0]) | skip
    all_goals simp [L0,spin_P,brush,wSeat,tick,negateField,passN];
    · cases s.flip j <;> simp
    · cases s.flip i <;> cases s.flip j <;> simp
    cases s.flip i <;> simp
end YM.MS.City
