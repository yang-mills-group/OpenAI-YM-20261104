import YM.SchemeRG11.Outer.Purl
/-! Orthogonal masks at mesh N. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Patho
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long Air North Wolt Sew Dock MvPolynomial Bark Bare
open scoped Classical Pointwise ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {m n:ℕ}{N:Side}
lemma char_r (s:Signed)(p x:Site N): Full.char (s.act p) (s.act x)=Full.char p x:=by
 unfold Full.char Full.dot; congr 1; exact (Fintype.sum_equiv s.perm _ _ (fun i=>by rw [Signed.act_at,Signed.act_at]; split<;>simp)).symm
lemma delta_r (s:Signed)(p:Site N):delta (moment (s.act p)) = delta (moment p):=by
 have e(x:Site N): (∑ i, (Full.char x (0+step i)+char x (0-step i)- 2 • (char x 0)))=Complex.ofReal (-delta (moment x)):=by simpa only [Full.char_zero,one_mul] using Full.char_lap x 0
 have hz(i:Axis): let M:=Full.char p (step i)+Full.char p (-step i); let q:=s.act p; M= char q (step (s.perm i))+char q (-step (s.perm i)):=by
   dsimp; have he:= Lattice.Step.vec_rotate (d:=posDir i) (R:=Per N) s; rw [Step.vec_pos] at he; conv_lhs=>rw [←char_r s p (step i),←char_r s p (-step i)]; rw [s.act_neg]; rw [←he]
   unfold posDir Lattice.Step.rotate Step.vec; cases hh:s.flip i<;> simp [add_comm]
 apply neg_injective; apply Complex.ofReal_injective; rw [←e,←e]; exact Eq.symm (Fintype.sum_equiv s.perm _ _ (fun i=>by simp only [zero_add, zero_sub, Full.char_zero]; rw [hz]))
lemma toroid_p (s:Signed)(p:Site N):Full.toroid (s.act p)=Full.toroid p:=by
 let E:Equiv.Perm (Site N):={toFun:=s.act,invFun:=s⁻¹.act,left_inv:=fun x=>s.inv_act x,right_inv:=fun x=>s.act_inv x}
 refine (Fintype.sum_equiv E _ _ ?_).symm; intro i; unfold topWeight; change _ = _ * char (s.act i) _; rw [char_r,show E i=s.act i from rfl,delta_r] -- check
lemma aura (s: Signed)(p:Cover): Cellular.coverLine (s.act p) = Cellular.coverLine p:=by
 let T:= Align.itinerary (2:Side) (by decide)
 have h(y: Cover): Tendsto (fun i=> thread (wrap (T.period i) y)) atTop (𝓝 (Cellular.coverLine y)) :=by simpa using (shrink (Medium.constant T y)).naked.add (tendsto_const_nhds (x:=Cellular.coverLine y))
 refine tendsto_nhds_unique (h _) ((h p).congr (fun i=>?_))
 rw [←wrap_signed,thread, thread,toroid_p]
variable {A:Type*}[AddCommGroup A][One A]
def homeE(s:Signed)(p:Code G A): Code G A:= let t:=((posDir p.1.2).rotate s); (t.used (s.act p.1.1),p.2)
def scent(s:Signed)(p:Code G A): Stem (Code G A) ℝ:= let t:=((posDir p.1.2).rotate s); (if t.neg then -(1:ℝ) else 1) • Finsupp.single (homeE s p) 1
lemma scent_p(s:Signed)(p:Code G A)(c:trunk G A): sense (cant c) (scent s p)=cant (wideLink G s c) p:=by simp only [scent,homeE,cant, map_smul, wideLink_apply,PiLp.smul_apply,sense,Finsupp.linearCombination_single,one_smul]
def ray(s:Signed)(x:Four A)(i:Axis):Four A:=if s.flip i then s.act x-step (s.perm i) else s.act x
lemma sway(s:Signed)(x y:Code G A)(D:Dose (Code G A) ℝ):
 (D.pull (scent s)).pulse x y= (Push.FiniteDetection.Free.Hyper.flip s x.1.2)*(Push.FiniteDetection.Free.Hyper.flip s y.1.2)*D.pulse ((ray s x.1.1 x.1.2,s.perm x.1.2),x.2) ((ray s y.1.1 y.1.2,s.perm y.1.2),y.2):=by
 have he(k:Code G A):scent s k=_ :=(show _= (Push.FiniteDetection.Free.Hyper.flip s k.1.2) • Finsupp.single ((ray s k.1.1 k.1.2,s.perm k.1.2),k.2) 1 from by cases h:s.flip k.1.2<;>simp [scent,homeE, Lattice.Step.rotate,Step.used,Push.FiniteDetection.Free.Hyper.flip,ray,posDir,h])
 change D.bed _ _=_; rw [he,he,Dose.bed,map_smul,map_smul,sense,Finsupp.linearCombination_single,one_smul,D.single_wind,Pi.smul_apply,smul_eq_mul,smul_eq_mul]; ring
lemma backer(s:Signed):(Atoll.land G).pull (scent s)=Atoll.land G:=by
 apply Dose.strict; rintro ⟨⟨x,i⟩,a⟩ ⟨⟨y,j⟩,b⟩; rw [sway]; unfold Atoll.land; by_cases h:i=j
 · subst j; dsimp only; rw [Push.FiniteDetection.Free.Hyper.flip_sq]; simp only [one_mul, and_true]
   by_cases e:s.flip i; all_goals simp [ray,e,← Signed.act_sub,aura]
 dsimp only; simp [h]
lemma light(s:Signed):(spray G N).pull (scent s)=spray G N:=by
 apply Dose.strict; rintro ⟨⟨x,i⟩,a⟩ ⟨⟨y,j⟩,b⟩; rw [sway,spray_eq,spray_eq]; dsimp only; by_cases h:i=j
 · subst j; rw [Push.FiniteDetection.Free.Hyper.flip_sq]; simp only [one_mul,and_true]
   have he: ray s y i-ray s x i=s.act (y-x):=by unfold ray; split<;>simp
   have hw : ray s y i+ray s x i+step (s.perm i)=s.act (y+x+ step i):=by
     have hh:= Lattice.Step.vec_rotate (R:=Per N) (d:=posDir i) s; rw [Step.vec_pos] at hh
     rw [Signed.act_add,Signed.act_add,←hh]; cases hi:s.flip i<;> simp [Lattice.Step.rotate, Step.vec, ray, hi,posDir]; abel -- order
   rw [he,hw]; unfold thread; rw [toroid_p,toroid_p]
 simp [h]
end YM.SchemeRG11.Patho
