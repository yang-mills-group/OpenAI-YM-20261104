import YM.MSbar.Counter.Scale
/-! Exact pole is local, independent of scale, and insufficient
from any isolated exponent slice; use coherence under confluent exponential factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Counter
open Dim Symbol Domain Diagram Super Scale Scale.Inertia Function Set Filter Complex Crest
open scoped Classical Topology BigOperators
variable {C:Type}{W:Edition C}{d: Bit}{m j k i n:ℕ}{U:Set ℂ}{A: Mass C} {M: SizeLaw C}{z:ℂ}
variable {V:Finset ℕ}{F G H:ℕ→Functionals C}

-- true derivatives cost layer table and Collect across finite spectrum
-- distinguish internal integrations and homogeneity from ℏ total
def heat (M:SizeLaw C)(F:ℕ→Functionals C) : ℕ → Functionals C:= fun v z=> Scale.tick (Scale.mass M v z) (F v z)
def scan (i:ℕ) (V:Finset ℕ) (F:ℕ→Functionals C) := ∑ v∈V, times (step v i) (F v)
@[simp] lemma scan_zero (s:Finset ℕ)(F:ℕ→Functionals C): scan 0 s F=∑ v∈s,F v:= by unfold scan; apply Finset.sum_congr rfl; intro i _; ext1 z; simp [times,step]
-- An analytic sum even after differentiating wrt log scale on dilated arguments
abbrev Coherent (U:Set ℂ)(W:Edition C)(d:Bit)(V: Finset ℕ)(F:ℕ→Functionals C):Prop:= ∀ i,Regular U W d (scan i V F)

variable (h:∀ v∈V, Price k U W d (F v))
namespace Coherent
lemma ticker {ι:Type*}{Y:ι→Vertex C}(B:Finset ι) (h:∀ i ∈ B, Live W d (Y i)): Scale.tick A (∑ i∈B,Y i)= ∑ i∈B, Scale.tick A (Y i):=by
    induction B using Finset.induction_on with
    | empty=> simp
    | insert i s he ih=>
       have hh (i':ι) (hx:i'∈s):= h i' (Finset.mem_insert_of_mem hx)
       rw [Finset.sum_insert he, Finset.sum_insert he,tick_add (h i (Finset.mem_insert_self ..)) (Live.sum s hh), ih hh]
lemma near {X Y:Functionals C} (hX:∀ z,Live W d (X z))(hY:∀ z,Live W d (Y z))
    (he: jam A X+Y=0) (hy: jam A Y=0): Y=0:=by
    funext z; apply hollow (A:=A) (hY z) (congr_fun hy z)
    have hh :=congr_fun he z; simp only [Pi.add_apply,jam,← eq_neg_iff_add_eq_zero, Pi.zero_apply] at hh
    rw [show Y z= Scale.tick A ((-1:ℂ) • X z) from (by rw [tick_scale (hX z),hh]; simp)]; exact projects (Live.scale _ (hX z))
variable [Profit U]
include h
lemma harmony : Price k U W d (scan i V F) := Price.sum V fun v hv=> every _ _ (h v hv)
lemma rise (i:ℕ)(h0:Regular U W d (scan i V (heat M F))): jam (Scale.mass M 0 0) (principal W d U (scan i V F))+ principal W d U (scan (i+1) V F)= 0 := by
   let A:=Scale.mass M 0 (0:ℂ); let x:=scan i V F; let y:=scan (i+1) V F
   have H:EqOn (scan i V (heat M F)) (jam A x+y) (rim U):=by
      intro z hz; dsimp only [scan,x,y,jam]; simp only [Finset.sum_apply,Pi.add_apply,jam,times,heat]; rw [ticker V (W:=W) (d:=d) ?_, ← Finset.sum_add_distrib]; swap
      · exact fun v hv=> Live.scale _ ((h v hv).alive hz)
      apply Finset.sum_congr rfl; intro v hv
      have hf:= (h v hv).alive hz; change step v i z • _=Scale.tick A (step v i z • _) + step v (i+1) z • _; rw [tick_scale hf,lift_equal (M:=M) hf]; simp only [step,A,smul_smul,smul_add,pow_succ] -- order?
   change jam A _+_=0; rw [← extraction (harmony h), ← Price.combine (keeps (harmony h)) (harmony h)]; change principal W d U (jam A x+y)=0; exact is_principal (show Regular U W d ((jam A x+y)-0) by rw [sub_zero]; exact Price.recognize h0 (fun x hx=>Eq.symm (H hx))) (Winter.empty_free 0)
variable (hH:Coherent U W d V (heat M F))
include hH
lemma higher (i:ℕ): Regular U W d (scan (i+1) V F) := by
    let S(k):=scan k V F; let k':=k
    have hx (t:ℕ): ∀ j≥ k-t, Regular U W d (S (j+1)):=by -- assumption artificial remove
        induction t with
        | zero=>intro j hj; exact Price.sum V (fun v hv=> Crest.after (h v hv) (i:=k) (j:=j+1) (by omega))
        | succ t ih=>
           intro j hj; let z(j:ℕ):=principal W d U (S j); let A:=Scale.mass M 0 (0:ℂ)
           have a : Regular U W d (S (j+1+1)):= ih (j+1) (by omega)
           have hb:z (j+1+1)=0:= (Price.criterion (harmony h)).mpr a
           have hJ: jam A (z (j+1))=0:=by have hh:jam A (z (j+1))+ z (j+1+1)=0:= rise h (j+1) (hH _); rwa [hb,add_zero] at hh
           exact (Price.criterion (harmony h)).mp (near (fun t=> (harmony (i:=j) h).pair.1.live t) (fun t=> (harmony (i:=j+1) h).pair.1.live t) (rise h j (hH j)) hJ)
    exact hx k i (by omega)
lemma eigen : jam (Scale.mass M 0 0) (principal W d U (scan 0 V F))=0:=by have hh:=rise h 0 (hH 0); rwa [(Price.criterion (harmony h)).mpr (higher h hH 0),add_zero] at hh
end Coherent

def clean (U:Set ℂ)(W:Edition C)(d:Bit)(V:Finset ℕ)(F:ℕ→Functionals C)(i:ℕ): Functionals C:= if i=0 then F i-principal W d U (scan 0 V F) else F i
namespace Coherent
variable [Profit U](hH: Coherent U W d V (heat M F))
include h hH
lemma cleans (hv:0∈ V): Coherent U W d V (clean U W d V F):= by
   intro i; rcases i with _|i
   · rw [scan_zero]; have hh : ∑ v∈V,clean U W d V F v= scan 0 V F-principal W d U (scan 0 V F):=by
            nth_rw 1 [scan_zero]; rw [← Finset.add_sum_erase _ _ hv,← Finset.add_sum_erase (f:=F) _ hv,clean,if_pos rfl]
            rw [show ∑ x∈V.erase 0, clean U W d V F x= ∑ x∈V.erase 0,F x from Finset.sum_congr rfl fun _ hx=> if_neg (Finset.mem_erase.mp hx).1]; abel
     rw [hh]; exact (harmony h).pair.2
   rw [show scan (i+1) V (clean U W d V F)=scan (i+1) V F from ?_]; exact higher h hH _
   apply Finset.sum_congr rfl; intro v hv; ext1 z; unfold times clean; split_ifs with h; subst v; simp [step]; rfl
lemma mode (j:ℕ) (hj:j∈V): Price k U W d (clean U W d V F j):=by unfold clean; split_ifs with he; exact (h j hj).sub (harmony h).pair.1.bound;exact h j hj
lemma flows : ∀ v∈V, EqOn (heat M (clean U W d V F) v) (heat M F v) (rim U) := by
    intro v hv z hz; unfold heat clean; split_ifs with he; swap; rfl
    subst v; have hc:= congr_fun (eigen h hH) z; simp only [jam,no_add,Pi.zero_apply] at hc
    simp only [no_add,Pi.sub_apply,sub_eq_add_neg]; rw [← neg_one_smul ℂ (principal W d U (scan 0 V F) z),tick_add ((h 0 hv).alive hz) (Live.scale _ ((harmony h).pair.1.live z)), tick_scale ((harmony h).pair.1.live z),hc];simp
end Coherent
end YM.MSbar.Counter
