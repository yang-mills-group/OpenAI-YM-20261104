import YangMills.WilsonProof.NativeSupport.YM.MS.Alps.Easy
/-!
# Charts in exponential scale, preserving stencil properties

`amount` weights often $∃λ$, later constrain all via Phi dim. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Alps
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum
open Momentum Metric
open scoped Topology ContDiff
variable {G:Gauge}{I A B E P:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup P][NormedSpace ℝ P]
  {m n:ℕ}
def plower (a:ℂ)(t:ℝ): Signal.MH (Mob G):= {
   toFun:=plow a t
   map_smul':= by intro x p; ext; simp only [plow,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring
   map_add':= fun U V=> funext fun i=> funext fun l=> by simp only [plow,Pi.add_apply,mul_add] }
lemma cert (a:ℂ)(t:ℝ)(F:Mob G): plower a t F=plow a t F:=rfl
lemma shift (a b:ℂ)(t:ℝ)(F:Mob G): plow (a+b) t F= amount b t • plow a t F:= by
   ext; simp only [plow,Pi.smul_apply,smul_eq_mul]; simp_rw [amount_add]; ring
lemma gene (K:Spin (L m))(i j: Cfield G m) (h:(flagS K G).fieldC i j≠0): wfield i=wfield j:=by
   let n:= i.1.2; have he:n=j.1.2:= by_contradiction fun he=> h (by simp [flagS,leggo,Spin.prop,rayS,show i.1.2≠ _ from he])
   unfold n at he; simp [wfield, dim, he] -- Ambig `Spin.prop`
lemma beam_W (a:ℂ)(t:ℝ)(K:Spin (L m))(F:Rack G m)(w:Legs (Shore G m)) :
   beam (flagS K G) (fun w=> amount (a+(mass w:ℂ)) t*F (sr t w)) w= amount (a+(mass w:ℂ)) t*((flagS K G).beam F (sr t w)):= by
   induction w generalizing F a with
   | nil=> simp [sr] -- nil
   | cons i w ih=> let V:=flagS K G; rw [Pilot.met,show sr t (i::w)=(i.1,Real.exp t • i.2)::sr t w from rfl, Pilot.met,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; by_cases h:V.fieldC i.1 j=0; · rw [show (flagS K G).fieldC _ _=0 from h]; simp
                   simp only [Price_cons]; have hm : D (j,V.volp i.2) (fun w=> amount (a+(mass w:ℂ)) t * F (sr t w)) =(fun w:Legs (Shore G m)=> amount (a + wfield i.1+(mass w:ℂ)) t* D (j,V.volp (Real.exp t • i.2)) F (sr t w)):= by
                         funext w; simp only [at_D,Price_cons, sr, List.map_cons, Int.cast_add,add_assoc, ← gene K _ j h, show V.volp (Real.exp t • i.2)=Real.exp t • V.volp i.2 from map_smul K.turn ..]
                   rw [hm, ih]; push_cast; rw [add_assoc]; ring
variable {F:Mob G} {U:Rip G}{b:Bool}
lemma Stays (h:Sturdy b F)(a:ℂ)(t:ℝ): Sturdy b (plow a t F):= by
   refine ⟨fun m K hK=>?_,fun h' i=>?_⟩; · funext l; calc
        _ = amount (a+(mass l:ℂ)) t*((flagS K G).beam (F m) (sr t l)):= beam_W ..
        _ = _:= by rw [h.turn m K hK]; rfl
   unfold plow; rw [mass_lift, lift_sr,h.grows h']
lemma mead (h:Ruddy b U)(a:ℂ)(t:ℝ): Ruddy b (pulse a t U) where
   grows h' i j p:= by rw [pulse,← map_smul,h.grows h']; rfl
   turn n K hK p i j:= by
       have H := h.turn n K hK; unfold pulse; rw [← show (flagS K G).volp (Real.exp t • p)=Real.exp t • (flagS K G).volp p from map_smul K.turn .., H (Real.exp t • p)]; simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a' _=> Finset.sum_congr rfl fun j' _=> ?_; by_cases hp: (flagS K G).fieldC a' i=0; simp [hp]; by_cases hx:(flagS K G).fieldC j' j=0; simp [hx]; rw [gene K a' i hp, gene K j' j hx]; ring
end YM.MS.Alps
