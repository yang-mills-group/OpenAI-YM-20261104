import YM.MS.Heat.Odelta
import YM.MS.Heat.Broad
/-!
# Time derivatives for flows

absolute-length differentiation, not log. Master check at all times. Integral measure with stationary compact load.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Book Convolve Base
open Wire
open scoped Topology ContDiff
variable {E E' P A I:Type}[NormedAddCommGroup P][NormedSpace ℝ P][NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup E'][NormedSpace ℝ E'][Fintype A]
variable {F H : BF A P}{K:ℝ→ Flux A P ℂ}{p: Sector A} {F' H': Row A P ℂ}{L:Flux A P ℂ}{t:ℝ}{c:Bool}
def Jet (K:ℝ→ Flux A P ℂ)(L:Flux A P ℂ)(t:ℝ): Prop:= ∀ i j x, HasDerivAt (fun s=>K s i j x) (L i j x) t
namespace Zip
omit [Fintype A] [NormedAddCommGroup P][NormedSpace ℝ P] in
lemma add (h: Zip F F' t)(he: Zip H H' t): Zip (F+H) (F'+H') t:= fun i=> (h i).add (he i)
omit [Fintype A][NormedAddCommGroup P][NormedSpace ℝ P] in
lemma scalar (h:Zip F F' t)(c:ℂ): Zip (c • F) (c • F') t:= fun w=> (h w).const_mul c
end Zip
omit [NormedAddCommGroup P][NormedSpace ℝ P] in
lemma ZQ (Z:Charge p P ℂ)(h:Zip F F' t): Zip (fun x=> Z.raise (F x)) (Z.raise F') t:= by
    intro l; let S:=Centre (Legs (Mode A P)); have H T (hT:T∈S): HasDerivAt (fun x=> T (F x)) (T F') t:= by
         refine Submodule.span_induction (p:=fun T _=> HasDerivAt (fun x=>T (F x)) (T F') t) ?_ (hasDerivAt_const ..) (fun i j x y hi hj=> hi.add hj) (fun c f _ hf=> hf.const_mul c) hT
         rintro i ⟨i,rfl⟩; exact h i
    exact H _ ((sense_Q Z).reaches l)
-- point tree jets. reversal at all times and at derivative kernel (power). easier via radius. 
omit [NormedSpace ℝ P] in
lemma tree_zip (hh:∀ i, Reverse (K i) p)(hr: Reverse L p)(hk:Jet K L t)(hf: Zip F F' t)(h: Zip H H' t): Zip (fun x=> tree p (K x) (F x) (H x)) (tree p L (F t) (H t)+ tree p (K t) F' (H t)+tree p (K t) (F t) H') t:= by
   have hb i j l r: HasDerivAt (fun x=> radius p (K x) i j (F x) (H x) l r) (radius p L i j (F t) (H t) l r+ radius p (K t) i j F' (H t) l r+radius p (K t) i j (F t) H' l r) t := by
       unfold radius; dsimp only; convert! (((hk i j (-net l)).const_mul 2).mul ((hf ((i,-net l)::l)).const_mul (cross (p j) (degree (field p) l))))|>.mul (h ((j,- -net l)::r)) using 1; dsimp only [Pi.mul_apply]; ring
   intro l; let U i:=attaches p (K i) (F i) (H i); let Y:=attaches p L (F t) (H t)+ attaches p (K t) F' (H t) + attaches p (K t) (F t) H'; let W (l:Legs (Mode A P)):= allocate (field p) l (R:=ℂ)
   have he w (U: ℝ→ Shared (Mode A P) ℂ)(Y : Shared (Mode A P) ℂ)(h : ∀ i j, Split i j w→HasDerivAt (fun x=> U x i j) (Y i j) t): HasDerivAt (fun x=> W w (U x)) (W w Y) t:= by induction w generalizing U Y with| nil=> exact h _ _ .nil| cons a l ih=>exact ih _ _ (fun i j h'=> (h _ _ h'.left).add ((h _ _ h'.right).const_mul _))
   have hv l : W l Y=tree p L (F t) (H t) l+ tree p (K t) F' (H t) l+tree p (K t) (F t) H' l:=by unfold Y; rw [map_add,map_add]; rfl
   suffices hz : ∀ i j, Split i j l→ HasDerivAt (fun x=>U x i j) (Y i j) t by rw [Pi.add_apply,Pi.add_apply,← hv]; exact he l U Y hz
   intro i j _; unfold U Y; simp only [Pi.add_apply]; simp_rw [convertR (hh _),convertR hr,← Finset.sum_add_distrib]; refine HasDerivAt.fun_sum (fun k _=> HasDerivAt.fun_sum (fun t _=>hb k t i j))
variable [FiniteDimensional ℝ P] [MeasurableSpace P][BorelSpace P]
lemma orbit_zip (μ:Measure P)[IsFiniteMeasure μ](ht:Cour μ)(hL: flex K)(h:TouchF F)(hT: Pass L (F t) μ)(hp:Pass (K t) F' μ)(hk: Jet K L t)(hf: Zip F F' t): Zip (fun x=> orbit (K x) μ (F x)) (orbit L μ (F t)+ orbit (K t) μ F') t:= by
   intro l; let f (x:P×ℝ) := trc (K x.2) x.1 (F x.2) l; have he : ContDiff ℝ ∞ f:= by
       let w:tagSmooth (P×ℝ) A P:= l.map fun p=>(p.1,fun _=>p.2); convert flex_pays h hL Prod.snd contDiff_snd Prod.fst contDiff_fst (w:=w) ?_ using 1; ext; unfold f w walk0; simp [Function.comp_def]
       intro x hx; obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hx; exact contDiff_const
   let V (x:ℝ) := ∫ i,f (i,x) ∂μ; have hv := Lot μ ht he; simp_rw [finite_cc μ (period0 μ ht hL h)]; rw [finite_cc μ hT,finite_cc μ hp];
   let Y (x:P):= trc L x (F t) l + trc (K t) x F' l; have hY x: HasDerivAt (fun t=> f (x,t)) (Y x) t:= by unfold f Y; simp only [at_trc,← Finset.sum_add_distrib]; exact HasDerivAt.fun_sum (fun i _=> HasDerivAt.fun_sum (fun k _=> (hk i k x).mul (hf _)))
   have hR : iteratedDeriv 1 V t= ∫ x,Y x ∂μ:= by rw [iteratedDeriv_eq_iteratedFDeriv]; dsimp only [V]; rw [hv.identity,ContinuousMultilinearMap.integral_apply (hv.integ 1 t)]; refine integral_congr_ae (Eventually.of_forall (fun x=>?_)); dsimp only; rw [← iteratedDeriv_eq_iteratedFDeriv,iteratedDeriv_one,hY x|>.deriv]
   have hz : HasDerivAt V (∫ x,Y x ∂μ) t:= by rw [← hR, iteratedDeriv_one]; exact (hv.contDiff.differentiable (by simp) t).hasDerivAt
   unfold Y at hz; rw [integral_add (hT _) (hp _)] at hz; exact hz
end YM.MS.Heat
