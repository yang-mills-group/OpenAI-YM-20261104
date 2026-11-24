import YM.MS.Wind.Traces
/-!
# Uniformity in logMS parameter at resolution one

At arbitrary momenta, not using decay of the frame propagator. Use strict periodicity
 of each mode (double Brillouin shift). count integrals polynomial. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Real
open Landau Native Lattice Tone Momentum Heat Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal High
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{b:Bool}{u:ℤ}{t:ℝ}{P:Pack G}{F H: Wind.Flow G} {X E : Type}[Fintype X][DecidableEq X][NormedAddCommGroup E][NormedSpace ℝ E]

-- strict periodic

def amt (q:X→Cover) : (X→ QP):= fun i=> rep (q i)+ rep (q i)
lemma strictPerk (l r:List (Lane4 G)) (h: Perk (F t))(i:BH G)(p: QP)(q:Cover): F t (l++(i,p+(rep q+rep q))::r)=F t (l++(i,p)::r):= by rw [← add_assoc,h l r i (p+rep q) q,h l r i p q,←mul_assoc, testX, one_mul]
lemma altSpace (h:Perk (F t))(n:ℕ)(f:Fin n→ BH G)(p: Fin n→QP)(q:Fin n→Cover)(l:List (Lane4 G)): F t (l++ Local.gaze f (p+amt q))=F t (l++ Local.gaze f p):= by
    induction n generalizing l with | zero=> simp [Local.gaze]| succ n ih=>
       simp only [Local.gaze,List.ofFn_succ, Pi.add_apply]; unfold amt at *; rw [strictPerk l _ h]
       have he (a:Lane4 G)(v:List (Lane4 G)): l++a::v=(l++[a])++v:= (List.append_assoc l [a] v).symm;
       simpa [Local.gaze] using ih (f∘Fin.succ) (p ∘ Fin.succ) (q∘ Fin.succ) (l++[(f 0,p 0)]) -- eta
omit [DecidableEq X] in
lemma realm (p: X→QP): ∃ z:X→ QP, ∃ q, ‖z‖ ≤ 4*π ∧ p=z+amt q:= by
    let r:= 4*π; have hr:0<r:= by unfold r; positivity
    let q (i:X) (k:Axis) := Int.floor (p i k/r); let z:=p-amt q; have hz (i:X) k: amt q i k=(q i k:ℝ)*r:= by unfold amt q Tone.rep embed r; dsimp; ring
    refine ⟨z,q,?_ ,(sub_add_cancel ..).symm⟩; apply (pi_norm_le_iff_of_nonneg hr.le).mpr; intro i; apply (pi_norm_le_iff_of_nonneg hr.le).mpr; intro k; rw [norm_eq_abs,abs_le]; unfold z; rw [Pi.sub_apply, Pi.sub_apply, hz];
    have hu := (le_div_iff₀ hr).mp (Int.floor_le (p i k/r)); have hx := (div_lt_iff₀ hr).mp (Int.lt_floor_add_one (p i k/r)); change _ ≤ _ at hu
    change -r ≤ _ ∧ _ ≤r; unfold q; constructor <;> linarith
lemma temper (h: Bon b u F) (n:ℕ)(f:Fin n→ BH G) (t:ℝ) : (fun p=> F t (Local.gaze f p)).HasTemperateGrowth:= by
   let A p := F t (Local.gaze f p); have he : ContDiff ℝ ∞ A:= by unfold A; simp_rw [← Local.at_arr]; exact TouchF.routine h.joint _ _
   refine ⟨he,fun j=>?_⟩; let U p:= ‖iteratedFDeriv ℝ j A p‖; have hx : Continuous U:= (he.continuous_iteratedFDeriv (m:=j) (by exact_mod_cast le_top)).norm;
   let W:= Metric.closedBall (0:Fin n→QP) (4*π); letI : ProperSpace (Fin n→QP):= FiniteDimensional.proper ℝ _; obtain ⟨v,hv⟩:= ((isCompact_closedBall (0:Fin n→QP) (4*π)).image hx).bddAbove
   refine ⟨0,v,fun p=>?_⟩; obtain ⟨z,q,hz,rfl⟩:= realm p; simp only [pow_zero,mul_one];
   have hg : ‖iteratedFDeriv ℝ j A z‖ ≤ v:= hv (Set.mem_image_of_mem U (by simpa using hz)); change U _ ≤ _; rw [show U (z+amt q)=U z from ?_]; exact hg
   unfold U; rw [add_comm z, ← iteratedFDeriv_comp_add_left]; congr! 2; funext i; rw [add_comm]; exact altSpace (h.perk t) n f i q [] -- check
lemma stamp_sail (h: Bon b u F)(t:ℝ)(w:Wire (BH G) E QP): HasTemperateGrowth (fun x=> F t (sail w x)):= by
    let i (a:Fin w.length):= (w.get a).1; let T : E →L[ℝ] (Fin w.length→ QP) := ContinuousLinearMap.pi (fun j=> (w.get j).2); rw [show (fun x=>F t (sail w x))=(fun p=> F t (Local.gaze i p))∘ T from funext fun x=> congr_arg (F t) (by apply List.ext_getElem; all_goals simp [sail,Local.gaze,T,i])]; exact (temper h _ i _).comp T.hasTemperateGrowth
end YM.MS.Wind
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Real
open Landau Native Lattice Tone Momentum Heat Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal High
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{b:Bool} {v:ℤ}{t:ℝ} {P:Pack G}
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E]
lemma poly_t (c: _root_.Polynomial ℝ): (fun i:ℝ=> c.eval i).HasTemperateGrowth:= by
   induction c using _root_.Polynomial.induction_on' with
   | add p q hp hq=> simp_rw [_root_.Polynomial.eval_add]; exact hp.add hq
   | monomial n a=> simp_rw [_root_.Polynomial.eval_monomial]; exact (HasTemperateGrowth.const a).mul (HasTemperateGrowth.id.pow n) -- id field?
lemma polynomial_cost (D:Polynomial ℝ): Bound meet.dawn (fun i:ℝ=>fun _:E=> D.eval i) fun _=>1:=by
   apply Costs.scalar; obtain ⟨b,C,hx,hC⟩:= (poly_t D).norm_iteratedFDeriv_le_uniform 0; refine ⟨C+1,by positivity,b,fun i p _=>?_⟩; specialize hC 0 le_rfl i; simp only [norm_iteratedFDeriv_zero] at hC; apply hC.trans; simp only [mul_one];
   have he: (1+‖i‖)≤ meet.dawn.full.cheap i p := by
       change _ ≤ (1+|i|)*(1+0)*(1+exp 0*‖p‖); simp only [add_zero,mul_one, Real.norm_eq_abs]; exact le_mul_of_one_le_right (by positivity) (by simp)
   gcongr; linarith
lemma posture (h:Fees b v P)(t:ℝ)(w:Wire (BH G) E QP): Bound meet.dawn (fun i x=> P i t (sail w x)) fun _=>1:=by
   obtain ⟨v,hv⟩:=h.currency; have hx (i:ℝ) (x:E) : P i t (sail w x)=∑ j∈Finset.range v,(plate v j).eval i • P j t (sail w x):= by nth_rw 1 [interpret hv i]; unfold evaluate; simp
   rw [funext fun i=> funext (hx i)]; refine Costs.sum _ (fun j _=>?_ ) fun _ _ _=>zero_le_one; let f : E→ ℂ:= fun i=> P j t (sail w i); have he : Bound meet.dawn (fun _=>f) fun _=>1:= by
       have hs:= meet.dawn.rescaled (stamp_sail (h.stay (j:ℝ)) t w); simpa [LogTime.IntervalFamily.dawn, meet, f] using hs -- need field path
   convert! (polynomial_cost (E:=E) (plate v j)).smul he using 1; simp
lemma post_ok (F:Dec G)(h:∀ n,Fees b v (F n)): Rising b (col F):= fun _ _ _ n w _ _=> posture (h n) (exp 0) w
end YM.MS.Wind
