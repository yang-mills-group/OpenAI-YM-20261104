import YM.MSbar.Pole.Symbol.Trace

/-! Slot update invariance and analytic angular contraction of poles. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Set Function Filter MeasureTheory Ambient Momentum Age Mellin place
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {I : Type} [Fintype I] {n : ℕ}
namespace Wall
variable {E J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup J] [NormedSpace ℝ J] {U : Set ℂ}
lemma affine {F : ℂ→E→ℂ} (h : Wall U (ticket (@id E)) 1 F) (L : J→L[ℝ] E) (b:E) : Wall U (ticket (@id J)) 1 (fun z x=>F z (b+L x)):= by
  let T : ℂ × J →L[ℝ] ℂ × E := (ContinuousLinearMap.fst ..).prod (L.comp (ContinuousLinearMap.snd ..)); let a : ℂ×E := (0,b)
  have he (x:ℂ×J):a+T x=(x.1,b+L x.2):= by change (0+x.1,b+L x.2)=_; rw [zero_add]
  have hp := comp_affine_bill T a h.stream (U:=strip J U) (p:=stretch (ticket (@id J))) (q:=1) (fun i hi=>?_ ) ?_ (Bills.const _)
  · simp_rw [he] at hp; exact ⟨hp,fun z hz x=>h.region _ hz _⟩
  · change a+T i ∈ _; rw [he]; exact ⟨hi.1,mem_univ _⟩
  simp_rw [he]; refine bill_single (C:=1+‖b‖+‖L‖) (by positivity) (l:=1) fun x hx=> ?_
  change ‖1+‖b+ L x.2‖‖ ≤ _*(1+‖x.2‖)^1; rw [Real.norm_of_nonneg (by positivity),pow_one]
  nlinarith [L.le_opNorm x.2,norm_add_le b (L x.2),norm_nonneg x.2,norm_nonneg b,norm_nonneg L]
end Wall
namespace Symbol
variable {a b i : I} {F : ℂ→Cloud I} {R:ℝ}

def blink (a:I) (n:ℕ): External I n →L[ℝ] External I n := ContinuousLinearMap.pi fun i=>if i=a then 0 else ContinuousLinearMap.proj i
lemma blinks (a:I) (x:External I n) : blink a n x=update x a 0:=by funext i; by_cases hi:i=a; subst i; simp [blink]; simp [blink,hi]
def dotChange (a b:I) (n:ℕ):= (blink a n).comp (blink b n)
lemma dots (x:External I n)(u v:place n): joint a b x u v = joint a b 0 u v + dotChange a b n x := by
  change _=_+(blink a n ((blink b n) x)); rw [blinks,blinks]; funext i; by_cases h:i=a; subst i; simp [joint];
  by_cases hy:i=b; subst i; simp [joint,h]; simp [joint,h,hy]

def expanded (n : ℕ) : External I n →L[ℝ] External I (n+1):=ContinuousLinearMap.pi fun i=> (pad n).comp (ContinuousLinearMap.proj i)
lemma cheaper (a b:I)(h : Wall (zone R) (ticket (@id (External I n))) 1 (fun z=> F z n)):
    Wall (zone R) (ticket (@id (External I n))) 1 (fun z x=> horizontal a b (F z) x) := by
  let A (i : Fin (2*n)) (z:ℂ) (x : External I n) := F z n (joint a b x (ortho n i) (ortho n i))
  have he(i:Fin (2*n)):Wall (zone R) (ticket (@id _)) 1 (A i):= by
    unfold A; rw [show (fun z (x:External I n)=> F z n (joint a b x (ortho n i) (ortho n i))) = fun z x=> F z n (joint a b 0 (ortho n i) (ortho n i) + dotChange a b n x) from funext fun z=> funext fun x=> congr_arg _ (dots ..)]
    exact h.affine _ _
  have hv := Wall.sum Finset.univ A fun i _=> he i
  apply Wall.eq Metric.isOpen_ball hv; intro z _; funext x; simp_rw [horizontal,Finset.sum_apply]; rfl

lemma distant (a b:I) (h : Meridian (zone R) F) (n : ℕ) :
    Wall (zone R) (ticket (@id (External I n))) 1 (fun z x=> (dimension z-2*n)*vertical a b (F z) x) := by
  let c(z:ℂ):= dimension z-2*n; have hc : Differentiable ℂ c:=by unfold c dimension; fun_prop
  refine Wall.mul (Wall.entire hc R fun x hx=>((zone_mem ..).mp hx).le) ?_
  let v := place.room n 1 -- namespace shadow
  have ht:= (h.budget (n+1)).affine ((dotChange a b (n+1)).comp (expanded (I:=I) n)) (joint a b 0 v v)
  refine Wall.eq Metric.isOpen_ball ht ?_
  intro z hz; funext x; exact congr_arg _ (dots ..)

lemma tracing (hn:a≠b) (h : Meridian (zone R) F) (hf : ∀ z∈zone R,Tone (F z) a) (hg : ∀ z∈zone R,Tone (F z) b) :
    Meridian (zone R) (fun z=> stroke a b (dimension z) (F z)) :=
  ⟨fun n => (cheaper a b (h.budget n)).add (distant a b h n), fun z hz=> trace_style (h.tensor z hz) _ hn (hf z hz) (hg z hz)⟩
end Symbol
end YM.MSbar.Pole
