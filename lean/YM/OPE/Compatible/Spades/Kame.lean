import YM.OPE.Compatible.Spades.Break
/-!
# Orthogonal equivalence for smooth heavy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Jargon
open MeasureTheory Function Set Finset Filter Module
open scoped Topology BigOperators Classical ContDiff ENNReal
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial Silt Tensor Cloud
variable {E F X Y:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup X] [NormedSpace ℝ X]
variable {I J:Type}{i j k r:ℕ}{p q:E→ℝ}
local notation "Z"=> Radial.zone (E:=E)
section
variable [FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E]
variable (A:Law E)(μ:Measure E)[μ.IsAddHaarMeasure]
def RunsG (A:Law E)(μ:Measure E)(p:E→ℝ):Prop:=Integrable (p * A.kern) μ
lemma runsG (h:Stature p j): RunsG A μ p:=A.integrable_entry μ h.invoice h.smooth.continuous
lemma burlV (h:Stature p j)(hi:i≤j){v:Fin i→E}: RunsG A μ (Fline p v):= A.integrable_entry μ (h.card hi v) (h.pic hi)
omit [FiniteDimensional ℝ E] [BorelSpace E][μ.IsAddHaarMeasure] in lemma duneAdd (h:RunsG A μ p)(hp:RunsG A μ q): A.average μ (p+q)=A.average μ p+A.average μ q:=by unfold Law.average; rw[add_mul]; simp only [Pi.add_apply]; rw [integral_add h hp,add_div]
omit [FiniteDimensional ℝ E] [BorelSpace E][μ.IsAddHaarMeasure] in lemma duneSub (h:RunsG A μ p)(hp:RunsG A μ q): A.average μ (p-q)=A.average μ p-A.average μ q:=by unfold Law.average; rw[sub_mul]; simp only [Pi.sub_apply]; rw [integral_sub h hp,sub_div]
lemma swell (a:E)(h:Stature p (j+1)): A.average μ (⇑(A.P a)*p)= A.average μ (pointD a p):=by
      let g:= pointD a p; have hg:= h.lower a; have hp:=((Stature.poly (Bond.glyph (A.P a)) (j+1)).mul h); have hq:=A.translation_lemma a h.invoice h.smooth.continuous hg.invoice hg.smooth.continuous (fun x y=> ?_) μ
      · unfold Law.average; rw [mul_comm p,sub_mul] at hq; simp only [Pi.sub_apply] at hq; rw [integral_sub (runsG A μ hg) (runsG A μ hp)] at hq; exact congr_arg (· /_) (sub_eq_zero.mp hq).symm
      let t(z:ℝ):= x+z • a; have hx:HasDerivAt t a y:=by simpa only [one_smul] using! HasDerivAt.const_add x ( (hasDerivAt_id' y).smul_const a)
      exact (h.smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt y hx
noncomputable def Vas (p:E→ℝ)(i:Fin j→E):ℝ := A.average μ (Fline p i)
omit [FiniteDimensional ℝ E] [BorelSpace E][μ.IsAddHaarMeasure] in lemma vas0 (p:E→ℝ) (i:Fin 0→E): Vas A μ p i=A.average μ p:=by rw [Vas,Fline_zero]
-- anti through all e LESS than k. no integrable assumption built in
structure Haven (μ:Measure E)(A:Law E)(i:ℕ) (p:E→ℝ):Prop where
    bill {k:ℕ} : k < i→∀ q:E→ℝ,anthem k q→A.average μ (p*q)=0
namespace Haven
variable {μ A}
omit [FiniteDimensional ℝ E][BorelSpace E][μ.IsAddHaarMeasure] in
lemma points (h:Haven μ A i p)(hv:k ≤ i): Haven μ A k p:=⟨fun hi=> h.bill (lt_of_lt_of_le hi hv)⟩ -- unused vars
omit [FiniteDimensional ℝ E][BorelSpace E][μ.IsAddHaarMeasure] in
lemma first (h:Haven μ A (k+1) p):A.average μ p=0:=by have he:= h.bill (show 0<k+1 from Nat.succ_pos _) 1 (anthem.bank ..); rwa [mul_one] at he
lemma drift (h:Haven μ A (j+1) p)(hp:Stature p (i+1))(v:E): Haven μ A j (pointD v p):=by
      refine ⟨fun {e} he q hq=>?_⟩; have hz:= h.bill (show e+1<j+1 from by omega) _ (anthem.cons (A.P v) hq); have hu:= Stature.poly hq.cost (i+1); rw [show p*_=⇑(A.P v)*(p*q) from by ring,swell _ _ _ (hp.mul hu),ringWheel hp hu v, duneAdd (p:=p*pointD v q) (q:=q*pointD v p) _ _ (runsG A μ ((hp.mono i.le_succ).mul (hu.lower v))) (runsG A μ ((hu.mono i.le_succ).mul (hp.lower v))),h.bill (show e-1<j+1 by omega) _ (veils v hq),zero_add] at hz; rw [mul_comm]; exact hz
omit [FiniteDimensional ℝ E][BorelSpace E][μ.IsAddHaarMeasure] in
lemma cohabit (h:Haven μ A k p)(hp:anthem i q)(hh:r+i ≤ k): Haven μ A r (p*q):=⟨fun hx g hg=>by rw [mul_assoc]; exact h.bill (by omega) _ (hp.times hg)⟩
lemma thaw (p:E→ℝ)(hp:Stature p (i+1))(he:A.average μ p=0)(hz:∀ v:E,Haven μ A j (pointD v p)): Haven μ A (j+1) p:=by
      induction j using Nat.strong_induction_on with
      | h j ih=>
          refine ⟨fun {k} hk q hq=>?_⟩; induction hq with
          | bank n t=> rw [show p*_= t • p from funext fun v=> mul_comm ..,scooted,he,mul_zero]
          | @add n f g hv hu Ha Hb=>rw [mul_add, duneAdd A μ (runsG _ _ (hp.mul (Stature.poly hv.cost _))) (runsG _ _ (hp.mul (Stature.poly hu.cost _))),Ha hk,Hb hk, add_zero]
          | @cons n u f hH IH=>
                    let a:= A.inverse u; have ha:=hz a; have hv:Stature f (i+1):= Stature.poly hH.cost _; have hh: pointD a p*f=f*pointD a p:= mul_comm ..
                    rw[← (show A.P a=u from A.applies _),show p*_=⇑(A.P a)*(p*f) from by ring,swell A μ a (hp.mul hv), ringWheel hp hv a,duneAdd (p:=p*pointD a f) (q:=f*pointD a p) _ _ (runsG A μ ((hp.mono i.le_succ).mul (hv.lower a))) (runsG A μ ((hv.mono i.le_succ).mul (hp.lower a))),←hh,ha.bill (by omega:n<j) f hH, add_zero]; have hr: Haven μ A (n+1) p:= ih n (by omega) (fun v=>(hz v).points (by omega)); exact hr.bill (by omega:n-1<n+1) _ (veils a hH)
end Haven
lemma corresponding (k:ℕ) (h: Stature p k):Haven μ A (k+1) p ↔ ∀ i:ℕ,i ≤ k →∀ x:Fin i→E,Vas A μ p x=0:=by
      induction k generalizing p with
      | zero=>
          constructor
          · intro he i hi; obtain rfl:= Nat.eq_zero_of_le_zero hi; intro v; rw [vas0]; exact he.first
          intro hp; refine ⟨fun {j} hj f hf=>?_⟩; cases j with
          | succ j=>omega
          | zero=>
               have he:∀ n (f:E→ℝ),anthem n f→n=0→∃ c,f=fun _=>c:=by
                  intro n f hf hn; induction hf with
                  | bank=>exact ⟨_,rfl⟩
                  | add _ _ H Hp=> obtain ⟨c,hc⟩:= H hn; obtain ⟨b,hb⟩:=Hp hn; rw [hc,hb]; exact ⟨c+b,rfl⟩
                  | cons=>omega
               obtain ⟨c,rfl⟩:=he _ _ hf rfl; have hx:=hp 0 le_rfl fun _=>0; rw [vas0] at hx; rw[show p*_ =c • p from funext fun x=>mul_comm ..,scooted,hx,mul_zero]
      | succ k ih=>
          have he(a:E)(j:ℕ)(hi:j ≤ k)(v:Fin j→E): Vas A μ p (Fin.snoc v a)=Vas A μ (pointD a p) v:=congr_arg (A.average μ) (rungs (h.smooth.of_le (Nat.cast_le.mpr (by omega))) v a)
          constructor
          · intro hp i hi x; cases i with
            | zero=> exact (vas0 ..).trans hp.first
            | succ i=> rw [← Fin.snoc_init_self x,he _ i (by omega)]; exact (ih (h.lower _)).mp (hp.drift h _) i (by omega) _
          intro hp; refine Haven.thaw _ h ((vas0 A μ p (fun _:Fin 0=>0)).symm.trans (hp 0 (Nat.zero_le _) _)) (fun v=>(ih (h.lower v)).2 (fun i hi x=>?_)); rw[← he v i hi]; exact hp _ (by omega) _
end
end YM.OPE.Jargon
