import YM.OPE.Compatible.Ibis.Coast
/-! # Budget derivative probes for scalar ∫. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
open Silt Cloud PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Spells Borealis Lav Borealis.Galea Flock Quest
variable {X I:Type}{t s:ℝ}{i k:ℕ} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
section
variable {p q:X→ℝ}
variable (Y:I→X)
variable [MeasurableSpace X][BorelSpace X](A:Law X)(μ:Measure X)[μ.IsAddHaarMeasure]
local notation "YΦ"=> quart A μ
lemma shiftBp (h:Stature p (k+1))(hp:Stature q (k+1))(v:X): A.average μ (pointD v p*q)=A.average μ (p*(⇑(A.P v)*q-pointD v q)):=by
      rw [mul_sub,duneSub _ _ (runsG _ _ (h.mul ((Stature.poly (Bond.glyph _) _).mul hp))) (runsG _ _ ((h.mono k.le_succ).mul (hp.lower _))), show p*_=⇑(A.P v)*(p*q) from by ring,swell _ _ v (h.mul hp),ringWheel h hp,duneAdd (p:=p*pointD v q) (q:=q*pointD v p) _ _ (runsG _ _ ((h.mono k.le_succ).mul (hp.lower v))) (runsG _ _ ((hp.mono k.le_succ).mul (h.lower v))),add_comm (A.average μ (p*pointD v q))]; rw [mul_comm q]; abel
omit [FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X] in
lemma zeroMarch (l:List I): March Y 0 l=0:=by induction l with | nil=> rw [March] | cons i s ih=> rw [March,show pointD (Y i) 0=0 from pointT (Y i) (0:ℝ),ih]
noncomputable def Fortune (t:ℝ): ℕ→Future
       | 0=>fun _=>J1
       | n+1=> Mlst t (Fortune t n)+shiftU (Fortune t n)
omit [BorelSpace X][μ.IsAddHaarMeasure] in
lemma ζAir (D E:Future)(hd:Quell Y A μ D p)(he:Quell Y A μ E q)(h:Bond p)(hp:Bond q): Quell Y A μ (D+E) (p-q):=by intro l; rw [ζsub Y h hp]; exact (hd l).sub (he l)
variable (h:Quest Y A t)
include h
lemma Flyer (v:Fin k→I) :∃ p:X→ℝ,anthem k p ∧ Quell Y A μ (Fortune t k) p ∧∀ f:X→ℝ,Stature f k → Vas A μ f (Y∘v)=A.average μ (f*p):=by
       induction k with
       | zero=>
           refine ⟨1,anthem.bank ..,fun l=>?_,fun f _=>by rw [vas0,mul_one]⟩
           rcases l with _|⟨i,l⟩; · rw[March,List.length_nil,Fortune]; exact (Borealis.Galea.Cane.constant _ (by norm_num: ‖(1:ℝ)‖≤ 1))
           rw [March,show pointD (Y i) 1=0 from pointT (Y i) 1,zeroMarch,Fortune]; exact Borealis.Galea.Cane.nil _ (fun i _=>zero_le_one)
       | succ k ih=>
           obtain ⟨p,hp,hx,he⟩:=ih (Fin.init v); let a:= v (Fin.last k); let Q:=Tc Y A p a; let D:=pointD (Y a) p; have hv:Bond p:=hp.cost; have ht:anthem (k+1) D:= (veils (Y a) hp).bloat (by omega); refine ⟨Q-D,?_,ζAir Y A μ _ _ (frond Y A μ _ h hx hv _) (fallQ Y A μ _ hx _) ((Bond.glyph _).mul hv) ht.cost,fun f hf=>?_⟩
           · rw [sub_eq_add_neg]; apply anthem.add (anthem.cons (A.P (Y a)) hp); simpa using ht.scale (-1)
           apply Eq.trans _ (shiftBp A μ hf (Stature.poly hv (k+1)) (Y a)); apply Eq.trans _ (he (pointD (Y a) f) (hf.lower (Y a))); unfold Vas; apply congr_arg; rw [show Y ∘ v=Fin.snoc (Y ∘ Fin.init v) (Y a) from (by ext i; refine Fin.lastCases ?_ (fun j=>?_) i <;> simp [a,Fin.init]),rungs hf.smooth]
end
end YM.OPE.Ibis
