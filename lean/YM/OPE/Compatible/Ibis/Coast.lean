import YM.OPE.Compatible.Munch.Rind
/-! # Budget derivative probes. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
open Silt Cloud PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Spells Borealis Lav Borealis.Galea Flock
variable {X I:Type}{t s:ℝ}{i k:ℕ} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
-- budget derivatives without metric cost via univariate directions.Diced contractions.P
section
variable {p q:X→ℝ}
abbrev Future:= ℕ→price
variable (Y:I→X)
noncomputable def March (g:X→ℝ): List I→X→ℝ
      | []=>g
      | i::s=> March (pointD (Y i) g) s
-- termination by second; syntax lean g used? pattern need Y arg
lemma ζadd (h:Bond p)(hp:Bond q)(a:List I): March Y (p+q) a=March Y p a+March Y q a:=by
       induction a generalizing p q with
       | nil=> rw[March,March,March]
       | cons i l ih=> rw[March, March, March, pointS _ _ _ h hp]; exact ih (h.amount _) (hp.amount _)
lemma pointSu (v:X)(h:Bond p)(hp:Bond q): pointD v (p-q)=pointD v p-pointD v q:=by
       funext x; rw [pointD, fderiv_sub (h.smooth.differentiable (by simp)|>.differentiableAt) (hp.smooth.differentiable (by simp)|>.differentiableAt)];rfl
lemma ζsub (h:Bond p)(hp:Bond q)(a:List I): March Y (p-q) a=March Y p a-March Y q a:=by
       induction a generalizing p q with
       | nil=>rw[March,March,March]
       | cons i l ih=>rw [March,March,March,pointSu _ h hp]; exact ih (h.amount _) (hp.amount _)
lemma ζscale (h:Bond p)(v:ℝ)(a:List I): March Y (v • p) a=v • March Y p a:=by
       induction a generalizing p with
       | nil=> rw [March,March]
       | cons i l ih=>
            rw [March,March,show pointD (Y i) (v • p)= v • pointD (Y i) p from ?_,ih (p:=pointD (Y i) p) (h.amount _)]
            funext x; change (fderiv ℝ (fun i=>v*p i) x) (Y i)=_; rw [fderiv_const_mul (𝕜:=ℝ)]; rfl; exact h.smooth.differentiable (by simp) _ -- rewrite
variable [MeasurableSpace X][BorelSpace X](A:Law X)(μ:Measure X)[μ.IsAddHaarMeasure]
local notation "YΦ"=> quart A μ
structure Quest (C:ℝ): Prop where
      high:0 ≤ C
      normP : ∀ i j:I,‖A.P (Y i) (Y j)‖ ≤ C
abbrev Quell (d:Future)(p:X→ℝ): Prop:=∀ l:List I,Borealis.Galea.Cane (quart A μ) (March Y p l) (d l.length)
namespace Quest
variable (d:Future)(h:Quest Y A t)
local notation "E"=> Quell
noncomputable abbrev shiftU (d:Future)(n:ℕ):=d (n+1)
noncomputable abbrev Tc (f:X→ℝ)(x:I):X→ℝ:= ⇑(A.P (Y x))*f
noncomputable def Mlst (t:ℝ) (d:Future): Future
      | 0=>JumpP (fun i=>Real.sqrt t * ampleP i) (d 0)
      | n+1=>Mlst t (shiftU d) n+t • (d n)
omit [FiniteDimensional ℝ X][BorelSpace X][μ.IsAddHaarMeasure] in
lemma fallQ (hd:E Y A μ d p)(i:I): E Y A μ (shiftU d) (pointD (Y i) p):=by intro l; rw [← (show _= March Y (pointD (Y i) p) l from (show March Y p (i::l)= _ from by rw [March]))]; exact hd (i::l)
include h
lemma frond (hd:E Y A μ d p)(hx:Bond p)(i:I): E Y A μ (Mlst t d) (Tc Y A p i):=by
       intro l; induction l generalizing d p with
       | nil=>
           unfold Tc; rw[March]; let x:= Y i; have hv: A.wick (A.P x) (A.P x) ≤ t := by change A.P x (A.inverse (A.P x)) ≤ _; rw [A.solves]; exact (Real.le_norm_self _).trans (h.normP i i)
           intro n hn; rw [List.length_nil,Mlst]; have he : Borealis.Galea.Cane YΦ p (d 0):=by have hh:=hd []; rwa [March] at hh
           have hu:Borealis.Galea.Cane YΦ (fun y=>A.P x y) (fun i=> Real.sqrt t * ampleP i):= fun _ H=> Lal A μ (A.P x) (show 0 ≤ Real.sqrt t from Real.sqrt_nonneg _) (hv.trans_eq (Real.sq_sqrt h.high).symm) H -- missing args
           exact (hu.mul he) n hn
       | cons j l ih=>
           let Dp:= pointD (Y j) p; let x:= Y i; let k:= A.P x (Y j); have hpA:=h.normP i j
           have H:Borealis.Galea.Cane YΦ (March Y (Tc Y A Dp i) l) (Mlst t (shiftU d) l.length):=ih _ (fallQ Y A μ d hd j) (hx.amount _)
           have hp' : pointD (Y j) (Tc Y A p i)= Tc Y A Dp i+ k • p:=by
               rw [Tc,pointM _ _ _ (Bond.glyph _) hx,pointC]; apply congr_arg (fun p:X→ℝ=>Tc Y A Dp i+p); exact funext fun _=> mul_comm ..
           rw [March, hp', ζadd Y (p:=Tc Y A Dp i) (q:=k • p) ((Bond.glyph _).mul (hx.amount _)) (hx.scale _),ζscale Y hx,List.length_cons,Mlst]; exact H.add (((hd l).scal k).grow fun i' hi=>mul_le_mul_of_nonneg_right hpA ((hd l _ hi).pos))
end Quest
end
end YM.OPE.Ibis
