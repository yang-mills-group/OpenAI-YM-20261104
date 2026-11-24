import YM.OPE.Compatible.Ibis.Feign
/-! # standardized reading moments. exact transfer and prices without dimensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
open Silt Cloud PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Spells Borealis Lav Borealis.Galea Flock Quest
variable {X I:Type}{t s r R:ℝ}{i j k:ℕ}
section
variable [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] [MeasurableSpace X][BorelSpace X]
variable (A:Law X)(μ:Measure X)[μ.IsAddHaarMeasure]
local notation "YΦ"=> quart A μ
structure Spectre (p:X→ℝ)(k:ℕ)(r:ℝ):Prop where
       Aet : Pu YΦ p
       Λ (i:ℕ)(hi:i≤k) (f:X→ℝ)(h:anthem i f)(s:ℝ)(hv:Fault YΦ 2 f s): ‖∫ x,(p*f) x ∂YΦ‖ ≤ r*s
namespace Spectre
variable {A μ}{p q:X→ℝ}
omit [FiniteDimensional ℝ X] [BorelSpace X][μ.IsAddHaarMeasure] in lemma widen (h:Spectre A μ p k r)(hs:r ≤ s): Spectre A μ p k s:=⟨h.Aet,fun i hi f hv s hh=> (h.Λ i hi f hv s hh).trans (mul_le_mul_of_nonneg_right hs hh.pos)⟩ -- TC
omit [FiniteDimensional ℝ X] [BorelSpace X][μ.IsAddHaarMeasure] in lemma bound (h:Spectre A μ p k r)(hp:j ≤ k): Spectre A μ p j r:= ⟨h.Aet,fun i hi=> h.Λ i (hi.trans hp)⟩
lemma Ffoot (h: Fault (quart A μ) 2 p r)(ht:Pu YΦ p): Spectre A μ p k r:=⟨ht,fun _ _ f _ s ht=> (Fault.pays (h.double (show Fault YΦ (2*1) f s from ht) (show 0<1 by decide)) le_rfl)⟩ -- warnings
lemma scored (h:Spectre A μ p k r)(hp:Spectre A μ q k s):Spectre A μ (p+q) k (r+s):=⟨addedP h.Aet hp.Aet, fun i hi f hv z he=>by
       have hh := Ppu A μ (Stature.poly hv.cost 0); rw [_root_.add_mul p]; simp only [Pi.add_apply]; rw[integral_add (show Integrable _ YΦ from Irite (timesP h.Aet hh)) (show Integrable _ YΦ from Irite (timesP hp.Aet hh))]; exact (norm_add_le ..).trans ((add_le_add (h.Λ i hi f hv z he) (hp.Λ i hi f hv z he)).trans_eq (_root_.add_mul ..|>.symm))⟩
omit [FiniteDimensional ℝ X] [BorelSpace X][μ.IsAddHaarMeasure] in lemma weight (h:Spectre A μ p k r)(v:ℝ): Spectre A μ (v • p) k (‖v‖*r):=⟨scaleP h.Aet v,fun i hi f hv s hx=>by rw [smul_mul_assoc]; simp only [Pi.smul_apply,smul_eq_mul];rw[integral_const_mul v (fun i=>(p*f) i),norm_mul]; exact (mul_le_mul_of_nonneg_left (h.Λ i hi f hv s hx) (norm_nonneg _)).trans_eq (_root_.mul_assoc ..|>.symm)⟩ -- vv
omit [BorelSpace X][μ.IsAddHaarMeasure][FiniteDimensional ℝ X] in lemma minus (h:Spectre A μ p k r):Spectre A μ (-p) k r:=by simpa using h.weight (-1)
lemma back (h: Haven μ A (k+1) p)(hp:Pu YΦ p): Spectre A μ p k 0:=⟨hp, fun i hi f hh _ _=> by rw [has_p,h.bill (by omega) f hh,norm_zero,zero_mul]⟩
lemma runs (h:Spectre A μ p k r)(Y:I→X)(hv:Quest Y A t)(hk:i ≤ k)(hp:Stature p i)(v:Fin i→I):‖Vas A μ p (Y∘v)‖ ≤ r*Fortune t i 0 2:=by
       obtain ⟨q,hq,hX,hh⟩:= Flyer Y A μ hv v; rw [hh _ hp,← has_p]; apply h.Λ i hk q hq; have hz:=hX []; rw [March] at hz; exact hz 2 two_pos
end Spectre
end
end YM.OPE.Ibis
