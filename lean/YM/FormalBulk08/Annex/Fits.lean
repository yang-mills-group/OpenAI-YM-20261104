import YM.FormalBulk08.Annex.Pole
import YM.FormalBulk08.Spigot.Niv

/-! Λ norms in central cube. Lift path support also in the
measures to exact address halo. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Annex
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type*}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}
open Spigot Pose

abbrev Channel (D:ℕ):= Brush D→ Measure Deck
def bondM (μ:Channel D):Halo D:= fun i=>(μ i).map embark
def Concentrated (μ:Halo D):Prop:=∃ ν:Channel D, (∀ i,IsFiniteMeasure (ν i))∧ μ=bondM ν
lemma backed {μ:Halo D}(h:Concentrated μ) : Fleet μ:= by obtain ⟨ν,p,rfl⟩:=h; intro i; have hh:=p i; unfold bondM;infer_instance
lemma massif (μ:Channel D)(i): ((bondM μ) i).real Set.univ=(μ i).real Set.univ:=by simp [bondM,measureReal_def,Measure.map_apply embarks.measurable]
lemma studX (μ ν:Channel D)(p:Studio D) : Spigot.record (bondM μ) (bondM ν) p=∑ i,((∫ v,(compress D p) i v ∂(μ i)) - (∫ v,(compress D p) i v ∂(ν i))):= by
    unfold Spigot.record bondM; refine Finset.sum_congr rfl fun i _=>?_ ; have h (f:Measure Deck): (∫ v,p.val i v ∂(f.map embark))=∫ v,(compress D p) i v ∂f:= integral_map embarks.measurable.aemeasurable (p.val i).continuous.aestronglyMeasurable; rw [h,h]
lemma records {μ ν:Halo D}(hp:Concentrated μ)(he:Concentrated ν)(x y: Studio D)(h: compress D x=compress D y):Spigot.record μ ν x= Spigot.record μ ν y:=by obtain ⟨u,p,rfl⟩:=hp; obtain ⟨v,s,rfl⟩:=he; rw [studX,studX,h]
lemma ledger (A:ℝ)(hA:0 ≤ A)(f:Studio D→ₗ[ℝ]ℝ)(hp:∀ p,‖f p‖≤ A*‖compress D p‖):∃ μ ν:Halo D, Concentrated μ∧ Concentrated ν ∧ district μ ν≤ Fintype.card (Brush D)*A ∧∀ p:Studio D,f p=Spigot.record μ ν p:=by
   obtain ⟨μ,ν,a,b,c,d⟩:= pole D A hA f hp;refine ⟨bondM μ,bondM ν,⟨μ,a,rfl⟩,⟨ν,b,rfl⟩,?_,fun p=>(d p).trans (studX _ _ _).symm⟩
   unfold district; simp_rw [massif]; exact c
lemma bill_low {μ:Halo D}(hp:Fleet μ)(i:Brush D)(u:ℕ){A:ℝ}(he:0≤ σ)(h:0≤ A): rush u σ A*(μ i).real Set.univ ≤ stub μ u A σ i:= by
    have hh:=hp i; let f (t:Pier):=rush u σ (A+‖t.val‖); have hf : Continuous f:=by unfold f rush;fun_prop
    have hw:= integral_mono (integrable_const (μ:=μ i) (rush u σ A)) (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)) fun x=> rush_more u h he (show A≤ A+‖(x:Pier).val‖ by simp)
    simpa only [f,stub,integral_const, smul_eq_mul, mul_comm ((μ i).real _)] using hw
lemma bill_roof {μ ν:Halo D}(hp:Fleet μ)(hq:Fleet ν)(u:ℕ){A:ℝ}(he:0≤σ)(h:0≤A): rush u σ A*district μ ν≤ burse u A σ μ ν:= by
   unfold burse district; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i _=>?_ ;rw [mul_add]; exact add_le_add (bill_low hp i u he h) (bill_low hq i u he h)
lemma rush_ceil (u:ℕ){A σ:ℝ}(h:0≤A)(ht:σ≤1): rush u σ (A+8)≤ (9^u* Real.exp 8) * rush u σ A:= by
   unfold rush; rw [mul_add σ, Real.exp_add]; have hz : σ*8≤8:=by linarith
   refine (mul_le_mul (show (1+(A+8))^u≤(9*(1+A))^u from pow_le_pow_left₀ (by linarith) (by linarith) _) (mul_le_mul_of_nonneg_left (Real.exp_monotone hz) (Real.exp_pos _).le) (by positivity) (by positivity)).trans_eq ?_
   rw [mul_pow];ring
lemma exposures {U W B V:Halo D}(h:Fleet U)(he:Fleet W)(hk:Fleet B)(hb:Fleet V)(hp:district U W≤ C*district B V)(hc:0≤C)(hx:0≤σ)(hy:σ≤1)(u:ℕ)(r:ℕ):burse u r σ U W≤(9^u*Real.exp 8*C)*burse u r σ B V:= by
   let x:ℝ:=r; have hv:0≤x:=Nat.cast_nonneg _; have ho:= bill_roof hk hb u hx hv; let g:ℝ:=9^u*Real.exp 8*C
   refine (burse_hot u hv hx h he).trans ?_; apply le_trans _ (mul_le_mul_of_nonneg_left ho (show 0≤g by unfold g;positivity)); change _≤ g * _; unfold g
   apply (mul_le_mul (rush_ceil u hv hy) hp (district_pos ..) (mul_nonneg (by positivity) (rush_paid u σ hv))).trans_eq;ring
variable {I:Type}{L:Studio D→ₗ[ℝ] Studio D}{M:Cabin D I G r}{o:Loc G 1}
lemma portfolio (H:Pass D C L) (h:Energy M u σ A) (he:0≤σ)(hp:σ≤1): ∃ B:Cabin D I G r,B.pulse=(fun i=> (M.pulse i).comp L)∧ B.atoms=M.atoms∧(∀ i,Concentrated (B.plus i)∧Concentrated (B.minus i))∧Energy B u σ (9^u*Real.exp 8 * (Fintype.card (Brush D)* C) * A):=by
   let r(i:I):=district (M.plus i) (M.minus i); let U i:= (M.pulse i).comp L; have hc:0≤ C:=zero_le_one.trans H.safe
   choose μ ν hM hN hC P using fun i=>ledger (C*r i) (mul_nonneg hc (district_pos ..)) (U i) (fun p=>by change ‖M.pulse i (L p)‖≤_;rw [h.paper]; exact (record_prices (h.plus i) (h.minus i) (L p)).trans ((mul_le_mul_of_nonneg_left (H.price p) (district_pos ..)).trans_eq (by unfold r;ring)))
   let E := Cabin.mk M.atoms μ ν U; let x:ℝ:=Fintype.card (Brush D);let y:=x*C;have hz:0≤y:= mul_nonneg (Nat.cast_nonneg _) hc;let b:=9^u*Real.exp 8*y; have hb:0≤b:=by unfold b;positivity
   have e i := backed (hM i);have k i:=backed (hN i)
   refine ⟨E,rfl,rfl,fun i=> ⟨hM i,hN i⟩,?_⟩;
   let w (i:I):=(M.atoms i).magnitude * burse u (M.atoms i).length σ (M.plus i) (M.minus i)
   have HZ i: (E.atoms i).magnitude*burse u (E.atoms i).length σ (E.plus i) (E.minus i) ≤ b*w i:= by
       let Hz := exposures (e i) (k i) (h.plus i) (h.minus i) ((hC i).trans_eq (mul_assoc x C (r i)).symm) hz he hp u (M.atoms i).length; rw [show b*w i = _ from (show b*w i=(M.atoms i).magnitude*(b* _) from mul_left_comm ..)];exact mul_le_mul_of_nonneg_left Hz (show 0≤(M.atoms i).magnitude from Finset.sum_nonneg fun _ _=>abs_nonneg _)
   have hv: SumBudget (fun i=> (M.atoms i).magnitude * burse u (M.atoms i).length σ (E.plus i) (E.minus i)) (b*A):= sum_tier ⟨fun i=>mul_nonneg hb (h.income.1 i), h.income.2.1.mul_left b,by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.income.2.2 hb⟩ (fun i=>mul_nonneg (Finset.sum_nonneg fun _ _=>abs_nonneg _) (burse_below u (Nat.cast_nonneg _) (e i) (k i))) HZ
   exact ⟨e,k,hv,P,h.actual⟩
end YM.FormalBulk08.Annex
