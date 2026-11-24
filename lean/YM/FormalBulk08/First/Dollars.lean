import YM.FormalBulk08.First.Ranks
import YM.FormalBulk08.Hay.Greet

/-! Geometric presentation for USE at real steps. This costs `loopCap` IN
 addition to polynomial z^C. Do not use such an implementation of
 converting to paths in the inherited repeated estimates. Use Pot and PrintK
 without this cost in EACH formal operation; at comparing into actual
 support-weighted reps spend the additional `p_i^geo` cost, here bounded
 by `(1+clock.monitor)`. Sends no \(\theta\)-dependent ratio into L. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.First
open Function Filter Set MeasureTheory Lattice RG Exterior Wilson Precision
open Stationary hiding shine Rays
open scoped Topology BigOperators ENNReal Matrix ContDiff Classical
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa Broc City Cork Lotus Shore Gorge Laurent Bloch Flat Next.Free Bank Wine Dove North
open Next.Foundations PhysicalNext.Repeat.Legato
variable {G:Gauge}{K:KernelChoices}{ρ:ChartRatio G}{A:Levels G}{C:Family G}{W:Borough.Window G K}
structure Margins (G:Gauge)(p:Stage)(E:ℕ)(σ μ R:ℝ):Prop where
   positive:0≤R
   size: 0<μ
   buys :∀ (X:PathData G) Λ,X.Bounds p.clip p.width p.paths Λ →0≤Λ→∃ T:Pot G,Hay.Troupe T p.clip X ∧ Broc.Fits T E μ ((1+Λ)*R) ∧∀ (Y:Pot G) C, Broc.Fits Y E σ C→ Temper Y E → Sane Y E → (∀ j≤2,Y j=T j)→∃ P,PrintK (Y-T) E 3 (E-2) μ ((C+(1+Λ)*R)*R) P
lemma margins_exist (p:Stage)(hG:G.Simple)(E:ℕ)(he:2≤ E){σ:ℝ}(h:0<σ):∃ μ R,Margins G p E σ μ R:= by
    obtain ⟨δ,d,K,T,h1,h2,h3,h4,B,h5,P⟩:= Hay.leaf_up hG p.width_pos h p.paths_pos.le p.clip.direct p.clip.quadratic_pos.le E he
    let μ:= min δ d; let R:=max K (max T B); have hr:K≤ R:=le_max_left ..; have hb: T≤R:=le_trans (le_max_left ..) (le_max_right ..);have hX:B≤R:=le_trans (le_max_right ..) (le_max_right ..); have hz:0≤R:=h5.trans hX;refine ⟨μ,R,hz,lt_min h1 h2,fun X Λ hx hΛ=>?_⟩
    obtain ⟨Y,hY,A,Q⟩:=P _ le_rfl X _ hx; have hv: K+Λ*T ≤ (1+Λ)*R:=by rw [add_mul,one_mul];gcongr
    refine ⟨Y,hY, A.mono (min_le_left ..) hv,fun T C k c d w=>?_⟩; obtain ⟨P,hP⟩:=Q T _ k c d w; exact ⟨P,hP.mono (min_le_right ..) (mul_le_mul (add_le_add_right hv _) hX h5 (add_nonneg k.money (by positivity)))⟩
def prints (G:Gauge)(p:Stage)(E:ℕ)(σ:ℝ):ℝ:= if h:G.Simple ∧ 0<σ ∧ 2≤ E then (margins_exist p h.1 E h.2.2 h.2.1).choose else 1
def money (G:Gauge)(p:Stage)(E:ℕ)(σ:ℝ):ℝ:= if h:G.Simple∧ 0<σ∧ 2≤ E then (margins_exist p h.1 E h.2.2 h.2.1).choose_spec.choose else 1
lemma sold (p: Stage)(E:ℕ)(hE:2≤E)(hs:G.Simple)(σ:ℝ)(h:0<σ): Margins G p E σ (prints G p E σ) (money G p E σ):= by rw [prints,money,dif_pos ⟨hs,h,hE⟩,dif_pos ⟨hs,h,hE⟩]; exact (margins_exist p hs E hE h).choose_spec.choose_spec
open Borough RG.Supply Push.PriceCompiler
def PrizeK (p: Stage)(G:Gauge)(E:ℕ)(σ:ℝ):ℝ:= max |money G p E σ| |(prints G p E σ)⁻¹|
structure Dahlia (A:Levels G) (σ:ℕ→ℝ):Prop where
   boots : ∀ j E, E≤ A.clock.J (j+1) → PrizeK (A.params j) G E (σ (A.clock.J j)) ≤ ageZ (A.clock.hatBeta j)
lemma till_boost {Y:RG.Supply.Sheet G}{P:Rolls Y}{T:Protection P} (V:Delays T)(σ:ℕ→ℝ):∃ Z:Delays T,DelayLe V Z ∧∀ X:Delays T,DelayLe Z X→∀ (B:Bar X)(L:Wait B)(A:Levels G), Paid L A→ Dahlia A σ := by
   choose C c H using fun j:ℕ=> bddBill (fun x:Fin (j+1) × Fin (j+1)=>PrizeK (Y.profile x.1.val) G x.2.val (σ x.1.val))
   obtain ⟨Z,h,-,P⟩:=delay_extra V (fun j x=> C j ≤ ageZ x) (fun _ _ _=>True) (fun j=> age_fly.eventually_ge_atTop _) (fun _ _=> Filter.Eventually.of_forall fun _=> trivial)
   refine ⟨Z,h,fun X v B L A a=> ⟨fun j E hj=>?_⟩⟩
   have hx:= (P X v).1 _ _ (a.pays j); rw [show A.params j=Y.profile (A.clock.J j) by change A.clock.stage _=_; rw [a.stage]]; refine le_trans ((le_abs_self _).trans (H (A.clock.J (j+1)) (⟨_, Nat.lt_succ_of_le (A.fits.mono (Nat.le_succ j))⟩,⟨_,Nat.lt_succ_of_le hj⟩))) hx
-- affordable extra
lemma finances_exist (hG:G.Simple) (b:ℝ)(p:0<b)(e:ℕ)(he:4≤e) : ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book),Nonempty (Spec.Final C f T)∧ C.Makes∧ Spec.Calibrated C∧ C.path.levels.clock.kernel.penalty=b ∧ UVExtension.Oasis.Floral (hG:=hG) C ∧ (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧ (∀ d k:ℕ,∀ᶠ n in atTop,∀ r:ℕ,∀ v:Fin r→ C.book.Token,(∀ i,(v i).1≤ d) →∃ g,UVExtension.Poppy.Margins C r n k v g) ∧ Provenance G C (chart G) ∧ Evergreens C.path.levels.clock.kernel Spigot.herald (Labels.frames G).level (hol G) (chart G) (windowBasis G _) C.path.levels ∧ C.path.levels.clock.J 0=e∧ Dahlia C.path.levels (windowBasis G C.path.levels.clock.kernel).width:= by
   refine achievable hG b p e he (fun L=>Dahlia L (windowBasis G L.clock.kernel).width) (fun K _ Y hb P Z V=>?_); obtain ⟨W,H,V⟩:= till_boost V (windowBasis G K).width; refine ⟨W,H,fun D H B I A g=>?_⟩; rw [g.kernel,hb]; exact V D H B I A g
end YM.FormalBulk08.First
