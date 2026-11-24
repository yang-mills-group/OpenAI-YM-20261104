import YM.WilsonCoeffUV.MultiUV
/-!
# Covariance of the mixed formal algorithm (signed axes)

Roll only unmasked formal kernels. Position gears use all root labels through
capture; not an equivariance of overlapping IR sectors. Signature useful against
physical stencil moving charts. This proof includes Ward, numerator reset; no
cost for arbitrary exchanges of UV curvature-lift choices.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Motion
open Wheel.ScaleS Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost Physical
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Wheel.Flooring Ticket
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι:Type}{S:Finset ι}{E:Credit}{m b N e i a:ℕ}{G:Gauge}{A:Levels G}{R:Realm G (e+1) E}{Ñ: ChartRatio G}{T:ι→SealR G}{n:Side}{σ:Signed}{D K k:ι→ℕ}
variable [DecidableEq ι]
lemma mapEquation {U V:Type}[CommRing U][CommRing V](R:Finset ι→U)(L:Finset ι→U)(T:U→+*V)(h:Equation R L): Equation (fun i=>T (R i)) (fun i=>T (L i)) := by
   refine ⟨by simp only [h.1,map_one],by simp only [h.2.1,map_zero],?_⟩; funext s; rw [dial,← map_nsmul,show s.card • R s= _ from congr_fun h.2.2 s,shells,map_sum]; exact Finset.sum_congr rfl fun i _=> by simp only [dial, map_mul,map_nsmul]

def swish (σ:Signed)(X:Case D): Case D:=fun i=> spinV σ _ (X i)

def turnsO (σ:Signed)(X Y:family G D):Prop:=∀ (S:Finset ι)(n:Side)(A:Case D),rollTest (readO A (Y S) n) (readO (swish σ A) (X S) n) σ 0
lemma ordinary_spin {X Y:family G D}(p:Eu k X)(q:Eu k Y)(v:X ∅=0)(w:Y ∅=0)(r:turnsO σ X Y): turnsO σ (levelsO X) (levelsO Y) :=by
    intro S n A Z I Q T T' h
    have he:=levels_exp X p v (swish σ A) n; have hx:=levels_exp Y q w A n; let K:= train (spool T); let L:= train (spool T'); let P:= (fun j=>K (readO A (Y j) n)); let Q':=fun j=> L (readO (swish σ A) (X j) n); have hf:P=Q':=funext fun j=> r j n A h
    have hL:=mapEquation _ _ K hx; have hR:=mapEquation _ _ L he
    change Equation _ Q' at hR; rw [←hf] at hR; exact congr_fun (Equation.prod_u _ _ _ hL hR) S
lemma reserve_spin {X Y:family G D}(p:Eu k X)(q:Eu k Y)(v:X ∅=puff D G)(w:Y ∅=puff D G)(r:turnsO σ X Y): turnsO σ (reverseO X) (reverseO Y) :=by
    intro S n A Z I Q T T' h
    have he:=levels_log X p v (swish σ A) n; have hx:=levels_log Y q w A n; let K:= train (spool T); let L:= train (spool T'); let P:= fun j=>K (readO A (Y j) n); let Q':=fun j=> L (readO (swish σ A) (X j) n); have hf:P=Q':=funext fun j=>r j n A h
    have hL:=mapEquation _ _ K hx; have hR:=mapEquation _ _ L he
    change Equation Q' _ at hR; rw [← hf] at hR; exact congr_fun (Equation.unique _ _ _ hL hR) S
omit [DecidableEq ι] in
lemma verse_spin {X Y:family G D}(p:Eu k X)(q:Eu k Y)(r:turnsO σ X Y)(u:m<N)(g:G.Simple)(w:LocalRatio Ñ): turnsO σ (fun i=>verseI A Ñ m N (mass k i) (X i)) (fun i=>verseI A Ñ m N (mass k i) (Y i)):=by
    intro S n F
    let L:= ll A m; let K:=A.clock.kernel; let T:=n*L.L; let V:=freeForms A N (m+1); let Y':=freeForms A N m; let M:= roam A N m; let X':= (story A Ñ N (m+1)).1 T; let b:=ratioHigh A Ñ N m; let J:= mass k S; let s:=stepAt L K n; let f:=xree L K n; let R:= reed (R:=ℝ) s f V (M n) Ñ X' J; let Q':=pPly F S ((Y S).1 T); let P:=pPly (swish σ F) S ((X S).1 T)
    have he := (old A Ñ g w N (m+1) u).basis T; have hp:shellK J P:= ply_shell _ ((p _).span _); have hx:shellK J Q':= ply_shell _ ((q _).span _)
    have h (U: Era G (Pen D S))(H: Case D) : readO H (verseI A Ñ m N J U) n = flash (Blue.mix b (R (pPly H S (U.1 T)))):=by
        unfold readO pPly; apply congr_arg _; change ply _ (Blue.mix b (reed s f V (M n) Ñ X' J (U.1 T)))=_; rw [ply_mixX]; exact congr_arg _ (reed_maps s f V (M n) J (touch H S).toLinearMap)
    rw [h,h]; intro M0 N0 z x x' hv; change train _ (flash (Blue.mix b (R Q')))=_; refine rollMix ?_ (reed_band s f V (M n) J he.lamp w hx) (reed_band s f V (M n) J he.lamp w hp) (back_cc (angle_tilt (A:=A) g w u)) hv
    apply reed_turn s f V (M n) Y' he.lamp he.stem w _ hx hp (A.blocks m 0).branches (age_sym ..) he.shape (fun i=> ply_pure _ ((q S).pale _ _)) (fun i=>ply_pure _ ((p S).pale _ _)) ((cond_laws A m N).1 n T rfl) (horizon_step A m N u n T rfl) he.valid
    rw [show s.ratio.embed 0=(0:Site T) from map_zero (s.ratio.root)]; exact r S T F
lemma logged {X Y:family G D}(p:Eu k X)(q:Eu k Y)(x:X ∅=0)(y:Y ∅=0)(t:m<N)(g:G.Simple)(u:LocalRatio Ñ)(r:turnsO σ X Y): turnsO σ (logO A Ñ m N X k) (logO A Ñ m N Y k):= reserve_spin (vol A Ñ m N X k t g u p) (vol A Ñ m N Y k t g u q) (edV_e _ _ _ _ X _ t g u) (edV_e _ _ _ _ Y _ t g u) (verse_spin (placedO _ p) (placedO _ q) (ordinary_spin p q x y r) t g u)

end YM.WilsonCoeffUV.Wheel.Motion
