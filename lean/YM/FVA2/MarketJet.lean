import YM.FVA2.PricesJet
/-!
# Prolongation in physical coordinate *any* bank, no continuity assumption

Including curves with singular limits, finite-to-µ identities of every
coefficientwise moment.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.FVA2.WorldJet
open Function Filter Set MeasureTheory
open Pert Pert.Position Maxwell Maxwell.Free PositionX
open PositionX.Jet
open MS.Koszul MS.Book MS.Book.Program MS.Book.Convolve
open Clock Score Based PairCoords Modes Paper Trans ColorCode Attend BoxOffice Counterpart
open PowerSeries
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} (F:Labels.Frames G) {d r n:ℕ} {I:Type*} [Fintype I]
local notation "Tt"=> E F d
variable (A: Word (Buffer F d))(Q:Module.Basis I ℂ (E F d))
-- multilinear plus coefficients into Word
abbrev Court (T:Type)[AddCommGroup T][Module ℂ T] (n:ℕ) (Z:Type)[AddCommMonoid Z][Module ℂ Z]:= MultilinearMap ℂ (fun _ :Fin n=> T) Z
def transfer : E F d →ₗ[ℂ] Word (E F d) := LinearMap.pi fun i=> frameWord F A i
def style (i:I): E F d →ₗ[ℂ] Cn:= raiseW ∘ₗ (LinearMap.pi fun u:ℕ=> Q.coord i ∘ₗ frameWord F A u)
def rentF (p:Fin n→I) : Court (E F d) n Cn:= (MultilinearMap.mkPiAlgebra ℂ (Fin n) Cn).compLinearMap (fun i=> style F A Q (p i))
omit [Fintype I] in
lemma real (p:Fin n→E F d)(i:Fin n→I): rentF F A Q i p=∏ x:Fin n,style F A Q (i x) ( p x):= rfl
variable (L: Court (E F d) n Cn)
def drag : Court (E F d) n Cn:= ∑ i:Fin n→ I,( LinearMap.mulRight ℂ (L (Q ∘ i))).compMultilinearMap ( rentF F A Q i )
lemma atDrag (f: Fin n→ E F d) : drag F A Q L f=∑ i:Fin n→ I,(∏ j:Fin n,style F A Q (i j) ( f j )) * L (Q∘i) := by unfold drag; rw [ _root_.sum_apply ]; rfl
-- FrameFlow n acts.T. Need map rank jets identity.Interface (e owner weighed Sect).
lemma insight (p:E F d)(v:ℝ→ Buffer F d) (H:Act n v A): Act n (fun t:ℝ=> frameC F (v t) p) (fun i=> frameWord F A i p) := by
    let x: Buffer F d→ₗ[ℝ] E F d:={ toFun B:= B.val p,map_add' a b:= rfl,map_smul' r a:= rfl }
    let f : Buffer F d→L[ℝ] E F d:= LinearMap.toContinuousLinearMap (E:=Buffer F d) (𝕜:=ℝ) (F':=E F d) x; have he (v:Buffer F d): frameC F v p=f v+p:=add_comm .. ; simp_rw [he,frame_at]; exact ( H.linear (L:=f)).add (Act.static p)
omit [Fintype I] in
lemma node4 (n:ℕ)(x:E F d)(i:I): out ( style F A Q i x ) n= Q.coord i (frameWord F A n x):= by rw [style,LinearMap.comp_apply,saving ]; rfl
omit [Fintype I] in
lemma style_h (p:E F d)(i:I)(v:ℝ→Buffer F d)(h: Act n v A): Act n (fun t:ℝ=>Q.coord i (frameC F (v t) p)) (out (style F A Q i p)) := by rw [funext (fun n=>node4 F A Q n p i)]; exact (insight F A p v h).linear (L:= ((Q.coord i).restrictScalars ℝ).toContinuousLinearMap)
omit [Fintype I] in
private lemma varies (p: Fin n→ E F d)(i:Fin n→I)(v:ℝ→ Buffer F d)(h:Act r v A) : Act r (fun t:ℝ=> ∏ j: Fin n,Q.coord (i j) (frameC F (v t) (p j))) (out (rentF F A Q i p)):= by
    have hv:= forAll Finset.univ (fun j _=>style_h F A Q (p j) (i j) v h); convert hv using 1; ext; rw [ Finset.prod_apply ]; rfl
lemma countr (L: Court (E F d) n ℂ)(u:Fin n→ E F d): L u=∑ i:Fin n→ I,(∏ j: Fin n,Q.coord (i j) (u j))* L (Q ∘ i):= by
    conv_lhs=> rw [ ← funext fun i=> Q.sum_equivFun (u i) ]
    rw [ MultilinearMap.map_sum_finset,Fintype.piFinset_univ ]; exact Finset.sum_congr rfl (fun i _=> L.map_smul_univ ..)
abbrev JetB (v: Bank F d)(L: Court (E F d) n Cn)(t:Test n)(m:ℕ): Prop:= v n t=(coeff m).compMultilinearMap L
-- coordinate lift.
variable {L}
lemma urban (s:Test n)(x:ℝ→ Bank F d)(Z: Word (Bank F d))(v:ℝ→ Buffer F d)(h: Act r v A)(hx: Appears r x Z)(he:∀ m≤r, JetB F (Z m) L s m)(p:Fin n→E F d): Act r (fun t:ℝ=> market F (v t) (x t) n s p) (out (drag F A Q L p)):= by
    let f (i:Fin n→I) (k:ℝ):= x k n s (Q ∘ i); have hu i: Act r (f i) ( out (L (Q∘i)) ):= by refine Act.repairs (show Act r (f i) _ from hx.writes (Pert.Position.Section.mk n (Q ∘ i) s) ) ?_; intro k hk; exact DFunLike.congr_fun ( he k hk ) (Q ∘ i)
    have hl(i:Fin n→I):= beget ( varies F A Q p i v h ) (hu i); obtain hp:= summ Finset.univ (fun i _=> hl i); rw [atDrag ]; convert! hp using 1; ext t; rw [ Finset.sum_apply ]; exact countr F Q (x t n s) (frameC F (v t) ∘ p)
lemma drag_h (s:Test n)(w: Word (Bank F d))(v:Fin n→ E F d) (he:∀ j:ℕ, JetB F (w j) L s j) (j:ℕ): coeff j (drag F A Q L v)= predMarket A w j n s v:= by
   obtain hx:=appears_delay w j; obtain h := Act.swell A (show j≤j from le_rfl); exact (urban F A Q s (delay w j) w (delay A j) h hx (fun i _=> he i) v).trans_at ((appears_market hx h).writes ⟨n,v,s⟩) le_rfl
end YM.FVA2.WorldJet
