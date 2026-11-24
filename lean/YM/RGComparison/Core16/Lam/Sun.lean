import YM.RGComparison.Core16.Lam.Eaves
/-!
# Visible Θ Score API, REAL period and gauge rotations
Still need derivative budgets on physical transport residual kernel. Don't switch paths! Carry Q calibration and AP per-parameter IR of costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lam
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity Finset
open Precision Push.BetaTransport Next.Fluctuations Pressure
open Parcel Parcel.Oven Forge.Hut
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side} {P: Patch} {K:KernelChoices} {d:f.val=c.val*P.L.val}
    {W:Oven P}{X:Shelf G (PlaqAxes⊕Axis) W.Xways}
variable (hW: Parcel.Oven.Offers W X K)(B:Forest (StepData.mk P K d).ratio)(H: Bid.Larger (G:=G) (StepData.mk P K d))
local notation "S"=> StepData.mk P K d
local notation "U"=> gear S B X

abbrev feel (K:KernelChoices) (v:G.Color) (x:G.El) := line1 (Lam.over K (G.mat x)) 0 v
abbrev peak (K:KernelChoices)(v w:G.Color)(x:G.El):= lend (Lam.over K (G.mat x)) v w
structure Seal (G:Gauge)(K:KernelChoices)(c:ℝ): Prop where
    floor : 0<c
    hot (v : G.ColorIndex)(x:G.El):|feel K (colors G v) x| ≤ c
    ticket (v w:G.ColorIndex)(x:G.El) : |peak K (colors G v) (colors G w) x| ≤ c
lemma seals (G:Gauge)(K:KernelChoices):∃ c:ℝ,Seal G K c:=by
    choose p hp using fun v:G.ColorIndex=> (havenreal (f:=feel K (colors G v)) ((swirl K (colors G v)).continuous.comp G.continuous_mat)).cost
    choose q hq using fun u:G.ColorIndex × G.ColorIndex=> (havenreal (f:=peak K (colors G u.1) (colors G u.2)) ((tilt K ..).continuous.comp G.continuous_mat)).cost
    let A:=∑ i,|p i|; let B:=∑ i,|q i|
    refine ⟨A+B+1, ?_⟩; constructor
    · unfold A B; positivity
    · intro v x; apply (le_trans (b:=A) ?_ (by unfold B; linarith only [show 0≤∑ i,|q i| from sum_nonneg fun i _=>abs_nonneg _])) ; exact (hp v x).trans ((le_abs_self _).trans (single_le_sum (f:=fun i=>|p i|) (fun i _=>abs_nonneg (p i)) (mem_univ _)))
    intro v w x; refine (le_trans (b:=B) ?_ (by unfold A; linarith only [show 0≤∑ i,|p i| from sum_nonneg fun i _=>abs_nonneg _])); exact (hq (v,w) x).trans ((le_abs_self _).trans (single_le_sum (f:=fun i=>|q i|) (fun i _=>abs_nonneg (q i)) (mem_univ _)))

variable (i j:Operand G c) {L:ℝ}(Z:Seal G K L)

-- digits relative template on uptime
-- shapePsi into collector in ColorBasis chart. spur marker arity recipes realized from BOOL tuple.
-- stencil order arbitrary.
abbrev harp (X:Shelf G (PlaqAxes⊕Axis) W.Xways)(i:Operand G c) := stock W X (gear S B X) (.inr i.1)
-- abbreviation S hidden across binder include S.K d issues name?

-- primitive material with receipts before period
abbrev tileΨ (W:Oven P)(K:KernelChoices)(a : Axis×G.ColorIndex):= plate W K (colors G a.2) a.1
abbrev heatΨ (W:Oven P)(K:KernelChoices)(a : Bool× Axis× G.ColorIndex × G.ColorIndex):= if a.1 then tops W K (colors G a.2.2.1) (colors G a.2.2.2) a.2.1 else 0
abbrev profileDatum (i:Operand G c) : Axis× G.ColorIndex := (i.1.2,i.2)
abbrev tier (i j:Operand G c) : Bool × Axis × G.ColorIndex × G.ColorIndex:= (decide (i.1=j.1),i.1.2,i.2,j.2)

variable {i j}
abbrev b0 {W: Oven P} (X:Shelf G (PlaqAxes⊕Axis) W.Xways):= Push.AbsoluteSums.Animals.ballCost X.sector.b * X.sector.K
include H hW
lemma housed (i:Operand G c): ((U).soil (.inr i.1)).card≤b0 X ∧ celery (harp B X i) ((U).soil (.inr i.1)) X.Q:=by
   let V:= U; let hp:= paint S B hW H
   refine ⟨price_cover (loc:=V.loc) ((hp.tickets 0 ⟨le_rfl,hW.good.thick.2.1.le⟩).core) _ _,fun y=>?_⟩; unfold harp Lam.stock; rcases h:(U).stem (.inr i.1) y with _|j
   · exact (show ‖(0:G.Color)‖ ≤ X.Q from norm_zero.trans_le hW.good.thick.1.le)
   exact hp.thread _ _ _ h -- order
include Z

-- Verifies Full Lip Ticket: do all roots at high AP order using same Θ belief. Product COval uses stamp operation at θ. Identity applies even though `scoop F` not analytic globally.
omit H hW in
private lemma slope_ticket (i)(x:Sky G B.Free)(t:(S).Choices): |raise S (compass i) (fire S B t x)| ≤ L := by
    rw [(sensor S i i _).1]; exact Z.hot ..
omit H hW in
private lemma top_ticket (i j:Operand G c)(x:Sky G B.Free)(t:(S).Choices): |tip S (compass i) (compass j) (fire S B t x)| ≤ L := by
    rw [(sensor S i j _).2]; split; exact Z.ticket ..; rw [abs_zero]; exact Z.floor.le
variable {φ: News G c→ℝ} (hφ:ContDiff ℝ ∞ φ) {E:ℝ} (he: ∀ t (x:Sky G B.Free), |φ (fire (StepData.mk P K d) B t x)| ≤ E)
include hφ he
omit Z in
lemma pastry {g:ℝ}(g':amen X g): Envelope (scoop S B φ g) := ⟨(turned_bill S B hW H hφ g').1,E,fun x=> bounded S B hW H g' (fun t=> he t x)⟩
omit hφ he Z

variable {g:ℝ}(g': amen X g)(x:Sky G B.Free)
include g' in
private lemma stamped (hg:0<g)(i:Operand G c)(z:crisp (X.δ/2) ((U).soil (.inr i.1)) x)(t:(S).Choices) : raise S (compass i) (fire S B t x)= tileΨ W K (profileDatum i) (g • book (harp B X i) g x) := by
    have hx:= chooses hW B H.1 i.1 x hg g' (crisp_negligible _ _ (half_le_self hW.good.extent.1.le) (le_refl _) z) t
    rw [(sensor S i i _).1]; exact congr_arg (fun x:G.Mat=> line1 (Lam.over K x) 0 (colors G i.2)) hx -- section? macro
include Z
lemma visor (i:Operand G c): Visible X (tileΨ W K (profileDatum i)) (scoop S B (raise S (compass i))) (harp B X i) (b0 X) L := by
     refine ⟨fun g hg=> pastry hW B H (raise_hot S _) (fun t x=>slope_ticket B Z i x t) hg, fun g hg x=> bounded S B hW H hg (slope_ticket B Z i x), (U).soil (.inr i.1), (housed hW B H i).1,(housed hW B H i).2,fun g hg he x hx=> Lam.pure S B hW H hg (stamped hW B H hg x he i hx)⟩ -- args

lemma hued (i j): Visible X (heatΨ W K (tier i j)) (scoop S B (tip S (compass i) (compass j))) (harp B X i) (b0 X) L:= by
    refine ⟨fun g hg=> pastry hW B H (tip_hot S ..) (fun t x=>top_ticket B Z i j x t) hg, fun g hg x=> bounded S B hW H hg (top_ticket B Z i j x), (U).soil (.inr i.1), (housed hW B H i).1,(housed hW B H i).2,fun g hg he x hx=> Lam.pure S B hW H hg (fun t=>?_)⟩
    have hv:= chooses hW B H.1 i.1 x he hg (crisp_negligible _ _ (half_le_self hW.good.extent.1.le) (le_refl _) hx) t; rw [(sensor ..).2]; unfold heatΨ tier; split
    next H => split
              next h=> exact congr_arg (fun z:G.Mat=> lend (Lam.over K z) (colors G i.2) _) hv
              next h=> exfalso; apply h; dsimp only; simp only [H,decide_true]
    next h=> split
             next he=> simp [h] at he
             next he=> rfl

abbrev hearth (W:Oven P)(K:KernelChoices)(a:(Axis× G.ColorIndex)× Axis× G.ColorIndex) := Silk.unite (tileΨ W K a.1) (tileΨ W K a.2)
set_option maxHeartbeats 600000 in
lemma fusion (i j): Visible X (hearth W K (profileDatum i,profileDatum j)) (scoop S B (raise S (compass i)* raise S (compass j))) (Silk.woven (harp B X i) (harp B X j)) (2*b0 X) (L^2):= by
    have he t (x:Sky G B.Free) : |(raise S (compass i)*raise S (compass j)) (fire S B t x)| ≤ L^2:= by rw [Pi.mul_apply,abs_mul,sq]; exact mul_le_mul (slope_ticket B Z i x t) (slope_ticket B Z j x t) (abs_nonneg _) Z.floor.le
    let v(i: Operand G c):=(U).soil (.inr i.1); obtain ⟨h,ht⟩:=housed hW B H i; obtain ⟨hh,hJ⟩:=housed hW B H j
    refine ⟨fun g hg=> pastry hW B H ((raise_hot S _).mul (raise_hot S _)) he hg, fun g hg x=> bounded S B hW H hg (fun t=> he t x), v i∪v j, (Finset.card_union_le _ _).trans (le_trans (Nat.add_le_add h hh) (Nat.le_of_eq (two_mul ..).symm)), Silk.coveredBy _ _ ht hJ,fun g hg he x hx=> Lam.pure S B hW H hg (fun t=>?_)⟩
    simp_rw [Pi.mul_apply]; exact congr_arg₂ _ (stamped hW B H hg x he i (crisp_negligible _ _ le_rfl Finset.subset_union_left hx) t) (stamped hW B H hg x he j (crisp_negligible _ _ le_rfl Finset.subset_union_right hx) t)
end YM.RGComparison.Core16.Lam
