import YM.LocalLTE.Pond.Mint
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes
variable {G}
open Extra.Iteration Urns
variable {t σ C' Λ Δ α k κ a v w u:ℝ} {c:Clip} {L:Side} {p:BudgetPoint} {d N:ℕ}
variable {R:PathData G}(hR:R.Bounds c σ C' Λ) (hv : Width p c σ)(hG:G.Simple)(hn:20<n.val)(hg:32*p.B<n.val) (ht:p.B=Pressure.radiusB t) (hC:p.threshold=Pressure.temp t) (he:p.threshold ≤2*Pressure.fiery G t L)(hx:1 ≤ betaF G t L) (hb:3 ≤ p.B)(hk:Reliable G κ k) (hd:WilsonStartup.Decent c p)
-- Numerics.After.D.D F.bore universe all.Current.True accuracy.
variable (X:Listing G n) (g:Source G n) (P0:ℕ→Pot G n)(V:Tour X d)
variable {e:ℝ}
section energies
variable {ι:Type} {U: ι → RegularAddress n} {P Q:ι→ Config G n→ℝ}
lemma Stocked.cheaper (h: Stocked p U P a) (hv:a≤v) : Stocked p U P v := by obtain ⟨f,h,hF⟩:=h; exact ⟨f,h,fun x=>budget_loosen (hF x) hv⟩
lemma Stocked.minus (h:Stocked p U P a)(hk:Stocked p U Q w): Stocked p U (P-Q) (a+w) :=by
   obtain ⟨f,h,hF⟩:= h; obtain ⟨g,hg,hG⟩:=hk; refine ⟨f+g,fun i=>⟨reg_sub (h i|>.1) (hg _|>.1), VerifiedReset.sup_sub (h _|>.1) (hg _|>.1) (h _|>.2) (hg _|>.2)⟩,fun i=> ?_⟩
   convert budget_plus (hF i) (hG i) using 2 with j; simp only [Pi.add_apply,BudgetPoint.mass,mul_add]; split <;> ring
lemma Stocked.joins (h:Stocked p U P a)(hk:Stocked p U Q w): Stocked p U (P+Q) (a+w) :=by
   rw [←sub_neg_eq_add]
   apply h.minus; obtain ⟨f,h,hF⟩:= hk; refine ⟨f,fun i=>?_,hF⟩
   rw [Pi.neg_apply,← neg_one_smul ℝ]; refine ⟨CouplingShape.reg_scale _ (h _|>.1),?_⟩; have he:= CouplingShape.sup_scale (-1) (h i|>.2); rw [abs_neg,abs_one,one_mul] at he; exact he
lemma Stocked.rotation (h: Stocked p U P a): Stocked p (Song.revolve U) (Song.choir P) (turnFee p*a):= by
    obtain ⟨f,h,hF⟩:= h; let t:= turnFee p; let d:= Song.Rim n; let k(j:Seat n ×ι):= d*(t*f j.2)
    have hz:= (turnFee_pos p).le; have ht:= Song.rim_nn n; refine ⟨k,fun i=>?_,fun z=>?_⟩
    · obtain ⟨θ,i⟩:=i; have he:= CouplingShape.sup_scale (Song.Rim n) (Song.transSup θ (h i|>.1) (h i|>.2)); rw [abs_of_nonneg ht] at he; exact ⟨CouplingShape.reg_scale _ (θ.regular (h _|>.1)),he⟩
    have he :0 ≤ a:= Cost.nonneg (hF 0)
    rw [show turnFee p*a=(Fintype.card (Seat n):ℝ)*(d*t*a) by rw [← mul_assoc, ← mul_assoc,Song.balance]; simp only [one_mul]; rfl]
    refine Cost.product (Cost.finite _ (show 0 ≤ d*t*a from mul_nonneg (mul_nonneg ht hz) he)) fun i=> ?_
    let y:= StepData.sendSites i.1 i.2
    have hh j : (Song.revolve U (i,j)).site=z ↔ (U j).site=y.symm z:= y.apply_eq_iff_eq_symm_apply
    have hv j : coverNumber p.B (Song.revolve U (i,j)).support = coverNumber p.B (U j).support := Seat.visit_count i _
    convert Cost.scale (hF (y.symm z)) (d*t) (mul_nonneg ht hz) using 2 with j; dsimp only [k]; simp_rw [hh,BudgetPoint.mass,hv]; unfold d t; split <;> ring
end energies
open Averaging
variable (α) {g0:Source G n}{m:ℕ}
local notation "δE"=> Averaging.delta (X.read g)
local notation "δ₀"=> Averaging.delta (X.read g0)
local notation "η"=> Price.vane R c p X d V κ α (Averaging.delta (X.read g0)) m g0.logRead
variable (h:Meadow.Budget p X.reg g.logRead a)(hw:Meadow.Budget p X.reg (g.logRead-g0.logRead) w)(hW:Portrays X d κ m g0.logRead V)
lemma at_delta (a: Source G n): Averaging.delta (X.read a)=delta (X.read (Magnet.seed a.logRead)):= rfl
include hG h hw
lemma levy : p.threshold^2*|δE- δ₀| ≤ w ∧ p.threshold^2*|δ₀| ≤ a+w:= by
    have he:= Urns.minus_cost h hw; rw [sub_sub_cancel] at he
    rw [Price.at_delta X g,Price.at_delta X g0,← Magnet.detects hG h he]; exact ⟨delta_bound hG (Magnet.promoted hw), delta_bound hG (Magnet.promoted he)⟩
variable (ht :p.B=Pressure.radiusB t)
include hR hv hn hd hg hC he hx hb hk ht hW
lemma emit (hM: Merchant G L κ p.order p.power m d t)(hF:Found G L κ p.order p.power m t) (hh:32*d<n.val) : let c' :=vest p δ₀ α (betaF G t L ^ Urns.dust m) (a+w) c G σ C'
    Stocked p (Price.tubeX R p X) (Collection.archive X R c g α δE-η) ((Price.tH p*regularNeed G p c σ C' 0 w)+c'):=by
     intro c'; have hy:= Price.levy hG X _ h hw
     have hp:= Urns.minus_cost h hw; rw [sub_sub_cancel] at hp
     have hx':= Price.crown hR hv hG hn hg ht hC he hx hb hk hd X g0 V m hM hF hp hW hh α (Averaging.delta (X.read g0))
     let Δ':=δE-δ₀; let F:= archive X R c g α δE; let E:=archive X R c g0 α δ₀; let K:= Magnet.seed (g.logRead-g0.logRead)
     have hz:F-E= archive X R c K 0 Δ':= funext fun i=> archive_sub (Magnet.promoted (X:=X) h).regular (Magnet.promoted (X:=X) hp).regular _ _ _ _ _ -- edit
     have he : Stocked p (Price.tubeX R p X) (F-E) _:= hz.symm ▸ (Price.dock hR hv hG hn hd X K 0 Δ' (show Meadow.Budget p X.reg K.logRead w from hw) hy.1)
     change Stocked _ _ (F-η) _; rw [show F-η=(F-E)+(E-η) from by abel]; exact he.joins hx'
end YM.AnalyticBridge.VerifiedReset.Collection.Price
