import YM.RGComparison.Core16.Lam.Expo
/-!
# At TORUS, replication costs after fixing an upper ratio. G_f period bigger.

After KernelFing screwwise forecast, moment occupations through narrower envelope still uploads into every previously used torus window. Yearly V-Orientation genuinely consequences (use H, H' respectively). NOW Heal estimates actually queried by the ω.Hat recipe at large to small. No decision to discard terms with empty masks across unrelated reps. This is POST-Fk coefficient comparison on periodic grids, using Overset Reynolds. V none gauge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lam
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity Finset
open Precision Push.BetaTransport Next.Fluctuations Pressure
open Parcel Parcel.Oven Forge.Hut Silk Stage Push.Uniform Push.AbsoluteSums.Animals
open PhysicalNext.Repeat Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology ContDiff PowerSeries BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {C F c f:Side} {P: Patch} {K:KernelChoices} {d:f.val=c.val*P.L.val} {E:F.val=C.val*P.L.val} {a:ℕ}
    {W:Oven P}{X:Shelf G (PlaqAxes⊕Axis) W.Xways}
variable (hW:P.Branches K G) (pW:Parcel.Oven.Offers W X K)
    {B : Forest (StepData.mk P K d).ratio} {B' : Forest (StepData.mk P K E).ratio} (hA:C.val=c.val*a) (hB:2≤c.val) (H: Bid.Larger (G:=G) (StepData.mk P K d)) (H' : Bid.Larger (G:=G) (StepData.mk P K E))
local notation "S"=> StepData.mk P K d
local notation "K0"=> gear S B X
local notation "A0"=> StepData.mk P K E
local notation "K1"=> gear A0 B' X

variable (V:Pinnage (zoom E d hA) B' B)(h : 2* X.sector.b<f.val)
set_option quotPrecheck false
local notation "∂F"=> projectStem (zoom E d hA) V
local notation "∂L"=> (show c.val∣C.val from ⟨a,hA⟩)

-- lift arbitrary Basis.Handle. Use trial plane wave toll.
def heave {C c:Side}(hd:c.val∣ C.val)(i:Operand G C): Operand G c:= (((splitter hd i.1.1,i.1.2):Bond c),i.2)
local notation "T₀"=> heave (G:=G) ∂L

include V h hB
lemma incline (i:Operand G C) : harp B X (T₀ i)=cover (harp B' X i) ∂F:= by
     let f:=projectStem (zoom E d hA) V
     have he: ∀ y,((K0).stem (.inr (T₀ i).1) y) = Option.map f ((K1).stem (.inr i.1) y):= by
        intro j
        let n:= plough (zoom E d hA) ∂L
        exact Eq.symm ((ministry K hA hB V h 0 |>.stem (.inr i.1) j)) -- h needed!
     funext p; unfold harp stock cover Function.comp; dsimp only; rw [he p]; cases (K1).stem (.inr i.1) p <;> rfl

include H H' pW V hB h
variable {L:Type}[Fintype L]{u:Stuff G B'.Free L}
    {r m j:ℕ}{y:ℝ}(hp:0≤y)(ht:Reel X y r r){I:Finset B'.Free}(hT:celery u I X.Q)(he:j≤r)(x:Site F) (ψ:(L→G.Color)→ℝ)
include hp ht
include hT x he in
lemma cover_earn (hu:∀ i∈I,m+ separation x (Hut.pad («S»:=StepData.mk P K E) B' i) ≤ f.val/3): |nth j (stamps K1 u ψ)-nth j (stamps K0 (cover u ∂F) ψ)| ≤ (y/costLamp X m)*lint ψ 0 r X.Q:=by
    let s:= ∂F; let R:=price K1; let Q v:= unfoldR (price K0) s v
    let d:= R-Q
    change |nth _ (owner _ _ _)-nth _ (owner _ _ _)|≤ _; rw [nth,nth,←map_sub, show owner (cover u s) ψ (price K0)= owner u ψ Q from congr_arg (day · 0) (funext fun k=> night_reels (u:=[]) s u ψ (price K0) k), ← owner_sub]; apply owner_cost (div_nonneg hp coin_pos.le) pW.good.thick.1.le hT he
    intro i hi j hj v; rw [nth,Pi.sub_apply,map_sub]; apply stencils K hA hB V pW H' H h 0 (fun i=> ?_) r r y ht (weave u v) ((length_bound u v).trans hi) _ j hj; rotate_left
    · intro i hi; rw [add_comm]; exact hu _ (rails u v hT i hi)
    simp [pW.good.thick.1.le]
-- convenience stock root. costs before selecting p'.
omit H H' hB V h ht pW hp in
lemma extent' (i:Operand G C){r}(hw:separation x (hold A0 i.1.1)+m+ X.sector.b ≤r) :∀ j∈(K1).soil (.inr i.1), m +separation x (Hut.pad («S»:=StepData.mk P K E) B' j) ≤ r:= by
    intro j hj; let v:= hold A0 i.1.1; let y:= Hut.pad («S»:=A0) B' j; have hv:separation v y≤ X.sector.b:= (member ..).1 hj; have hh:= separation_triangle x v y; change separation x v + _ + _ ≤ r at hw; change m+ separation x y ≤ _; omega

omit hp ht H H' pW V h hB in
lemma robot_difference {V U W Z:Roll}{j r:ℕ}(hj:j≤r){D₁ D₂ E₁ E₂:ℝ}
    (hR:∀ i ≤ r, |nth i V| ≤ D₁)(hV:∀ i ≤ r,|nth i U-nth i V| ≤ E₁)(hW:∀ i ≤ r,|nth i W| ≤ D₂)(hZ:∀ i ≤ r,|nth i W-nth i Z| ≤ E₂):
    |nth j (U*W)-nth j (V*Z)| ≤ (r+1:ℝ)*(D₁*E₂ + E₁* D₂):= by
    have hx(i:ℕ) {P Q:Roll}: nth i (P-Q)=nth i P-nth i Q:=map_sub ..
    rw [←hx,show U*W-V*Z= V*(W-Z)+(U-V)*W from by ring]; unfold nth; rw [map_add]; refine (abs_add_le ..).trans ((add_le_add (robot _ (fun i h=>hR i (h.trans hj)) (fun i h=> hx i ▸ hZ i (h.trans hj))) (robot _ (fun i h=> hx i ▸ hV i (h.trans hj)) (fun i h=> hW i (h.trans hj)))).trans ?_)
    rw [← mul_add,Nat.card_antidiagonal]; apply mul_le_mul_of_nonneg_right ?_ (add_nonneg (mul_nonneg ((abs_nonneg _).trans (hR j hj)) ((abs_nonneg _).trans (hZ j hj))) (mul_nonneg ((abs_nonneg _).trans (hV j hj)) ((abs_nonneg _).trans (hW j hj))))
    push_cast; gcongr
end YM.RGComparison.Core16.Lam
