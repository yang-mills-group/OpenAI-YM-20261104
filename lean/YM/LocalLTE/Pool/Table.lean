import YM.LocalLTE.Pool.Paint
/-! # Boundary surface payments on same theory. Extra regular stencil tags; hail projection and rotate. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Frost
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open AnalyticBridge VerifiedReset Collection Price
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf Urns
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
open Start Animals
open Padded Ovens Pipes
variable {x t :ℝ} (M:ℕ) {κ k:ℝ} (p: BudgetPoint)(c:Clip)
abbrev Card (M:ℕ)(n:Side):= Fin (M+2)×Key n
def bank (n:Side)(G: Gauge)(M:ℕ) : Pipes G n where
  reg i:= ew (Padded.name (Frost.Card M n) i).2.native
  kernel:= (Start.dictionary G n).kernel
  softer i:= neighbors 4 (Padded.name (Key n) i).native
  sites i:= ⟨_, (ew (Padded.name (Key n) i).native).anchor⟩
-- one transfer log per key. shard
def maskH (i:Key n): Pot G n:= let Z:= i.skin; let f:=i.accrual
                                  masked p.threshold (neighbors 4 i.native) f - masked p.threshold Z f
abbrev rota (i:Key n)(j:ℕ)(M:ℕ)(κ:ℝ) : Pot G n:= if j=M+1 then i.accrual-Frost.draft G i κ M else if j=0 then Frost.draft G i κ 0 else Frost.draft G i κ j - Frost.draft G i κ (j-1)
def part (x κ:ℝ)(i:Frost.Card M n): Pot G n := Start.weight c x • Frost.rota G i.2 i.1.val M κ
def iceCap (x κ :ℝ):Tap G n where
   regular i := if Padded.fixed (Frost.Card M n) i then part G M c x κ (Padded.name (Frost.Card M n) i) else 0
   forced i:= (Start.payload c p G n x).forced i
   logarithm i:= if Padded.fixed (Key n) i then weight c x • Frost.maskH G p (Padded.name (Key n) i) else 0
local notation "W" => (bank n G M)
local notation "P" => iceCap (n:=n) G M p c x κ
lemma reggo (i: ℕ):(P|>.regular i)=if fixed (Card M n) i then part G M c x κ (Padded.name (Frost.Card M n) i) else 0:=rfl
lemma bankSite (i:ℕ): ((W).reg i).site=(name (Card M n) i).2.native:=rfl
lemma bankSize (i:ℕ):((W).reg i).support=neighbors 4 (name (Card M n) i).2.native:=rfl
-- transfer supports & orientation. A.G.Pay costs.
variable (s:Signed)(o:Site n)
lemma glaze_sp (i : Key n) (x: Config G n): Frost.draft G (Key.perm s o i) κ j x = Frost.draft G i κ j (pull s o x):= by change glaze G _ _ _ _=_; rw [Key.oriented]; rfl
lemma rota_sp (i:Key n) (x:Config G n) : Frost.rota G (Key.perm s o i) j M κ x= Frost.rota G i j M κ (pull s o x):=by
  simp only [rota]; split; next h=> rw [Pi.sub_apply,Pi.sub_apply,glaze_sp]; unfold Key.accrual; rw [Key.oriented]; rfl
  split; exact glaze_sp ..; rw [Pi.sub_apply,Pi.sub_apply,glaze_sp,glaze_sp] -- indentation
lemma e_h (i:Key n): neighbors 4 (Key.perm s o i|>.native)=(neighbors 4 i.native).image (affine s o) := by exact (normRange (s:=(s,o)) (show (Key.perm s o i).native=affine s o i.native from rfl) 4).symm
abbrev markP : Equiv.Perm (Card M n):= Equiv.prodCongr (Equiv.refl _) (Key.perm s o)
lemma rainW : Nonempty (((W).pours P).Moves s o):=by
    obtain ⟨v⟩:= Start.moves (G:=G) (b:=p) (c:=c) s o x; let m i:= Padded.name (Frost.Card M n) i
    refine ⟨{ ep:=Padded.sends (markP M s o), kp:=v.kp,             reg_site:=fun i=> ?_, reg_support:=fun i=>?_, forced_inventory:=v.forced_inventory,forced_support:=v.forced_support,forced_tests:=v.forced_tests,valuesE:=fun i V=>?_,valuesK:=v.valuesK }⟩
    · dsimp only [pours]; rw [bankSite,bankSite,name_sends]; rfl
    · dsimp only [pours]; rw [bankSize,bankSize,name_sends]; exact e_h s o _ -- trunc
    dsimp only [pours]; rw [reggo,reggo]; simp only [fixed_sends,name_sends]; split
    · unfold Frost.part; exact congr_arg (fun w:ℝ=> Start.weight c x *w) (Frost.rota_sp (j:=(name (Card M n) i).1) G M s o _ V)
    rfl
-- gauge invariance of mask.
open Extra.Iteration
lemma usesU (i:Key n): Trio.Tidy p (neighbors 4 i.native) (maskH G p i) ∧ ∀ U:Config G n, Frost.maskH G p i U≠0→ ¬Healthy p.threshold (neighbors 4 i.native) U:=by
    let U:=(maskH G p i); let X:=neighbors 4 i.native
    have hh:p.Regular i.skin i.accrual (G:=G):= Start.accrual_regular ..; have hv:i.skin⊆neighbors 4 i.native:= (shore'₀ i).trans (shore_l _)
    refine ⟨Trio.tidy_sub _ (Trio.tidy_mask _ (VerifiedReset.reg_larger hh hv) (Finset.Subset.refl _)) (Trio.tidy_mask _ hh hv),fun w hw he=>hw (by unfold maskH; rw [Pi.sub_apply,masked_eq _ _ _ _ he,masked_eq _ _ _ _ (healthy_mono hv he),sub_self])⟩
lemma mount (i:Key n): maskH G p (Key.perm s o i) = maskH G p i ∘ pull s o:=by
    let v:= Key.perm s o i; have hP:(Key.perm s o i).accrual (G:=G)=i.accrual ∘ pull s o :=funext fun v=> by change residual G _ _=_; rw [Key.oriented]; rfl
    unfold maskH; rw [hP,Key.spun,e_h]; funext U; let θ:Seat n := (s,o)
    change masked _ (θ.spread _) (i.accrual ∘ θ.view) U-masked _ (θ.spread _) (i.accrual ∘ θ.view) U= _; rw [Seat.distribute, Seat.distribute]; rfl -- edit
-- to_continue
end YM.WilsonStartup.Frost
