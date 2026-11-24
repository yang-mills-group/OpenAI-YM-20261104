import YM.FVA2.O.Ward.Stamps
/-!
# Power weights for the B lines

`tide`: the weights `3 - wfield i - wfield j`. Use for `lineB`, `lineD`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Lives
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job
open scoped Topology ContDiff
variable {G:Gauge}{I E:Type}{t:I→ℝ}
abbrev lineA (G:Gauge)(s:ℝ):Edge G:= A0 G s 0
abbrev lineB (G:Gauge)(s:ℝ):Edge G:= B0 G s 0
abbrev lineD (G:Gauge)(s:ℝ):Edge G:= ( Wick.Q G 0 ).change (A0 G s 0)
abbrev tide (U:ℝ→ Edge G) : Prop := ∀ (i j:BH G)(p:ℝ), U p i j = era (exp p) (U 0 i j) ((3:ℤ)-wfield i-wfield j)
lemma shapeB : tide (lineB G):= by
    intro i j p; unfold lineB; ext x; unfold era; simp only [B0, Landau.choir,id_eq]; split; · rcases i with ⟨⟨_|a,_|_⟩,i⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,r⟩ <;> norm_num [laplace,Landau.low,coat,dim,wfield]  -- rfl would not handle 0 length
    rw [smul_zero]
lemma shapeD : tide (lineD G):= by
    intro i j p; unfold lineD; rw [cue,cue]; ext x; simp only [era, L0',Landau.choir,id_eq]; split; · rcases i with ⟨⟨_|a,_|_⟩,i⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,r⟩ <;> norm_num [laplace,Landau.dotLow,coat,dim,wfield]
    rw [smul_zero]
lemma edgeC {U:ℝ→Edge G}(h:tide U)(hr:Rolled (U 0)): BackF (fun (_:I)=> U):= by
    constructor; · intro _ i j p; rw [ funext (fun x:ℝ=>congr_fun (h i j x) p) ]; unfold era; exact Continuous.smul (M:=ℝ) (continuous_exp.zpow₀ _ (fun p=>Or.inl ((exp_pos p).ne'))) (( ((lineOf hr i j) 0|>.smooth ()) ).continuous.comp ( continuous_exp.smul continuous_const ))
    intro i T hT p q; unfold tap; simp only [Pi.one_apply, cw, one_zpow,one_mul]; rw [funext (fun k:camp T=>h p q k.2)]; exact Rake.transport (lineOf hr p q) (fun i=> htT i) hT
lemma edgeT (S: Scale I)(h:∀ i,exp (t i)= S.length i){U:ℝ→ Edge G}(hp:tide U)(hv:Rolled (U 0)): Sheet S (fun i=> (S.length i)⁻¹) (fun i=> U (t i)):= by
    intro i j; rw [funext (fun k=>hp i j (t k))]; simp_rw [h]; convert! fullE (S:=S) (lineOf hv i j) (n:=(3:ℤ)-wfield i-wfield j) using 1; ext; rw [← zpow_neg_one, ← zpow_add₀ (S.pos _).ne']; congr 1; omega
lemma realityA : BackF (fun (_:I)=> lineA G):= Upcoming I G
lemma realityB : BackF (fun (_:I)=> lineB G):= edgeC shapeB rB
lemma realityD : BackF (fun (_:I)=> lineD G):= edgeC shapeD rL
end YM.FVA2.O.Lives
