import YM.FVA2.Generator.Silt
/-!
# Annular first-order contact cancellation (assembled proof of this step)

Obtain the `harvest` scaling-increment estimate on the actual `XSpace`
`repair`. See `Generator/{Rhythm,Prose}` for how we use that to
kill the *diagonal* part of the order-one scale response -- before it
is shown that there is a full vanishing in the final grade-preserving prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Seals.Bottom
open Function Set Filter XSpace Pages Center Circuits XSpace.Trace XSpace.Lows XSpace.Mu XSpace.Chart2 XSpace.Furlough XSpace.Future
open Lattice XSpace.Gland Maxwell
open scoped Topology BigOperators Classical
variable {G:Gauge}{d n k:ℕ}
def visit (p:Stamp G): Stamp G→ₗ[ℂ] Tile G:= LinearMap.pi fun x:Cover=> tie G p ∘ₗ (Trace.volume x).toLinearMap
abbrev trip (p:Stamp G)(v:PlaqAxes):= visit p (V3 G (tile v))
variable {ι:Type}{L: Filter ι} [L.IsCountablyGenerated]{a:ι→ℝ} (S:Tendsto a L (𝓝 0))(ha:∀ᶠ i in L,0<a i)
variable (χ:Shade.Cut)(s:ℝ)(hs:0<s) (A: TaylorTower G)
private lemma arms {U:Type*}[Fintype U](V:Submodule ℂ (Tile G))(f:Axis→Axis→U→Tile G)(h:∀ u:U,(∑ i:Axis,∑ j:Axis,f i j u)∈ V) : (∑ i:Axis,∑ j:Axis,∑ u:U,f i j u)∈ V:= by
    let f'(p:Axis×Axis)(u:U):= f p.1 p.2 u; rw [show (∑ i:Axis,∑ j:Axis,∑ u:U,f i j u) = (∑ i:Axis×Axis,∑ u:U,f' i u) from by rw [Fintype.sum_prod_type],Finset.sum_comm]; apply V.sum_mem; intro i _; rw [ Fintype.sum_prod_type ]; exact h i
include S ha hs
lemma axis_pair (p:MultiplierEstimates G)(h:wage p=d): visit (Pages.ink p) (∑ v:PlaqAxes,V3 G (tile v))∈ None L a χ s (Bracket.seat d A):= by
    let K:=visit (Pages.ink p); let R:= None L a χ s (Bracket.seat d A); rw [show (∑ v:PlaqAxes,V3 G (tile v)) = (∑ v:PlaqAxes,(V3 G (tile v)-εglows v G)) + (∑ v:PlaqAxes, εglows v G) from by rw [ Finset.sum_sub_distrib, sub_add_cancel],map_add]; apply R.add_mem
    · rw [map_sum]; exact R.sum_mem fun i _=> vanishErr S ha χ s hs _ (show Pages.ink p∈ elemental G d from h ▸ title p) i le_rfl
    rw [minted]; simp_rw [Center.accounted,map_sum,map_smul]; -- sums dimensions i,j,x,y,z. flip inside. use auxiliary generic.
    apply arms; intro x; apply arms; intro y; apply arms; intro z; simp_rw [ ← Finset.smul_sum ]; apply R.smul_mem; exact Foster.supplied p S ha χ s hs A x y z h
lemma circulate {p:Stamp G}(h:p∈ Library G d): (∑ v:PlaqAxes,trip p v)∈ None L a χ s (Bracket.seat d A):= by
    rw [ ← map_sum ]; let V:= (∑ v:PlaqAxes,V3 G (tile v)); let R:= None L a χ s (Bracket.seat d A); induction h using Submodule.span_induction with
    | mem p h=> obtain ⟨q,hq,rfl⟩:=h; exact axis_pair S ha χ s hs A q hq
    | zero=> rw [show visit 0 V=0 from funext fun x=>by simp [visit]]; exact R.zero_mem
    | add p q _ _ a b=> rw [show visit (p+q) V= visit p V+visit q V from funext fun x=>by simp [visit]]; exact R.add_mem a b
    | smul c p _ hp=> rw [show visit (c • p) V = c • visit p V from funext fun x=> by simp [visit]]; exact R.smul_mem _ hp
variable {H:Source.Hol G}(W:Survey G H d)(p:On.Grade G d)
lemma ships (h:k≤d): Tendsto (fun i=> δ χ s (a i) (Bracket.seat d A) k (∑ v:PlaqAxes,Uptown.spirit W p v)) L (𝓝 0):= by
    rcases lt_or_eq_of_le h with h|rfl
    · simp_rw [map_sum]; obtain ht:= tendsto_finsetSum Finset.univ (fun v _=> vanishHigher S ha χ s hs (q:=Uptown.spirit W p v) (n:=d+4) (vetting W p v) (Bracket.seat d A) (by omega : k+4< d+4)); simpa only [Finset.sum_const_zero] using ht
    simp_rw [ show ∀ v,Uptown.spirit W p v=trip (Prelude.enter0 W p) v from fun v=>funext fun x=>by unfold Uptown.spirit; rw [encoded]; rfl ]; exact circulate S ha χ s hs A (Pages.marked W p)
lemma relieved : Tendsto (fun i=> Maxwell.probe A (Bracket.archive d (Uptown.debit W p χ (s*a i)).val) - Maxwell.probe A (Bracket.archive d (Uptown.debit W p χ (a i)).val)) L (𝓝 0):= by
    let V:=Bracket.seat d A; obtain he:= (tendsto_finsetSum (Finset.range (d+1)) fun i hi=> ships S ha χ s hs A W p (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).neg; simp only [Finset.sum_const_zero,neg_zero] at he; apply he.congr; intro i
    rw [Bracket.dicto,Bracket.dicto]; let v(t:ℝ):= view V (Uptown.debit W p χ t).val; change -(∑ k∈ _,_) = v (s*a i) - v (a i); unfold v
    unfold Uptown.debit
    unfold Uptown.bevel Lows.trunc; simp_rw [ LinearMap.sum_apply, Uptown.drama,map_sub,map_sum,← Finset.sum_neg_distrib ]; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro k _; simp_rw [Center.pay, map_sub ]; -- `Cut cider`; match. 
    unfold weigh; dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]; unfold Lows.Cut V; simp only [map_sum,Finset.sum_neg_distrib,Finset.sum_sub_distrib]; abel
-- strongest (B7): `greeting` without the a factor in increment *at all columns*.
theorem harvest (W:XSpace.Initialize G): By ℂ L (fun i=> repair W χ d (s*a i) p- repair W χ d (a i) p) 0 := by
    let f (x: TaylorTower G):Module.Dual ℂ (Normalize.Sec G d):= (Maxwell.probe x).toLinearMap ∘ₗ (shellSector G d).subtype ∘ₗ Bracket.portal W d
    refine redeemBy f ?_ ?_; intro x hx; apply (Bracket.exchangeable W d).1; rw [map_zero]; apply Subtype.ext; apply Maxwell.equalPol; intro t; change Maxwell.probe t _ = Maxwell.probe t 0; rw [map_zero]; exact hx t
    intro x; simp_rw [map_zero,map_sub]; change Tendsto (fun i=> Maxwell.probe x (Bracket.portal W d _).val - Maxwell.probe x (Bracket.portal W d _).val) L _; simp_rw [Furlough.shore]; exact relieved S ha χ s hs x _ _
end YM.FVA2.Generator.Seals.Bottom
