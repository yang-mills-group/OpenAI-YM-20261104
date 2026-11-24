import YM.Integration.WilsonOriginalPublicRelativeGramRestored

/-! A small-wall pooled reference pays the actual full matrix bound. The
signed quotient headers may be supplied by a weak field heard on a
wider panel, using the same two source matrices before all physical prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramWeakHeads
open Filter Finset Function Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Extraction Extraction.Banks RG17 Spec Table Table.Pairing Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open Trace.Pilot PhysMS
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonOriginalPublicRelativeGramReflectedLimit (ordered entered)
open WilsonOriginalPublicRelativeGramPosted (Dated submitted deposits gram)
open WilsonOriginalPublicRelativeGramOriented (maxwell)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator

variable {I₀:Type}
def cofile {G:Gauge}{R:Run G}{W:Initialize G}{d:I₀→ℕ}
    (pool far:Dated (L:=Unit) R W d):Dated (L:=Unit) R W d:=
  {far with frame:=fun which z=>if which then far.frame true z else pool.frame false z}

variable {G:Gauge}(B:Local.Physical.Deck G)(h:ℕ)(a:Axis)(R:Run G)
    {f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    (J:ℝ→tower S)(ℓ:Ultrafilter (ℕ×ℕ))(avoid:Finset E4){g:ℝ→ℝ}
    (Γ:WilsonViewerReportingGrid.Grid (ℓ:=ℓ) F h g)
local notation "I" => Glyph B h
local notation "Z" => ℝ×(ℕ×ℕ)
local notation "d" => (fun _:I=>h)
local notation "fused" => ordered trail (fun _:ℝ=>(ℓ:Filter (ℕ×ℕ)))

theorem original (simple:G.Simple)(temperature:Coupling G g)(lead:Leading F J)
    (below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)
    (Y:ℝ→(ℕ×ℕ)→I→R.family.label h)(b:ℝ→I→R.family.label h)
    (selected:∀ᶠr in trail,(∀i,Tendsto (fun z=>Y r z i) (ℓ:Filter (ℕ×ℕ)) (𝓝 (b r i))) ∧
       ∀i,S.project h (b r i)=J r h (named R B h i))
    (W:Initialize G)(sale:ℝ→Dated (L:=Unit) R W d)(fee:Z→I→I→ℝ)(level:I→ℕ)
    (wide:ℝ→Dated (L:=Unit) R W d)(ε:Z→ℝ)
    (covered:Tendsto (fun p:Z=>gram R W d (sale p.1) p.2) fused (𝓝 (maxwell B h a)))
    (hearing:∀ i j,∀ᶠp:Z in fused,
      ‖entered B h a R F ℓ avoid Γ Y p i j-submitted R W d (sale p.1) false p.2 i j‖≤fee p i j)
    (fresh:∀ i j,Tendsto (fun p:Z=>fee p i j) fused (𝓝 0))
    (deposited:∀ i j,Tendsto (fun p:Z=>deposits R W d (sale p.1) false p.2 i j) fused (𝓝 0))
    (relative:∀ᶠp:Z in fused,
      let row:=cofile (sale p.1) (wide p.1)
      IsUnit (row.frame false p.2).det ∧ ‖(1:Matrix I I ℂ)-(row.frame false p.2)⁻¹*row.frame true p.2‖≤ε p)
    (rate:Tendsto ε fused (𝓝 0))
    (heads:∀i j,level j≤level i → Tendsto (fun p:Z=>(wide p.1).frame true p.2 i j) fused
      (𝓝 ((1:Matrix I I ℂ) i j))):
    Tendsto (fun p:Z=>(sale p.1).frame false p.2) fused (𝓝 1) ∧
    Tendsto (fun p:Z=>(wide p.1).frame true p.2) fused (𝓝 1):=by
  let pool:=fun p:Z=>(sale p.1).frame false p.2
  let weak:=fun p:Z=>(wide p.1).frame true p.2
  let H:=fun p:Z=>gram R W d (sale p.1) p.2
  let M:=maxwell B h a
  let P:=entered B h a R F ℓ avoid Γ Y
  have physical:Tendsto P fused (𝓝 M):=WilsonOriginalPublicRelativeGramReflectedLimit.original
    B h a R F J ℓ avoid Γ simple temperature lead below Y b selected
  have self:Tendsto (fun p:Z=>(pool p)ᴴ*H p*pool p) fused (𝓝 M):=by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have near:Tendsto (fun p:Z=>P p i j) fused (𝓝 (M i j)):=
      ((continuous_id.matrix_elem i j).tendsto _).comp physical
    have difference:Tendsto (fun p:Z=>P p i j-((pool p)ᴴ*H p*pool p) i j) fused (𝓝 0):=by
      refine squeeze_zero_norm' ?_ (show Tendsto (fun p:Z=>fee p i j+deposits R W d (sale p.1) false p.2 i j) fused (𝓝 0) from ?_)
      · filter_upwards [hearing i j] with p price
        exact (norm_sub_le_norm_sub_add_norm_sub _ (submitted R W d (sale p.1) false p.2 i j) _).trans
          (add_le_add price (WilsonOriginalPublicRelativeGramPosted.printed R W d (sale p.1) false p.2 i j))
      · simpa only [add_zero] using (fresh i j).add (deposited i j)
    simpa only [sub_sub_cancel,sub_zero] using near.sub difference
  obtain ⟨C,paid⟩:=WilsonOriginalPublicRelativeGramOrientationLimit.bounded B h a pool H covered self
  have swap:Tendsto (fun p:Z=>weak p-pool p) fused (𝓝 0):=by
    refine squeeze_zero_norm' ?_ (show Tendsto (fun p:Z=>C*ε p) fused (𝓝 0) from ?_)
    · filter_upwards [relative,paid] with p receipt cap
      change IsUnit (pool p).det ∧ ‖(1:Matrix I I ℂ)-(pool p)⁻¹*weak p‖≤ε p at receipt
      have identity:weak p-pool p=pool p*((pool p)⁻¹*weak p-1):=by
        rw [Matrix.mul_sub,Matrix.mul_nonsing_inv_cancel_left _ _ receipt.1,Matrix.mul_one]
      rw [identity]
      exact (norm_mul_le ..).trans (mul_le_mul cap (by rw [norm_sub_rev]; exact receipt.2)
        (norm_nonneg _) ((norm_nonneg _).trans cap))
    · simpa only [mul_zero] using rate.const_mul C
  have ref:Tendsto pool fused (𝓝 1):=by
    apply WilsonOriginalPublicRelativeGramOrientationLimit.original B h a pool H level covered self
    intro i j order
    have e:Tendsto (fun p:Z=>(weak p-pool p) i j) fused (𝓝 ((0:Matrix I I ℂ) i j)):=
      ((continuous_id.matrix_elem i j).tendsto _).comp swap
    have one:Tendsto (fun p:Z=>weak p i j) fused (𝓝 ((1:Matrix I I ℂ) i j)):=heads i j order
    simpa only [Matrix.sub_apply,Matrix.zero_apply,sub_sub_cancel,sub_zero] using one.sub e
  exact ⟨ref,by simpa only [sub_add_cancel,zero_add] using swap.add ref⟩

end YM.Integration.WilsonOriginalPublicRelativeGramWeakHeads
