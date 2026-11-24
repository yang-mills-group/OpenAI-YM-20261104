import YM.XSpace.Credence

/-!
# Application to local compensated core vertex, in separated mark coordinates
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stall
open Function Filter Set Lattice Mu Chart2 Trace MvPolynomial Next.Rank.Normal Contraction JetGauge Future Drama Chapter Furlough Lows Scale Shade Further.FreeCovariance.KP Playpen
open scoped Topology BigOperators ContDiff
variable {ι I:Type}{L: Filter ι}{Q:Finset I}{a:ι→ℝ} {G:Gauge}{d:ℕ}
lemma page_bound {n:ℕ}{P:Tile G}(h:Book G n P):∀ x,P x∈ DegZ (UnitIndex G) n:=by
  have he (f:Line G)(t:Fee G) : harp f∈ DegZ (UnitIndex G) t.cost:= by unfold harp glyph; rw [Finsupp.linearCombination_apply,Finsupp.sum]; apply Submodule.sum_mem; intro i _; apply Submodule.smul_mem; apply higher (fun _=>1) (show 1≤t.cost by unfold Fee.cost; omega); exact gated _ _ (isWeightedHomogeneous_X ..)
  induction h with
  | unit=> exact fun x=> gated _ 0 (isWeightedHomogeneous_one ..)
  | zero=> exact fun _=> Submodule.zero_mem _
  | left p=> exact fun _=> he _ _
  | right p=>exact fun _=> he _ _
  | rent=> exact fun _=> constant_low _ _ _
  | mul h p i j=> exact fun x=>bounds_mul _ (i x) (j x)
  | add h p i j=> exact fun x=>Submodule.add_mem _ (i x) (j x)
  | scale h c i=> exact fun x=>Submodule.smul_mem _ _ (i x)

variable (V:Initialize G)(p:On.Grade G d)(c:Shade.Cut)
lemma issued_bound : ∃ n:ℕ,∀ t:ℝ,compCost c V p t∈ DegZ (UnitIndex G) n:=by
  obtain ⟨b,hb⟩:= degreeAny (Prelude.mark1 (V.surveys d) p); let W:=(d+4); refine ⟨max b W, fun i=>?_⟩; unfold compCost; apply Submodule.smul_mem; rw [compensate, LinearMap.sub_apply]; apply Submodule.sub_mem; swap
  · rw [rf,LinearMap.comp_apply,Bracket.screen]; apply Submodule.sum_mem; intro j _;  apply higher (fun _=>1) (le_trans (show j.val≤W by unfold W; omega) (le_max_right b W));
    suffices ∀ (A:Stamp G), A∈ OnStage G j.val→ A∈ DegZ (UnitIndex G) j.val from this _ (status (V.surveys j.val) (Normalize.part d j.val (repair V c d i p)))
    intro p hp; induction hp using Submodule.span_induction with
    | mem x h=> obtain ⟨z,hz,rfl⟩:=h; apply page_bound (P:=fun _=>story z) (hz.1 ▸ surge z 0) 0
    | zero=> exact Submodule.zero_mem _
    | add a b _ _ i j=> exact Submodule.add_mem _ i j
    | smul a b _ i=> exact Submodule.smul_mem _ _ i
  change Prelude.fuse _ _ _ _ ∈ _; rw [Uptown.drama]; refine Submodule.sub_mem _ (higher _ (le_max_left _ _) hb) (Submodule.sum_mem _ fun j _=>?_); rw [Shade.quick_sum]; apply Submodule.sum_mem; intro k _; exact Submodule.smul_mem _ _ (higher _ (le_max_right b W) (page_bound (vetting (V.surveys d) p j) k))

variable {F:I→ι→Cover}{w:I→E4}{s:Finset I}
def together (L:Filter ι): Accepts ι Unit where
  carrier := {p | Likely L (fun i=> p i ())}
  zero_mem':= Likely.zero
  add_mem' h p:= Likely.add h p
  smul_mem' c _ h:= Likely.smul (Likely.const L c) h
lemma permit_together (L:Filter ι): Permit L (together L):= fun _ h _ hh=> Likely.mul hh h
variable [L.IsCountablyGenerated](S:Tendsto a L (𝓝 0))(he:∀ᶠ i in L,0<a i)
include S he
lemma relief (A:Club G ι)(HA:A= Stall.interior (G:=G) S he c d ) : Admits (together L) A (fun i (_:Unit)=> compCost c V p (a i)) :=by
  obtain ⟨b,hb⟩:= issued_bound V p c; refine ⟨⟨b, fun i _=>hb _⟩,fun x hx=>?_⟩; subst A; let B i:= orchestra d (a i)⁻¹ (gather d (x i)); change Talent (L:=L) (a:=a) _ _ x at hx; exact solid B hx.1 hx.2.1 S he (he.mono (fun i hi=> inverse_meter d (a i) hi.ne' _)) c V p (secures S he c) hx.2.2

-- support caller real-orbit cost still external; positions as supplied
lemma reward (Z:Poses L a F w s)(H:∀ j∈s,5*c.rOut≤ ‖w j‖)(P:I→ι→Stamp G)(HP:∀ j∈s, Records a L (F j) (P j)): Likely L fun i=> E (Mu.root G) (freeze (compCost c V p (a i))*web s P i):= by classical exact pays (together L) s (factor S he c d Z H) (permit_together L) P HP (fun i (_:Unit)=> compCost _ _ p (a i)) (relief V p c S he _ rfl)
end YM.XSpace.Stall
