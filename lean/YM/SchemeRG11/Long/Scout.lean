import YM.SchemeRG11.Long.Lane
/-! Rotated stencil remains in same EXACT step grade. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Long
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open scoped Classical
variable {G: Gauge} {n:ℕ}
lemma bridged (i:Axis)(c:G.ColorIndex)(T:Bevy G.Color): element (cant (linkup T)) i c = EuclideanSpace.proj c ∘ T i:=rfl
lemma across (T:Bevy G.Color)(i:Axis)(c:G.ColorIndex)(s:Fliers)(x:Cover): fleet s (element (cant (linkup T)) i c) x=fleet s (T i) x c:=congrFun (plane_map ((EuclideanSpace.proj c).toLinearMap:Module.Dual ℝ G.Color) _ _) _
lemma swirl (x:Cover)(s: Signed)(j:ℕ)(L: Module.Dual ℝ (Pert.Bare.Response G j)):
 ∃ p: Touch G,p∈Stepper G (j+1) ∧ ∀ A:Bevy G.Color,L (Pert.Bare.wideCore G j x (Pert.Bare.wideLink G s (linkup A))) = sense (cant (linkup A)) p:=by
 have he(i b:Axis)(v: Fin j→ Axis)(c:G.ColorIndex):∃ p:Touch G,p∈Stepper G (j+1) ∧∀A:Bevy G.Color,Pert.Bare.wideCore G j x (Pert.Bare.wideLink G s (linkup A)) i b v c=sense (cant (linkup A)) p:=by
    let t:= clutch v
    have hw(a i:Axis): ∃ p:Touch G,p∈Stepper G (j+1) ∧∀A:Bevy G.Color,fleet t (soar a (wing s A i)) x c=sense (cant (linkup A)) p:=by
      let r:= a ::ₘ t; let k:=r.map s.perm; let d:Shaft G:= ((s.act x + (trail s i + motive s r),s.perm i),c); let u:= Push.FiniteDetection.Free.Hyper.flip s i * stir s r
      refine ⟨u • vane0 d k, Submodule.smul_mem _ _ (ride ?_),fun A=>?_⟩
      · simp [k,r,t,cargo]
      rw [map_smul,← flex_zero (vane0 d k),dip,zero_add,across,show fleet t (soar a (wing s A i))=fleet r (wing s A i) from by unfold r; rw [fleet_cons'];rfl, orient];rfl
    obtain ⟨p,P,Q⟩:=hw i b; obtain ⟨r,R,U⟩:=hw b i
    refine ⟨(j.factorial:ℝ)⁻¹ • (p-r),Submodule.smul_mem _ _ (Submodule.sub_mem _ P R),fun A=>?_⟩; rw [wide_wing,wingtips,Flock.bend,map_sub,Pi.sub_apply,map_smul,map_sub, ← Q A, ← U A]; rfl
 choose p H h using (fun e:Spot G j=>he e.slash e.via e.γ e.color)
 refine ⟨∑ i,L (Spot.impulse i) • p i, Submodule.sum_mem _ (fun i _=>Submodule.smul_mem _ _ (H i)),fun A=>?_⟩; nth_rw 1 [pad_full L]; rw [LinearMap.sum_apply,map_sum]; apply Finset.sum_congr rfl; intro i _; rw [_root_.map_smul, LinearMap.smul_apply]; congr 1; rw [← h]; change inner ℝ (unitColor G i.color) _=_; rw [real_inner_comm]; exact to_color ..
lemma high_probe (i:Labels.Key G): leafProbe 1 i∈Stepper G (i.1+1):=by
 let L:= ((Labels.axes G i.1).coord i.2); choose p H P using fun s:Signed=>swirl (G:=G) (affine s⁻¹ 0 (0:Cover)) s i.1 (L ∘ₗ Labels.Taylor.turn s.ortho ∘ₗ Pert.Bare.radialMap)
 let c:ℝ:= (Fintype.card Signed:ℝ)⁻¹
 rw [show leafProbe 1 i=c • ∑ j,p j from ?_]; exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _=>H i)
 apply strain; intro w; rw [← Tree.cant_inv w,Outlook.worker,Outlook.rune,map_smul, _root_.map_sum]; let A:=linkup.symm (Tree.tint w)
 rw [show Tree.tint w=linkup A from rfl, Outlook.soul,Pert.Bare.wideLinear]; simp only [LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.smul_apply,map_smul,map_sum,one_zpow,one_smul]; apply congrArg (c • ·); exact Finset.sum_congr rfl fun j _=>P j A
lemma ear (i:Labels.Key G)(h:ℝ):leafProbe h i∈Stepper G (i.1+1):=by
 apply Submodule.smul_mem; have he:=high_probe i; rwa [leafProbe,one_zpow,one_smul] at he
end YM.SchemeRG11.Long
