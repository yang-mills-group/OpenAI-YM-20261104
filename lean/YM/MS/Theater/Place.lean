import YM.MS.Theater.Value

set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset Metric MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge} {h k r:ℕ} {x v:ℤ} {p:Pol G} {F:Law G} {f:Local.BV.Grade G}
local notation "KΩ"=> hands G
lemma claim (p:Fin r→ Local.BV.Grade G)(w:Fin r→ℤ)(hp:∀ i,Horizontal ( p i ) ( w i ))(hz: Local.line r p≠0): ∀ i,(2:ℤ)≤ w i:= by intro i; by_contra! he; exact compose_line hz i (liftZ he ( hp i ))
lemma lineProduced (k:Fin r→ℕ)(p:(i:Fin r)→Witness G ( k i )) : ∃ f:Pol G, At f ((∑ i,(k i+2)),r) ∧ orbit G f= fac KΩ r ( Local.line r (fun i=> RowLeg G ( k i ) ( p i )) ):= by
    rw [ fac_line ]; induction r with | zero=> refine ⟨1, MvPolynomial.isWeightedHomogeneous_one _ _,?_⟩; unfold orbit; rw [LinearMap.comp_apply,AlgHom.toLinearMap_apply,map_one]; rfl | succ r ih=>
       rw [ Local.glow_add ]; obtain ⟨F,hF,h⟩:= ih ( k∘ Fin.succ ) (fun i=>p i.succ ); refine ⟨ page _ ( p 0 )* F, ?_,?_⟩; · rw [ Fin.sum_univ_succ ]; convert! ( nodeId _ _ |>.mp (bypage ( p 0 )) ).mul ( nodeId _ _ |>.mp hF ) using 1; exact Prod.ext rfl (add_comm r 1)
       rw [bags,pageX,h]; rfl
lemma shot (hK:Mem0 F h r): ∃ f∈ charge G ( h,r ), orbit G f=F:= by
    let V:= Submodule.map ( orbit G ) (charge G (h,r)); have hs:Carry G h r ≤ Submodule.comap ( fac KΩ r ) V:= by
        rw [Carry,span_le]; rintro v ⟨p,w,hQ,he,rfl⟩; rw [SetLike.mem_coe,Submodule.mem_comap]; by_cases hz:Local.line r p=0; rw [hz,map_zero]; exact zero_mem _
        have hm(i) := claim p w hQ hz i; let k(i:Fin r):= ( w i-2 ).toNat; have h'(i): w i=(k i:ℤ)+2:=by unfold k; obtain he:= hm i; omega
        choose x hx using fun i=> archiveA (k i) (p i) ( show Horizontal (p i) _ from h' i ▸ hQ i ); obtain ⟨f,hF,hf⟩:= lineProduced k x; suffices hb:(∑ i,(k i+2))=h by rw [ hb ] at hF; rw [show p=(fun i=>RowLeg G (k i) (x i)) from funext hx]; exact ⟨f,hF,hf⟩
        simp_rw [h'] at he; exact_mod_cast he
    refine (show F∈ V from Local.registred _ hK.2 ?_ ( hs hK.1 )); intro l hl; rw [ Book.mod_int ] at hl; exact ( tileCub.mp ( fare G h r hK.1 ) ).rank l (by omega)
end YM.MS.Theater
