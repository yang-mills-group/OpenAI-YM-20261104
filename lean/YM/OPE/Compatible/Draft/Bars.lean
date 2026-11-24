import YM.OPE.Compatible.Draft.Gyr
/-!
# Joint strands with all rotations. D-chart preserving products, same at orig. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n c f:Side}
open Wilson RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric Glass
attribute [local instance] Gauge.frobInner
variable {i j:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B} (S: StepData c f) (H: Even c.val)
local notation "μ"=> even_both S.ratio H
local notation "J!"=> Rill.rollB S H
abbrev StemX (T:Plot μ): (Tableau S H).Stand ({origin μ}:Set _):= T.Slotting (Pond H) (LiftV S.ratio H)
variable (T:Plot (even_both S.ratio H))
local notation "D!"=> StemX S H T
-- split
private def portC : T.Free ⊕ Limb H→ (StemX S H T).Free:=
    Sum.elim (fun i=>⟨.inl i.val,mt (T.slotted ..).mp i.property⟩) (fun i=>⟨.inr i, T.unslotted _ (LiftV S.ratio H) i⟩) -- ambiguity
private lemma reach_p : Bijective (portC S H T):=by
    constructor
    · intro a b h; rcases a with a|a<;> rcases b with b|b
      · change (⟨Sum.inl a.val,_⟩: (StemX S H T).Free)=⟨Sum.inl b.val,_⟩ at h; exact congr_arg Sum.inl (Subtype.ext (Sum.inl.inj (congr_arg Subtype.val h)))
      · exact False.elim (Sum.inl_ne_inr (show Sum.inl a.val=Sum.inr b from congr_arg Subtype.val h)) -- name
      · exact False.elim (Sum.inl_ne_inr (show Sum.inl b.val=Sum.inr a from congr_arg Subtype.val h.symm))
      exact congr_arg Sum.inr (Sum.inr.inj (show Sum.inr (α:=Limb μ) a=Sum.inr b from congr_arg Subtype.val h))
    rintro ⟨i|i,h⟩; · refine ⟨Sum.inl ⟨i,?_⟩,rfl⟩; exact mt (T.slotted ..).mpr h
    exact ⟨Sum.inr i,rfl⟩
def piBond (S:StepData c f)(H:Even c.val)(T:Plot (even_both S.ratio H)) : (StemX S H T).Free ≃ (T.Free⊕ Limb H):= (Equiv.ofBijective (portC S H T) (reach_p S H T)).symm
-- notation corrections
abbrev lo_left (G:Gauge): Keys G J!→L[ℝ] Keys G (Limb μ):=Pilot.prL (Equiv.refl _) G -- local G name bug
abbrev lo_right (G:Gauge): Keys G J!→L[ℝ] Keys G (Limb H):= Pilot.prR (Equiv.refl _) G
lemma beamAt (x:Keys G (StemX S H T).Free): lo_left S H G ((StemX S H T).rollX x)= T.rollX (Pilot.prL (piBond S H T) G x):=by
      ext1 i; change (StemX S H T).cite 0 x (.inl i)=T.cite 0 (Pilot.prL (piBond S H T) G x) i
      by_cases h:T.Branch i
      · unfold Stand.cite; rw [dif_pos h,dif_pos ((T.slotted ..).mpr h)];rfl
      unfold Stand.cite; rw [dif_neg h,dif_neg (mt (T.slotted ..).mp h)];rfl
lemma beamRt (x:Keys G (StemX S H T).Free): lo_right S H G ((StemX S H T).rollX x)= Pilot.prR (piBond S H T) G x := by
      ext1 i; change (StemX S H T).cite 0 _ (.inr i)=_; unfold Stand.cite; rw [dif_neg (T.unslotted (Pond H) (LiftV S.ratio H) i)];rfl
lemma mpar {p:ScriptJ (Keys G (Limb μ))}(h:(Pond μ).Marbles p):(Tableau S H).Marbles (p ∘ lo_left S H G):= by
      let L:=lo_left S H G; refine ⟨fun i=> (h.toll i).compLinear L.toLinearMap,fun {x y u} hU=>?_⟩; let U:=L ∘ x; let Y:=L ∘ y; have hv:(Pond μ).Track U Y u:=by
           refine ⟨L.contDiff.contDiffAt.comp 0 hU.hX, L.contDiff.contDiffAt.comp 0 hU.hY,?_,?_,?_,hU.chart⟩; unfold U; rw [comp_apply,hU.gx,map_zero]; unfold Y; rw [comp_apply,hU.gy,map_zero]
           exact hU.law.mono fun i hi=> funext fun v=> congr_fun hi (.inl v)
      change (fun t=>(p (L (t⁻¹ • x t))).atK t - (p (L (t⁻¹ • y t))).atK t)=O[_]_; simp_rw [map_smul]; exact h.honors hv
end YM.OPE.Cascade.Rill
