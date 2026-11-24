import YM.SchemeConversionRG11.FirstW.Jade.Arch
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Set Metric Lattice Pert Align Position Topology Maxwell Classical Deck
open scoped BigOperators Classical
variable {G:Gauge}{r:ℕ} (F:Labels.Frames G)(L:Side)
def NativeBill (F:Labels.Frames G)(L:Side)(v:Fin r→E F 6)(Z:ℕ→Pack F)(i:ℕ)(y:Full.Grid (Full.period L i) r): ℂ:= stock F (Full.period L i) y (Full.topSpacing L i) v (carryR (Full.period L i) (Full.topSpacing L i) (Z i))
variable {F L}
lemma scene {p:Points r}(hh:1<L.val)(h:p∈conf r){σ:ℕ→ℕ}(hs:Tendsto σ atTop atTop)(o:∀ i,Full.Grid (Full.period L (σ i)) r)(hu:Tendsto (fun i=> Full.embedding (Full.topSpacing L (σ i)) (o i)) atTop (𝓝 p)) : Diorama (Rig.path (itinerary L hh) σ hs) o p := ⟨h,fun j=> (PiLp.continuous_apply 2 (fun _:Fin r=>E4) j).continuousAt.tendsto.comp hu,fun i=> four_places hh (σ i)⟩ -- context help
lemma schedule_H {p:Points r}(hh:1<L.val) (hg:G.Simple)(v:Fin r→E F 6)(Z:ℕ→Pack F)(H:∀ Q:Wash,stampB F Z (itinerary L hh) Q)(hp:p∈conf r) : ∃ z:ℂ,∀ n:ℕ→ℕ,Tendsto n atTop atTop→∀ u:∀ i,Full.Grid (Full.period L (n i)) r,Tendsto (fun i=>Full.embedding (Full.topSpacing L (n i)) (u i)) atTop (𝓝 p) → Tendsto (fun i=> NativeBill F L v Z (n i) (u i)) atTop (𝓝 z) := by
 let M:= Rig.routine L hh; let W:=fun (i:ℕ)(u:Full.Grid (Full.period L i) r)=> Full.embedding (Full.topSpacing L i) u
 have hf: ∀ n:ℕ→ℕ,Tendsto n atTop atTop→∀ u:∀ i,Full.Grid (Full.period L (n i)) r,Tendsto (fun i=>W _ (u i)) atTop (𝓝 p) → Helen (fun i=> NativeBill F L v Z _ (u i)) := by
    intro n hs u he; change Helen (showP (Rig.path (itinerary L hh) n hs) F u v (Z ∘ n))
    exact d_paid (T:=Rig.path (itinerary L hh) n hs) F u (scene hh hp hs u he) hg (c:=fun i=> Rig.denom L (n i)) (fun i=>Rig.exchangePt L (n i)) v _ (fun Q=> covers_sub F Z n hs Q (H Q))
 let P := fun _:ℕ=> p; have he : Tendsto P atTop (𝓝 p):= tendsto_const_nhds
 have h:=transit (p:=NativeBill F L v Z) (v:=W) hf (n:=id) tendsto_id (Rig.plot M P) (show Tendsto (fun i=> Full.embedding (M.t i) (Rig.plot M P i)) atTop _ from (Rig.spot_limit M he).congr' ((Rig.spot_emb M he).mono (fun _ h=> h.symm)))
 exact h
lemma reflex (hh:1<L.val) (hg:G.Simple) (Z:ℕ→Pack F)(v:Fin r→E F 6)(H:∀ Q:Wash,stampB F Z (itinerary L hh) Q): ∃ W:Points r→ℂ,Rig.Arrives (Rig.routine L hh) (NativeBill F L v Z) (conf r) W:= by
 choose u hu using fun (x: {p // p∈conf r})=> schedule_H hh hg v Z H x.property
 refine ⟨fun x=>if h:x∈conf r then u ⟨x,h⟩ else 0, fun σ hs p hp o ht=>?_⟩; change Tendsto _ _ (𝓝 (if h:p∈conf r then u ⟨p,h⟩ else 0)); simp only [dif_pos hp]; exact hu ⟨p,hp⟩ σ hs o ht

def transcribed (F:Labels.Frames G)(L:Side)(v:Fin r→E F 6)(Z:ℕ→Pack F) (f:Points r→ℂ)(i:ℕ) := PowerSeries.coeff 1 (Full.profile 6 r F L i f v) - ∑ j:Fin r,PowerSeries.coeff 0 (Full.profile 6 r F L i f (update v j ((carryR (Full.period L i) (Full.topSpacing L i) (Z i)).val (v j))))
lemma recoup (h:1<L.val) (Z:ℕ→Pack F) (v:Fin r→E F 6)(f:Points r→ℂ): transcribed F L v Z f=Rig.reporting r (Rig.routine L h) (NativeBill F L v Z) f:=by
 funext i; simp only [transcribed, Full.profile,Rig.reporting, Rig.routine,NativeBill,sum_apply, smul_apply, map_sum, map_smul, smul_eq_mul, Deck.stock, Finset.mul_sum, mul_sub,mul_assoc,PowerSeries.coeff_zero_eq_constantCoeff_apply]
 rw [Finset.sum_comm (s:=Finset.univ (α:=Fin r)) (t:= Finset.univ (α:=Full.Grid (Full.period L i) r)), ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; rfl
lemma archived (hh:1<L.val)(Z:ℕ→Pack F) (v:Fin r→E F 6)(f:Points r→ℂ)(H: HasCompactSupport f)(hp:Continuous f)(hz:tsupport f ⊆ conf r){K:Points r→ℂ}(ht: Rig.Arrives (Rig.routine L hh) (NativeBill F L v Z) (conf r) K): Tendsto (transcribed F L v Z f) atTop (𝓝 (∫ x,f x*K x)) := by rw [recoup hh]; exact Rig.grid_limit hp H hz ht
-- witness actual field section permitted (no MS). gram/quasihorizon pay later. Distinct test also later
lemma YearOne (F:Labels.Frames G)(hg:G.Simple)(hh:1<L.val) : ∃ Z:ℕ→Pack F,(∀ Q:Wash,stampB F Z (itinerary L hh) Q) ∧ ∀ (r:ℕ)(v:Fin r→E F 6), ∃ W:Points r→ℂ,Rig.Arrives (Rig.routine L hh) (NativeBill F L v Z) (conf r) W ∧ ∀ f:Points r→ℂ,HasCompactSupport f→ Continuous f → tsupport f ⊆ conf r → Tendsto (transcribed F L v Z f) atTop (𝓝 (∫ x,f x*W x)) :=by
 obtain ⟨Z,H⟩:= covers_r F (show MarkGrid (itinerary L hh) _ from (fun i=> Rig.exchangePt L i)); refine ⟨Z,H,?_⟩; intro r v
 obtain ⟨w,H⟩:= reflex hh hg Z v H; exact ⟨w,H,fun f hB hp he=> archived hh Z v f hB hp he H⟩
end YM.RG11.FirstW
