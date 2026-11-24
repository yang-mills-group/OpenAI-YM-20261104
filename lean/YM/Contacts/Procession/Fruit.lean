import YM.Contacts.Procession.Invest
/-! Projection-facing interface at an available horizon (still need heat correction/transports & renormalized finite Mark frame). Re-open the shifted charge. -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Procession.Catch
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter Shuttle.Tide
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
variable {α β:Type}{G:Gauge}{σ:ℝ≥0}{T:TableFee}{p m d k t i r:ℕ}{n:Side}
abbrev coil (F:House α)(p:ℕ) := dazzle (shiftA (Catch.cap p) F)
lemma coil_pack (F:House α)(k:α→β)(p i j:ℕ): packing k (coil F p i j)= coil (plead F k) p i j:= by -- β
    unfold coil dazzle; split
    next h=> rw [← Catch.pledgeShift _ _] -- lemma infer p & need [Fintype α]? no
    next _=> ext; simp [packing,cram]
lemma coil_mirror (F:House α)(h:Proper p F) (i d:ℕ): Poem (coil F p i d):= by unfold coil dazzle; split; apply (tagged h (by unfold Catch.cap; omega) (ht:= (by unfold Catch.cap; omega))).poems; apply Poem.empty
section
variable {F:bore G}{x:Dye G}
theorem coil_tags (h:Mount F p)(hp:Price F x σ T)(he:0<σ) (i:ℕ): Tide.Tags (coil F p i):= by
   refine ⟨⟨coil_mirror _ h.incarnate _,?_ ⟩, fun m k=>?_⟩
   · intro r; refine ⟨x,σ,he,?_⟩; unfold coil dazzle; split; exact ⟨_,(xin (Catch.cap p) 0 hp).lands ..⟩; exact ⟨_,Rest.zero⟩
   let X:= plead F (lower m); let U:=shiftA (Catch.cap p) X; let n:=i+k+3; let K:=House.wind U n i; have hH:GuardsL K (n-i):=(h.attends m).birth _ _ (by omega:i<n); have hv:= fireLife hH; let V:= Kale.fire K; refine ⟨V,hv.consent,hv.invariance,hv.radiant,fun j hj x=>?_⟩; rw [nightwalk hv.radiant hH.analytic (firesL hH).2 j (by unfold n; omega) x]; rw [show _=_ from House.wind_jet U i n j x,if_pos (by omega:j+i<n),coil_pack,glitter] -- need V shorthand
end
end YM.Contacts.Procession.Catch
