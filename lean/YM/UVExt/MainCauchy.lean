import YM.UVExt.MainCascade

/-! Full ultraviolet-index convergence of all fixed-level leading unmasked canonical jets through order four under a single static geometry gate, at every physical period. Does **not** compare thermal resets or prove convergence of the separated histories. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function RG Precision Wilson Lattice Bid Exterior Laurent Bloch Matrix Filter Set
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge} {A : Levels G} {P : MapPrices} {M : Horizon A} {s : Supply.Sheet G} {L:Supply.Rolls s} {Q : PostCost L} {H : ChartRatio G} (K : Kin M H) (h : Discipline P A M) (hk : K.Planned Q)
include h hk in
lemma allJoint {U V : ℕ→Shadow G} {t' : ∀ m, Transfers A m} {u u' : ℕ→ℕ} (hu : Tendsto u atTop atTop) (hUV : ∀m,woodPassing K u m U) (hV : ∀ m,woodPassing K u' m V)
   (ht : Follows A u M t') (hk' : Tendsto u' atTop atTop) (p : ℕ) : confluent K u u' 4 p := raiseJoint K h hk u hu u' hUV hV ht hk' p 4 (Or.inr rfl) <| (show _ from raiseJoint K h hk u hu u' hUV hV ht hk' p 3 (Or.inl rfl) (joint_two K h hk u hu u' hUV hV ht hk' p))
include hk
lemma getPassing {u : ℕ→ℕ} (hu : Tendsto u atTop atTop) : ∃ U : ℕ→Shadow G, ∃ k : ℕ→ℕ, StrictMono k ∧ ∀ m, woodPassing K (u∘k) m U := by
  obtain ⟨U,-,k,hk,H⟩ := fleet (fun m=>(hu.eventually (eventually_ge_atTop m)).mono fun N h=>hk.cap (u N) m h) -- fix
  exact ⟨U,k,hk,H⟩
include hk h
/- Leading classical system only, quadratic/cubic/quartic **including** true Wilson base and nonlinear Ad along the Cover path, no flags. -/
set_option maxHeartbeats 250000 in
lemma mainCauchy (m p k : ℕ) (hk' : k≤4) : CauchySeq (spray (fun d=>knotted (A.S.side m p) (jclip A m) (K.path d m)) k) := by
  let f := (spray (fun d=>knotted (A.S.side m p) (jclip A m) (K.path d m)) k)
  change CauchySeq f
  by_contra hw; rw [Metric.cauchySeq_iff] at hw; push Not at hw
  obtain ⟨ε,he,hw⟩ := hw; choose xN hN yN hvN hv using hw
  have ht := tendsto_atTop_mono (l:=atTop) (f:=fun n=>n) hN tendsto_id
  have ht' := tendsto_atTop_mono (l:=atTop) (f:=id) hvN tendsto_id
  obtain ⟨U,l,hl,H⟩ := getPassing K hk ht
  obtain ⟨V,b,hb,H'⟩ := getPassing K hk (ht'.comp hl.tendsto_atTop)
  obtain ⟨g,hg,Y,hY⟩ := Assurance A M P ((ht.comp hl.tendsto_atTop).comp hb.tendsto_atTop) h
  let r := l∘b∘g
  have hr := (hl.comp <| hb.comp <| hg).tendsto_atTop
  have hU : ∀ j, woodPassing K (xN ∘ r) j U := fun j=>(H j).subseq ((hb.comp hg).tendsto_atTop)
  have hV : ∀ j, woodPassing K (yN ∘ r) j V := fun j=>(H' j).subseq hg.tendsto_atTop
  obtain ⟨F,h₁,h₂⟩ := allJoint K h hk (u:=xN ∘ r) (u':=yN ∘ r) (t':=Y) (ht.comp hr) hU hV hY (ht'.comp hr) p m k hk' -- named fix
  exact not_le_of_gt he (ge_of_tendsto (a:=0) (show Tendsto (fun i=>dist (f (xN (r i))) (f (yN (r i)))) atTop (𝓝 0) from by have ht := h₁.dist h₂; rw [dist_self] at ht; exact ht) <| Eventually.of_forall fun i=>hv (r i))

/-- Interface for consumers here. Not the full Wilson-law endpoint. Geometry receipts must be on an actual horizon. -/
def Leading (A : Levels G) (W : ℕ→ℕ→PathData G) := ∀ m p k : ℕ,k≤4 → ∃ g, Tendsto
    (fun d=> iteratedFDeriv ℝ k (fun v:Dir G (A.S.side m p)=> mainTerm (jclip A m) (W d m) (represent v)) 0) atTop (𝓝 g)
theorem leading_if_gates : Leading A K.path := fun m p k hk'=> cauchySeq_tendsto_of_complete (mainCauchy K h hk m p k hk')

end YM.UVExt.Paths
