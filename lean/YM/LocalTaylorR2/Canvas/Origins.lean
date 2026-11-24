import YM.LocalTaylorR2.Canvas.Nidus

/-! # Expose two private argument placement lemmas of Lakeside/Serene for use independently. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Frond
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows Mask Coat SliceRows.DataKernel Scroll Strokes Quill Metric
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {V : Config G c} {U : Config G f}
variable {s : ℝ} {P : Teller G} {L : Side} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {j : ℕ}
open Brush

/-- Require U match on ≤7B/8 (so available from a B protector).
No far κ usage. `L` post hull. -/
lemma placementR2 (H : Room P S T s) (o : Spot c f) (k : S.Choices) (z : Site c→G.El)
    (x : ZipP G c f) (a : Directions G f) (d : ℕ) (hd : 7*radiusB s /8≤d)
    (he : AgreeNear id (lead S o) d (gauge z V) (increment 1 x.1))
    (ht : AgreeNear S.ratio.parent (lead S o) d U (increment (replica S.ratio V) a))
    (hv : ∀ p : Bond f, separation (lead S o) (atEdge S p) ≤ d → spinRow S z a p=x.2 p) :
    squarepot T s k U V a o=ivy T s k o x := by
  let b:= lead S o; let G':= constantGauge z S.ratio; let P':=gauge G' U; let V':=gauge z V; let q:=S.prediction U k
  let w:=increment 1 x.1; let u:= shaft S x; let B:=radiusB s
  have hp := H.sight
  have hl:= SectorMeasure.funds_branch H.accepted
  obtain ⟨W,K,hP,-⟩ := H.accepted.feeds
  have hx : AgreeNear S.ratio.parent b d P' u := by
    intro i hi
    have hf : gauge G' (increment (replica S.ratio V) a) i=increment (replica S.ratio V') (spinRow S z a) i := by
      rw [← copied _ S.patch.odd_side]; unfold Lattice.gauge; simp only [increment,spinRow,exp_adjoint]
      change G' i.1*_*_=G' i.1*_* (G' i.1)⁻¹*(G' i.1*_*_); unfold G'; group
    rw [show P' i=gauge G' (increment (replica S.ratio V) a) i by unfold P' Lattice.gauge; rw [ht i hi],hf];
    unfold u shaft increment; rw [hv i hi,replica_near he i hi]; rfl
  unfold squarepot ivy
  rw [← winds z U V H.accepted s o k true, rivers H o k k (he.shrink (by rw [separation_self]; omega)) (hx.shrink (by change separation b b+_≤_; rw [separation_self]; omega)) ?_ true]
  swap
  · intro i hi; exact prediction_near_eq hl _ _ k i (hx.shrink (by simp only [id_eq] at hi; unfold b; omega))
  refine congr_arg₂ (·-·) rfl (Finset.sum_congr rfl fun i hi=> ?_)
  change ‖freely _ _ _ _ _+_‖^2/2=‖freely _ _ _ _ i+_‖^2/2
  have hf : focus S i=b := by rw [cost_is_here i,(parent_iff ..).1 hi]
  let R:=till s; let p:= he.shrink (q':=focus S i) (D':=B/4) (by rw [hf]; change separation b b+B/4≤d; unfold B; rw [separation_self]; omega)
  rw [← G.norm_adjoint (z (focus S i)),map_add, ← peony z H.accepted, ← under T hP]
  rw [show straightened T (till s) V' (spinRow S z a) i=straightened T R w x.snd i from ?_]
  · unfold freely baseStroke; rw [entry_stencil H _ _ _ _ k i (replica_near p) p, shoreVisa H i p]
  refine short_near T hl _ _ _ _ _ i (B/4) ?_ p ?_
  · unfold B; have hz:=H.frame; unfold till; omega
  intro j hj; apply hv j; change separation (focus S i) _≤_ at hj; rw [hf] at hj; unfold b at hj; omega

end YM.ConnectedActivityE6.Blaze.Frond
namespace YM.ConnectedActivityE6.Blaze.Silica.Clutch
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a α β γ d η σ W s b μ : ℝ} {j : ℕ}
open Brush
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {V : E → Config G c} {y : E→ Directions G f} {w : E→ Air f G}

lemma torchR2 (p : Room P S T X.x) (h : Clutch X z a β s x j V y w) (hp : Mode V x j d) (H : X.manifest)
    (i : Stream c f) (hk : ¬ Inside (rowSite S i) X.seeds (200*X.B)) (hψ : ¬ (fun k=> X.enforce (2*a) (y k) (X.booth (rowSite S i)))=ᶠ[𝓝 x] fun _=>0) :
    let K:= i.1; let _o := rowSite S i; let v t:=vary X (V t)
    let U:= X.input (worldZ X β z); let Z t:=pull K 0 (V t)
    let A k:= displacement K ((v k).signal (y k)) (replica S.ratio (V k)); let m:=7*X.B/8; let p:=s+4*a*X.t
    let F:= royalty G*(p*royalty G)
    Clean ((fun y=>pull K 0 (V y)) x) X.x (lead S i.2) (m+1) ∧
      (∀ j', distAt S j' (lead S i.2) ≤ m → Brush j (F*(1+(d+1+d))^j) 1 (fun k=>A k j') x) ∧
      (∀ᶠ k in 𝓝 x, AgreeNear S.ratio.parent (lead S i.2) m (pull K 0 U) (increment (replica S.ratio (Z k)) (A k))) ∧
      ∀ k, rootface (v k) (y k) U true K i.2= squarepot T X.x (choice K X.k) (pull K 0 U) (Z k) (A k) i.2 := by
  intro K o v U Z A m u B
  have he : 100 ≤ X.B := p.sight.1; have hM := h.pulse
  obtain ⟨hv,hq⟩ := darling h _ hψ
  have hh q (hi : distAt S q o≤ X.B) : q∉F.trunks → X.Hot q := fun hz=> far_active X.seeds F q (clear hk (by unfold distAt o at hi; omega)) hz
  have ho : ¬ Inside o X.seeds X.B := clear hk (by change X.B+separation o o≤_; rw [separation_self]; omega)
  refine ⟨?_,?_,?_,?_⟩
  · dsimp only; rw [h.atV]; exact ((clean_far X.seeds X.V H ho).shrink (v:=o) (D:=m+1) (by rw [separation_self]; unfold m; omega)).turn
  · intro i' hI
    have hz : distAt S (Channel.edge K i') o ≤ X.B := (projects S K (lead S i.2) i').trans (by unfold m at hI; omega)
    have hF : Brush j u 1 (fun k=> (v k).signal (y k) (edge K i')) x := by
      by_cases ht:edge K i'∈F.trunks
      · simp_rw [(v _).on_trunk _ _ ht]; apply (Brush.certified zero_le_one (0:G.Color)).climb _ le_rfl
        have hp:=h.price; rw [norm_zero]; unfold u; nlinarith only [hp,hM]
      have hk:∀ k, (v k).Hot _ := fun k=> hh _ hz ht
      simp_rw [(v _).at_hot _ _ (hk _)]; exact hv _ (X.ages _ _ (hh _ hz ht) hz)
    exact (displacement_pay (S:=S) K i' u _ hp hF).trim
  · filter_upwards [hq] with k hY
    have hp q (ht : distAt S q o ≤ X.B) : U q=increment (replica S.ratio (V k)) ((v k).signal (y k)) q := by
      by_cases hq : q∈ F.trunks
      · unfold U; rw [X.sliced _ q hq, increment,(v k).on_trunk _ _ hq,G.mat_lieExp_zero,one_mul]; exact
          (if_pos (F.trunk_internal (by simpa using hq))).symm
      have he:= hh q ht hq
      change X.input _ q=_; rw [← hY q (X.ages _ _ he ht),(v k).viewing _ q he]; unfold increment; rw [(v k).at_hot _ _ he]; rfl
    unfold Z A; rw [← pulls_replica,← pull_increment]
    exact Zone.nearU S K (fun q hF=> hp q (hF.trans (by unfold m; omega)))
  intro k
  unfold rootface squarepot; refine congrArg₂ (·-·) rfl ?_
  apply sum_congr rfl; intro p hp
  have hx : (v k).selected K (spot S p) := by
    rw [(parent_iff (S:=S) ..).mp hp]
    exact
      clear hk (by change 6*X.B+separation o o ≤_; rw [separation_self]; omega)
  rw [Blaze.Vine.pot,if_pos hx]; rfl

end YM.ConnectedActivityE6.Blaze.Silica.Clutch
