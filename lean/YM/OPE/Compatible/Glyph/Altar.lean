import YM.OPE.Compatible.Glyph.Window
/-!
# Hands after station costs. Retain alpha. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Exterior WithLp Work.F08 Matrix Bloch Precision Stationary
open scoped Topology BigOperators Classical
variable {G:Gauge}{σ s a κ C e c γ Λ:ℝ}{j i u:ℕ}{Ω y:Side→ℝ}{P Q:Clip} (B:Sponsor G)
abbrev awardX (j:ℕ):ℝ:= Stationary.pacesE B.X j
abbrev Nudge (j i:ℕ)(a τ κ d s γ:ℝ)(u:ℕ)(β Λ: Side→ℝ):Prop:=Transition G B.K j (B.X.η j) (B.X.α j) (awardX B j) (B.γ j) (B.X.α i) (awardX B i) (B.γ i) a τ κ d s γ u β Λ
lemma handstone (R:Flight j i)(C L':Bed)(U:PathData G) (h:TicketBed B j P R.wing C)(hp:TicketBed B i Q R.land L')
    (hm:Mag j i)(ha:Nudge B j i a σ κ c s γ u Ω y)(hg:γ>0)(he:Attached C U)(hf: U.Bounds P σ a Λ)(hΛ:1≤Λ) (hh: u ≤ R.L.val)(L:ChartRatio G)(hT:LocalRatio L):∃ α:ℝ,∃ Y:PathData G, |α+G.slopeConstant*Real.log R.L.val|+1 ≤ c ∧ Pilgrim G R B.K P Q U Y α L ∧ Attached L' Y ∧ ∀ s' κ' Λ':ℝ, 0<s'→s'≤s→κ≤κ'→y R.L ≤ Λ'→ Λ/2≤Λ'→ Y.Bounds Q s' κ' Λ':=by
      obtain ⟨m,hm',hx⟩:=naturalHigh R.patch B.K (B.affordable R.patch); let n t:= m t*R.L; let g t:=R.visit B.K (c:=m t) (f:= n t) rfl; let f(t):= Woody.forest (g t).ratio R.odd
      let A:=Stationary.Armada.mk (m:=m) (n:=n) (P:=R.patch) (K:=B.K) (fun t=> (g t).sizes); let T:=R.duo B.K.penalty; let D:=B.X.η j
      have ht t : Towers.Diagonal (A.boot t) C L' T:= diagonal B.K _ _ (B.h.net _) (B.h.net _) R hm.2.1 C L' h.2.1 hp.2.1 rfl
      have hb:= ticket_hull B P R.wing C h n; have hB:= ticket_hull B Q R.land L' hp m
      obtain ⟨η,hη,H⟩:=(Bid.cospons Work.E02.answer Work.F01.answer Work.F02.answer Work.F03.answer Work.F04.answer R.L j B.K D (B.X.eta_pos j) (G:=G)).χ
      have hv t:= H (m t) (n t) (g t) rfl rfl rfl (hx t) (f t) C L' P Q U _ _ _ _ _ _ T (ht t) (hb.2.2.1 (n t)) hf he (hb.2.2.2 t) (hB.2.2.1 (m t)); choose x hX using fun t=> (hv t).2; let d(t):=x t
      have hg': Stationary.Headers (P:=R.patch) T.A0 2 (B.X.α j) (awardX B j):= by
         intro l hl; have hr:= hm.1; apply strip_mono ((B.h.hop j i hm R).1 l (by change l.length≤2 at hl; omega)).1 le_rfl ?_; change _ ≤ awardX B j/ ((R.L.val:ℝ) ^ (1+l.length)); apply div_le_div_of_nonneg_right _ (by positivity); exact paces_extend ..
      obtain ⟨Y,o,-,hO,hP,hY,hl,H'⟩:= ha m n R.patch A P Q U f x C L' T _ _ _ L rfl hh hm' h.1 hp.1 ⟨hx,hb,hB,he,hf,hg',ht,fun i=>(hv i).1,fun i=>(hX i).1,fun i=>(hX i).2.1,fun i=>(hX i).2.2⟩ hΛ hη hT
      exact ⟨_,_, hY, ⟨m,hm',Ω R.L,γ,1,hg,fun i=> ⟨hx i,x i,(hX i).1,hl i,H' _ _ le_rfl le_rfl i⟩⟩, hO,hP⟩ -- parens
lemma moonX (i j:ℕ)(h:G.Simple):∃ κ s:ℝ,0≤κ ∧ 0<s ∧ ∀ τ a:ℝ,0<τ→0≤a→∃ c γ:ℝ,∃ u:ℕ,∃ Ω μ:Side→ℝ, 0≤c ∧ 0<γ ∧ Nudge B j i a τ κ c s γ u Ω μ := by
      obtain ⟨x⟩:= colorAvail _ h; obtain ⟨κ,s,ha,hb,H⟩:= transition_cap G x h B.K j (B.X.η j) (B.X.α j) (awardX B j) (B.γ j) (B.X.α i) (awardX B i) (B.γ i) (B.X.eta_pos _) (B.X.alpha_pos _) (paces_pos ..) (B.h.fit _|>.le) (B.X.alpha_pos _) (paces_pos ..) (B.h.fit _|>.le)
      refine ⟨κ,s,ha,hb,fun τ a hx hy=>?_⟩; exact H _ _ hx hy (pouring G h _ _ _ _ _ _ (B.X.alpha_pos _) (B.X.eta_pos _) (paces_pos ..) (B.h.fit _ |>.le) hx hy)
end YM.OPE.Votive
