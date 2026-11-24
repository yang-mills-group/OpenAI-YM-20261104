import YM.OPE.Compatible.Lake.Highway
/-!
# Target physical switches. Non-local k paths only through one-step matching certificates on the whole trajectory; does not assume an eventual k price towards LOG OPE. Keep upstream foundations and subpower finite-mark claims.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot MergeProof Next.Extract Dash Extra.Histories
open Next.Rank Next.Rank.Price Extraction ContinuousLinearMap Treaty
open scoped Topology Classical BigOperators
variable {G:Gauge} {C:Family G} {d k i:ℕ}{H: Extraction.Order}{W:Table C.book} {E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)] [∀ i,FiniteDimensional ℂ (E i)]
variable (T:C.Makes)
structure Fountain (T:C.Makes)(H: Extraction.Order)(W:Table C.book)(E: Fin (d+1)→Type) [∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℂ (E i)]: Prop where
    rank : Module.finrank ℂ (W.Field d) = Module.finrank ℂ (Dock E)
    travel : ∃ k:ℕ,C.ref d≤ k ∧ ∃ (δ c:ℝ)(U r:ℕ→ℝ),0<δ∧0≤c∧ RateLE atTop (hill C) U 0 ∧ RateLE atTop (hill C) r (-1-δ) ∧(∀ i:ℕ,k≤ i→0 ≤ r i)∧
        ∀ f:Filter (ℕ×ℕ),f.NeBot→f ≤ H.fuse→ ∃ g:Filter (ℕ×ℕ),g.NeBot ∧ g ≤ f∧ ∃ Y:ℕ→ C.label d≃L[ℂ] C.label d, Conic T g Y∧Ferried k c U r d Y E W
namespace Fountain
variable {T} (h:Fountain T H W E) (hG:G.Simple)
include h hG
lemma appointed (hB:∀ᶠ i:ℕ in atTop,16 ≤ extent C i) : ∃ i D,Escort T H W d i D:=by
    obtain ⟨k,hk,δ,c,U,r,hd,hc,hU,hr,hj,hY⟩:=h.travel
    let q i:=stampErr (U i) (U i) (U (i+1)) (r i) (r (i+1)) (r i); have hp:= hill_high (C:=C) hG; have ht:-1-δ<0:=by linarith
    have hq:RateLE atTop (hill C) q (-1-δ):=fees U r (fun i=>U (i+1)) (fun i=>r (i+1)) hG hU (hop U hG hU) ht.le hr (hop r hG hr)
    have hx : RateLE atTop (hill C) (fun i=>q i*(1+2*U i^2)) (-1-δ):=by
       have he:RateLE atTop (hill C) (fun i=>2*U i^2) 0:=by simpa only [mul_zero,zero_add] using (RateLE.const 2 hp).mul (hU.pow 2 hp)
       simpa only [add_zero] using hq.mul ((RateLE.const 1 hp).add he hp)
    have hy : RateLE atTop (hill C) (fun i=> 2*(U i+r i)+((Fintype.card (C.labels.level d).Index):ℝ)*U i) 0:=
       (show RateLE atTop (hill C) (fun i=>2*(U i+r i)) 0 by simpa only [zero_add] using (RateLE.const 2 hp).mul (hU.add (hr.mono ht.le) hp)).add (by simpa only [zero_add] using (RateLE.const ((Fintype.card (C.labels.level d).Index):ℝ) hp).mul hU) hp
    obtain ⟨j,hJ⟩:= eventually_atTop.mp ((((hq.mul hU).tends (by simpa using ht) hp).eventually (ge_mem_nhds (by norm_num: (0:ℝ)<1/2))).and (((hr.mul hU).tends (by simpa using ht) hp).eventually (gt_mem_nhds (by norm_num: (0:ℝ)<1/2)))|>.and (eventually_ge_atTop k))
    obtain ⟨K,D,hx,hM⟩:= extend_drive (E:=E) hG hy hc hU hx hd W j hB
    have he:= hJ j le_rfl|>.2
    refine ⟨K,D,hk.trans (he.trans hx),fun f hf hl=>?_⟩; obtain ⟨g,hg,hp,Q,H,P⟩:= hY f hf hl
    obtain ⟨A,hA,hS⟩:= ferryman P hj he (fun i hi=> (hJ i hi).1.2) h.rank (fun i hi=> (hJ i hi).1.1)
    exact ⟨g,hg,hp,Q,H,E,inferInstance,inferInstance,hM Q A hA hS⟩
end Fountain
structure Concourse (T:C.Makes) (H:Extraction.Order)(W:Table C.book) : Prop where
    high : ∀ᶠ i:ℕ in atTop,16 ≤ extent C i
    plunges d: ∃ E:Fin (d+1)→ Type, ∃ _ :∀ i,NormedAddCommGroup (E i), ∃ _ :∀ i,NormedSpace ℂ (E i),(∀ i,FiniteDimensional ℂ (E i)) ∧ Fountain T H W E
lemma Concourse.tender {T:C.Makes} {P: DiffPlan W}(h:Concourse T H W)(hP:P.Inclusions W)(u:Services C H W) : Lanes (F:=H) P:=by
    apply escorting (T:=T) hP u; intro d
    obtain ⟨E,hE,e,hd,hR⟩:= h.plunges d; letI:=hE;letI:=e;letI:=hd; exact hR.appointed u.simpleGate h.high
end YM.OPE.Lake
