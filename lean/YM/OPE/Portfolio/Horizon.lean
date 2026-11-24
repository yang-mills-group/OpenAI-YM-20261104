import YM.OPE.Portfolio.Layout
/-!
# Absorb the portfolio overheads for orbit radii; no geometry propagation paid here -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float
open scoped Topology BigOperators Classical
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}{H:History G}{N p m i b:ℕ}
-- structural palette `S all`, alignment path and occupancy.
set_option quotPrecheck false
variable (L:Playout H p m N V){I:Type}[Fintype I][DecidableEq I]
namespace Playout
variable {r:ℕ→ℕ}{u:I→Site (H.S.side i p)}{s:Ward (Names V I)}{W W':I→ℝ}{δ ψ φ:ℕ→ℝ}
    {A: ∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}
variable (h:H.Selected)(ht:Thor H δ r A ψ φ b)
local notation "v"=> L.primary
local notation "P"=> (H.levels.budget i)
local notation "S"=> H.levels.clock.op i p
variable {q:Config G (H.S.side i p)→Poly (Names V I)}{f:I→Cup (H.rep N p i)}{C:I→ℂ}{x y:ℝ}
lemma Market.shy (hh:L.Market s u f q W x)(hx:∀ i,0<W' i)(hw:W' ≤ W)(hz:y≤x) : L.Market s u f q W' y:= ⟨hx, hh.tall.shrinks (fun i=> hh.width i.2) (fun i=> hx i.2) (fun i=> hw i.2) hz⟩

/-- Put payload on a prescribed single level (use updating also for
extending sections artificially above N). -/
lemma single {ι:ℕ→Type}{i:ℕ}(a:ι i)[∀ i,Inhabited (ι i)]: ∃ f:(i:ℕ)→ι i,f i=a:= ⟨update (fun _=>default) _ a, update_self ..⟩
lemma twins {ι:ℕ→Type}{i j:ℕ}(a:ι i)(b:ι j)(h:i≠j)[∀ i,Inhabited (ι i)]: ∃ f:(i:ℕ)→ι i,f i=a∧f j=b:=by obtain ⟨f,hf⟩:=single a; exact ⟨update f j b,(update_of_ne h b f).trans hf,update_self ..⟩

include h ht
lemma ArcMarket.peek (hl:m ≤ i)(hi:b ≤ i)(hn:i<N) (hh:L.ArcMarket s u f q W (δ i) (φ i) C) (he:L.occupied (r i) u) (hL:Trial s) (hw:∀ j,0<W' j) (hp:s.Cares (L.spectrum i u) (P).B (fun i':V×I=>δ i*W i'.2) (W' ∘ Prod.snd) (1/2)) : L.Market s u f q W' ((P).supportExponent):=by
    obtain ⟨k,hk,hY⟩:= hh.tall; refine ⟨hw,?_⟩
    obtain ⟨K,hK⟩:= single (ι:=fun i=> V×I→ℕ→ Config G (H.S.side i p)→ℂ) k; obtain ⟨X,hX⟩:= single (ι:=fun i=> I→ Cup (H.rep N p i)) f; obtain ⟨U,hU⟩:= single (ι:=fun i=> I→Site (H.S.side i p)) u
    have ht' :(fun i=> L.spectrum i (U i)) i=L.spectrum i u:= hU ▸ rfl; have hF: (fun i=> L.cupsReg i (X i)) i=L.cupsReg i f:=hX ▸ rfl
    have hE: Occupancy (L.spectrum i (U i)) (r i):=hU ▸ he -- maybe
    rw [hk]; let T:= L.cupsReg i f; have hQ: Buccaneer (H.rep N p i) L.permutation L.tint L.primary s (L.spectrum i (U i)) (L.positions i) (L.cupsReg i (X i)) (K i) q (fun j=> δ i*W j) (δ i) (φ i) (L.skater C):=by rw [hU,hX,hK]; exact hY
    have hf:= Buccaneer.pegs (o:=fun i=> L.spectrum i (U i)) (q:= L.positions) (F:=fun i=>L.cupsReg i (X i)) h ht hi hn hQ hE hL (fun i=> mul_pos (ht.suns _ hi|>.hats.1) (hh.width i)) hw (by change s.Cares (L.spectrum i (U i)) _ _ _ _; rw [hU]; exact hp) -- notation lam issue
    try dsimp only at hf
    rw [hU,hX,hK] at hf; exact hf
lemma Market.strides (hi:b ≤ i)(hl:m ≤ i)(hn:i<N) {y:I→Site (H.S.side (i+1) p)}{g:I→Cup (H.rep N p (i+1))} {q:Config G (H.S.side (i+1) p)→Poly (Names V I)} (hh:L.Market s y g q W x)(hφ:x≥(H.levels.budget (i+1)).supportExponent-4) (he:Integrable q (prior G _))
    (hp:∀ j,u j=(S).ratio.parent (y j))(hE:L.occupied (r i) y)(hX:L.occupied (r i) u)
    (hQ:∀ j,Cup.Edge S (A N p i hn) (g j) (f j) (y j) (u j) (C j) (W j)) : L.ArcMarket s u f ((S).push (H.rep N p (i+1)).beta q) W (δ i) (φ i) C:=by
    obtain ⟨k,hk,hK⟩:= L.representing f h hl hn.le; have hm:= hl.trans i.le_succ; obtain ⟨j,hj,hJ⟩:= L.representing g h hm hn
    choose M a t hf hA ht' hz₀ hD using fun b=>(hQ b).travel; refine ⟨hh.width,hz₀,k,hK,?_⟩
    let X:= L.spectrum i u; obtain ⟨V₀, h₁,h₂⟩:= twins (ι:=fun i=> I→Site (H.S.side i p)) u y (by omega); obtain ⟨Y₀,h₃,h₄⟩:=twins (ι:=fun i=> I→ Cup (H.rep N p i)) f g (by omega); obtain ⟨K,h₅,h₆⟩:=twins (ι:=fun i=> V×I→ℕ→ Config G (H.S.side i p)→ℂ) k j (by omega)
    let Q k:= L.positions k; let o k:= L.spectrum k (V₀ k); let p' k:= L.cupsReg k (Y₀ k)
    have hF:o i=L.spectrum i u:= congr_arg (L.spectrum _) h₁; have hG:o (i+1)=L.spectrum (i+1) y:=congr_arg (L.spectrum _) h₂; have h0 :p' i=L.cupsReg i f:=congr_arg (L.cupsReg _) h₃; have h1 :p' (i+1)=L.cupsReg (i+1) g:=congr_arg (L.cupsReg _) h₄
    have hJ0:tapes H p N K i=L.cupsRes i f:=by rw [hK]; unfold tapes; rw [h₅]
    have hJ1:tapes H p N K (i+1)= L.cupsRes (i+1) g:=by rw [hJ]; unfold tapes; rw [h₆];
    rw [← hF,← h0,← h₅]; refine crossing (o:=o) (q:=Q) (F:=p') (K:=K) h ht hi hn hh.width ?_ hφ (hG.symm ▸ hE) (hF.symm ▸ hX) he (L.accord hl hn) ?_ ?_ ?_ ?_ (h₆ ▸ hj) (h₅ ▸ hk) ?_ hA ht' ?_
    · rw [hG,h1,hJ1]; exact hh.tall
    · rw [hF,hG]; exact L.spectrum_step u hl hn hp
    · rw [hG]; intro j _ ; exact fun b=> L.roster y hm hn j b
    · rw [h1,hJ1]; exact L.rebind g C hm hn
    · rw [h0,hJ0]; exact L.rebind f C hl hn.le
    · intro b; rw [hJ0,hJ1,h1,hF,hG, L.principal y hm hn, L.principal u hl hn.le, L.attended g hm hn,L.fleur g hm hn,L.fleur f hl hn.le,L.pepped]; exact ⟨M b,hf b,hD b⟩
    intro b
    have h5: profile (H.rep N p i).activities (k (v,b))=(f b).leaves:=(congr_fun hK.symm _).trans (L.fleur f hl hn.le b); have h6: profile (H.rep N p (i+1)).activities (j (v,b))=(g b).leaves:=(congr_fun hJ.symm _).trans (L.fleur g hm hn b)
    unfold manifest; rw [h0,h1,h₅,h₆, L.attended f hl hn.le, L.attended g hm hn]; rw [coin_port _ _ (hk _) (Cup.held (f b)) (h5.trans (f b).fitted) (h.represents _ _ _ hn.le|>.good.labels), coin_port _ _ (hj _) (Cup.held (g b)) (h6.trans (g b).fitted) (h.represents _ _ _ hn|>.good.labels)]; exact (hQ b).income.symm
end Playout
end YM.MergeProof.Ribbons.ManyCopies.Cadet
