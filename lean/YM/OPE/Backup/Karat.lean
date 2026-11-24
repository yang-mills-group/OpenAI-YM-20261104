import YM.OPE.Backup.InGauge
/-! # Repeg reserves only after masking; compatibility just before grouping. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Muster
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Source
open Extra.Trajectories MergeProof.Float OPE.Backup
open scoped Topology BigOperators Classical
variable {V I : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]{G:Gauge}{n:Side}
local notation "X"=> Names V I
-- Repricing hull invariant
set_option quotPrecheck false
variable {D:History G}{δ σ θ :ℕ→ℝ}{m N p a:ℕ}
local notation "Γ"=> D.levels.clock.op m p
local notation "P₀"=> (D.levels.budget m)
local notation "P₁"=> (D.levels.budget (m+1))
local notation "S"=> D.S
variable (h:D.Selected) {A: ∀ N p m:ℕ,m<N→GaugeDoor (D.rep N p (m+1)) (D.rep N p m)} {r:ℕ→ℕ}
   (ht:Thor D δ r A σ θ a)
variable {W W':I→ℝ}{E:V→Motion}{B:V→ Equiv.Perm V}{v:V}{L:Ward (Names V I)}
    {o:∀ (m:ℕ),V×I→Site (D.S.side m p)}{F:∀ m:ℕ,V×I → Config G (D.S.side m p)→ℂ}{K:∀ m:ℕ,V×I→ℕ→ Config G (D.S.side m p)→ℂ}
    {Y:Config G (D.S.side (m+1) p)→ Poly (Names V I)}{q:∀ m:ℕ,V→ Site (D.S.side m p)}{u x y z:ℝ}

/-- Intermediate with provisional (paid-for) uptake including nonmasked
representation for *one* step. -/
structure Buccaneer (R:Rep G n) (B:V→ Equiv.Perm V)(E:V→Motion)(v:V)(L:Ward X)(o:V×I→Site n)(q:V→ Site n)(F:V×I → Config G n→ℂ)(K:V×I→ℕ→ Config G n→ℂ)(Y:Config G n→Poly X)(w:I→ℝ)(δ θ:ℝ)(c:V×I→ℂ) : Prop where
    move : ∃ Y':Config G n→Poly X, Arc R F K Y' v E q B o (w ∘ Prod.snd) (R.p.supportExponent+1/2) (R.p.supportExponent+1) 1 θ δ c ∧ ∀ U,L.Writes (Y U) (Y' U)
    gets i U : (Y U).part (X|>.fire i)=coin R (F i) (K i) U
    liq i : Dominated (K i)
lemma Buccaneer.shy {R:Rep G n}{Y:Config G n→Poly X}{o q F K c}(h: Buccaneer R B E v L o q F K Y W x y c) (hw:W' ≤ W)(hz:∀ i,0<W' i): Buccaneer R B E v L o q F K Y W' x y c:=by
    obtain ⟨Y',hp,hH⟩:= h.move; exact ⟨⟨Y',hp.reprice (fun i=> hw i.snd) (fun i=>hz i.snd|>.le),hH⟩,h.gets,h.liq⟩
lemma Buccaneer.coinPart {R:Rep G n}{Y Y':Config G n→Poly X}{o q F K c}{δ θ:ℝ}(h:Buccaneer R B E v L o q F K Y W δ θ c)(hp:∀ U,L.Writes (Y U) (Y' U)) (i U) : (Y' U).part (X|>.fire i)= coin R (F i) (K i) U := ((hp U) _ (L.fire i)).symm.trans (h.gets ..)
local notation "w!"=> (fun i:V×I=> W i.2)
local notation "R"=> (D.rep N p)
local notation "F!"=> (x+1/2:ℝ) -- simplify
variable (hi:a ≤ m)(hn:m<N) {c:V×I→ℂ}
include h ht hi hn
lemma Buccaneer.pegs {Y:Config G (D.S.side m p)→Poly X}(hc: Buccaneer (R m) B E v L (o m) (q m) (F m) (K m) Y W (δ m) (θ m) c)(hx:Occupancy (o m) (r m))(hp:Trial L)(hw:∀ i,0<W i)(hW:∀ i,0 < W' i)
    (hV:L.Cares (o m) (P₀).B (W ∘ Prod.snd) (W' ∘ Prod.snd) (1/2)) : Bard (R m) L v E B (q m) (o m) (F m) (fun i=>profile (R m).activities (K m i)) Y (W' ∘ Prod.snd) ((P₀).supportExponent):=by
    obtain ⟨Y',hP,hY⟩:= hc.move; let R':=D.rep N p m; have hxP: R'.p=P₀:=(h.represents N p m hn.le).vac
    let W'' : V×I→ℝ := W ∘ Prod.snd; have hw'(i:V×I):0<W'' i:= hw i.2
    have hθ:= ht.suns m hi
    have hS:Serves R' (F m) (fun i=>profile R'.activities (K m i)) Y' v E (q m) B (o m) W'' (R'.p.supportExponent+1/2) 1:=by
       have hc_:= hθ.stakes; rw [← hxP] at hc_
       apply thru (Z:=1) (u:=R'.p.supportExponent+1/2) (ζ:=0) (by rw [add_zero]; exact hP) (h.represents N p m hn.le).good.labels hw' hθ.hats.1.le hx (by linarith only [hxP ▸ hθ.exp.1]) ?_ hw' (by simp [Repegs]) zero_le_one (by norm_num) (by rw [one_mul]; exact hc_.2) (fun i U=> Buccaneer.coinPart hc hY i U) hc.liq (fun U=>(Tour.bright D h N p m hn.le U).ne')
       rw [add_zero]; exact hc_.1.trans_eq (by ring)
    exact Bard.care (e:=1/2) ⟨⟨Y',hxP ▸ hS,hY⟩⟩ hp (fun i=> hw i.2) (fun i=> hW i.2) (hxP.symm ▸ hV)

local notation "E1"=> (fun i=> (Γ).ratio.embed (q m i))
local notation "y1"=> (fun i=> (Γ).ratio.parent (o (m+1) i))
local notation "Ω"=> manifest D p N F K
lemma crossing {a' t':I→ℝ} (hw:∀ i,0 < W i)(hv:Bard (R (m+1)) L v E B (q (m+1)) (o (m+1)) (F (m+1)) (tapes D p N K (m+1)) Y (W ∘ Prod.snd) u)
    (hφ:u ≥ (P₁).supportExponent-4)(hO:Occupancy (o (m+1)) (r m)) (hO':Occupancy (o m) (r m)) (he:Integrable Y (prior G _)) (hq:q (m+1)=E1)(hy:o m=y1)
    (hX:∀ j,j≠v→∀ b:I,o (m+1) (j,b)=affine (E j).1 (q (m+1) j) (o (m+1) (v,b)))
    (hs:May v E (q (m+1)) B (F (m+1)) (tapes D p N K (m+1)) c)(hd:May v E (q m) B (F m) (tapes D p N K m) c)
    (hf:∀ i,Dominated (K (m+1) i))(hg:∀ i,Dominated (K m i))
    (hZ:∀ b:I,∃ l:Set Wing,l.Finite∧Tale l (o (m+1) (v,b)) (o m (v,b)) 1 (F (m+1) (v,b)) (tapes D p N K (m+1) (v,b)) (tapes D p N K m (v,b)) (c (v,b)) (a' b) (t' b) (A N p m hn))
    (hA:∀ i,2*W i*a' i ≤ 1)(hT:∀ i, W i*t' i ≤ 1)
    (hH:∀ b:I, Ω m (v,b)=(Γ).push (R (m+1)).beta (Ω (m+1) (v,b))) : Buccaneer (R m) B E v L (o m) (q m) (F m) (K m) ((Γ).push (R (m+1)).beta Y) (fun i=>δ m*W i) (δ m) (θ m) c:=by
    have hF1:= h.represents N p _ hn; have hF0:= h.represents N p m hn.le; obtain ⟨H,hQ⟩:= ht.moon N p m hi hn; have hU:= ht.suns m hi; obtain ⟨Y',hS,hY⟩:= hv.grants
    let q':=E1; let o':=o (m+1); let r0:=Γ; let f':= manifest D p N F K
    have hw'(i:V×I):0<W i.snd:= hw i.snd
    have hk:Occupancy (r0.ratio.parent ∘ o') (r m):= (show o m=r0.ratio.parent ∘ o' from hy) ▸ hO'
    have hB: Serves (R (m+1)) (F (m+1)) (tapes D p N K (m+1)) Y' v E q' B o' (W ∘ Prod.snd) ((P₁).supportExponent-4) 1:= (show Serves (R (m+1)) _ _ _ _ _ E1 _ _ (W ∘ Prod.snd) u 1 from hq ▸ hS).prune hw' hw' (x:=1) (t:=0) (by simp [Repegs]) zero_le_one (by linarith only [hφ]) (by norm_num) -- names. 
    have hξ: chimes v E (q m) B o' (r0.ratio.parent ∘ o') (F (m+1)) (tapes D p N K (m+1)) (tapes D p N K m) c Γ:= chimes_parent D (by rw [hq] at hX; exact hX) (hq ▸ hs) (fun j hp b=>((hd j hp).2 b).2.1) -- hs? numeric
    have h_Z (i:I):∃ l:Set Wing,l.Finite∧Tale l (o' (v,i)) (r0.ratio.parent (o' (v,i))) 1 (F (m+1) (v,i)) (tapes D p N K (m+1) (v,i)) (tapes D p N K m (v,i)) (c (v,i)) (a' i) (t' i) (A N p m hn):=by
       have ht:= hZ i; rw [hy] at ht; exact ht
    have hθ:Integrable Y' (prior G _):= unabridged hB H.tunes H.propagate hξ hF1.good hw' (fun _ _ _=>rfl) h_Z hO (b:=1) zero_le_one (by linarith only [hU.exp.2]) (by rw [hF1.vac]; linarith only) (fun i=>hA i.snd) (fun i=>hT i.snd) H.contact
    have HH : Arc (R m) (F m) (K m) ((Γ).push (R (m+1)).beta Y') v E (q m) B (o m) (fun i=>δ m*W i.snd) ((P₀).supportExponent+1/2) ((P₀).supportExponent+1) 1 (θ m) (δ m) c:= by
       rw [hy]; exact freshArc D N m p r h hn hU H hQ hw' hB le_rfl hO hk (fun _ _ _=>rfl) (fun i=>hA i.snd) (fun i=>hT i.snd) h_Z hξ (fun i=> hF1.good.labels.moves _ _)
    refine ⟨⟨_,hF0.vac.symm ▸ HH,Writes_push Γ (D.levels.transition_mass ..) he hθ hY⟩,?_,hg⟩
    intro i U; have h_u:∀ i,(fun U=> (Y U).part (X|>.fire i))=f' (m+1) i:=fun i=>funext fun U=> hv.fire U hF1.good.labels rfl hf i
    have h_pushed:(fun U=> ((Γ).push (R (m+1)).beta Y U).part (X|>.fire i))=(Γ).push (R (m+1)).beta (f' (m+1) i):=by rw [push_get (D.levels.transition_mass ..) he,h_u] -- spacing
    have hS:= h_pushed; suffices h':(Γ).push (R (m+1)).beta (f' (m+1) i)= f' m i from congr_fun (hS.trans h') U
    obtain ⟨i,j⟩:=i; by_cases hc:i=v; · subst i; exact (hH _).symm
    have hu1:f' (m+1) (i,j)=stepUp (E i) (E1 i) (f' (m+1) (v,j)):=by
       unfold f' manifest; rw [((hs i hc).2 j).1]; rw [← hq]; exact opals (E i) D h hn _ _ (hF1.good.labels.moves _ _).some (hf _) (hf _) ((hs i hc).2 j).2.1
    have h'_:May v E (q m) B (F m) (tapes D p N K m) c:= ‹May v E (q m) _ _ _ c›
    have hu0:f' m (i,j)=stepUp (E i) (q m i) (f' m (v,j)):=by
       unfold f' manifest; rw [((h'_ i hc).2 j).1]; exact opals (E i) D h hn.le _ _ (hF0.good.labels.moves _ _).some (hg _) (hg _) ((h'_ i hc).2 j).2.1
    rw [hu0,hu1,(show f' m (v,j)=_ from hH j)]; have he':Integrable (f' (m+1) (v,j)) (prior G _):= (h_u (v,j)) ▸ (show Integrable (fun U=> (Y U).part (X|>.fire (v,j))) (prior G _) from ((Poly.get (X|>.fire (v,j))).restrictScalars ℝ).integrable_comp he)
    have hz:= unison (E i) D m N p 0 (q m i) _ he'; simp only [blast,pow_zero,one_smul] at hz; exact hz
end YM.MergeProof.Ribbons.ManyCopies.Muster
