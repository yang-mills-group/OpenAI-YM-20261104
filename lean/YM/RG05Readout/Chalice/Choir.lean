import YM.RG05Readout.Chalice.Cantus
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Chalice
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Petals Petals.Kernel Bay Dash

/-!
# Reconciling actual appointments and limit maps
 Issued at all levels k≥common.Adapter per representation ticket
 via density equality; any closure using deeper local mounts for projection
 estimates may match this same U data. Tuning passes first in theta. No renewal
 of f. Provides boarding pass at finite regulators. -/
variable (V V':Sight C d p) (E E':Emblems C d)
include h
private lemma same_here (hw: Awake D B b d)(hV: Spine D B h b p d N V E)(hp: Spine D B h b p d N V' E') : ∀ i:ℕ, b ≤ i → i ≤ N→(∀ x:Palette C d,pulseOut (V i x)= pulseOut (V' i x))∧ ∀ k:ℕ,i≤k→k<N→ E k=E' k:=by
   intro i hb hh; induction hh using Nat.decreasingInduction with
   | self=> exact ⟨fun x=> by rw [hp.starts,hV.starts],fun k hi he=> by omega⟩
   | of_succ i hi ih=>
      obtain ⟨hz,hζ⟩:= ih (hb.trans i.le_succ); have ht(x):pulseOut (V i (E i x))= pulseOut (V' i (E' i x)):=by
         funext f; rw [show pulseOut (V i (E i x)) f = _ from travels h hV (hm:=hi) (hp:=hb) f x, show pulseOut (V' i (E' i x)) f=_ from travels h hp (hm:=hi) (hp:=hb) f x]; rw [show pulseOut (V _ x)=pulseOut _ from hz x]
      have he:E i=E' i:=by
         ext1 x; obtain ⟨z,hz'⟩:=(hV.legal i hb hi.le).capacity0 (E i x); obtain ⟨q,hq⟩:=(hp.legal i hb hi.le).capacity0 (E' i x); exact germ_eyelet hw hz' hq hb hi (ht _)
      refine ⟨fun x=>?_,fun j hj h=>?_⟩
      · rcases (E' i).surjective x with ⟨a,rfl⟩; rw [he] at ht; exact ht a
      by_cases hg:i=j; exact hg ▸ he; exact hζ _ (by omega) h
lemma same_tuition (hw:Awake D B b d)(hV:Spine D B h b p d N V E)(ht:Spine D B h b p d N V' E') (hv:b ≤ N)(hK:b ≤ k)(he:k < N): E k= E' k:= (same_here h V V' E E' hw hV ht b le_rfl hv).2 _ hK he
variable {T S:YM.Table C.book}{L0:ℕ→YM.Table C.book}{P:DiffPlan T}{R:Dash.Bin S}(H:Next.Extract.Base C f S L0 R T P)
variable (dims:ℕ→ℕ) (Y:∀ d:ℕ,Cutoffs→ Emblems C d)
structure Anchored (D:Address.Rail C)(B:ℕ→ℕ→ℝ)(h:C.Makes)(t:ℕ→ℕ)(S:∀ d:ℕ,Cutoffs→ Emblems C d):Prop where
    age d: Awake D B (t d) d
    paid (j:Cutoffs)(d:ℕ) (ht:t d≤j.1): ∃ V:Sight C d j.2, Spine D B h (t d) j.2 d j.1 V (S d j)

variable (hq:Anchored (C:=C) D B h dims Y)
include hq
lemma Anchored.tracks (d:ℕ) : UniformM f (Y d) (dims d) D B h:= ⟨hq.age d, ((cutoff_grows f).eventually_ge_atTop _).mono fun j hi=>hq.paid j d hi⟩
omit hq
lemma opening (t:ℕ→ℕ)(hw:∀ d,Awake D B (t d) d): ∃ Y:∀ d:ℕ,Cutoffs→ Emblems C d, Anchored D B h t Y:=by
    choose Y hY using fun d (j:Cutoffs)=> show ∃ S:Emblems C d,t d ≤ j.1 → ∃ V:Sight C d j.2, Spine D B h (t d) j.2 d j.1 V S from (by
       by_cases hk:t d≤j.1; obtain ⟨V,S,hS⟩:= erect (p:=j.2) h (hw d) hk; exact ⟨_,fun _=>⟨_,hS⟩⟩
       exact ⟨fun _=>LinearEquiv.refl ℂ _,fun h=> (hk h).elim⟩); exact ⟨Y,hw,fun j d=> hY d j⟩

variable {g:Extraction.Order} {Z:∀ d:ℕ,ℕ→ Palette C d→ₗ[ℂ] C.label d}(hZ:Tune (dims:=dims) H Y g Z)
variable {w ζ}(A:OPE.Package C w ζ D)(L:Storage C D)(hG:G.Simple)(hT:∀ d,UVExt.Slots.StrongBin C R f d)
include H hq hZ hG L hT A
-- exact hierarchical fields in unselected kernel. That of all phases as functionals in Table.Constraint. See expansion after.
lemma choir {v:ℕ} (s:Fin v→ℕ)(u:(i:Fin v)→Cutoffs→Palette C (s i))(p:(i:Fin v)→ Palette C (s i))
    (Q:Fin n→C.book.Token)(F:Test (v+n)) {ℱ:Filter Cutoffs}[ℱ.NeBot](ht:ℱ≤ (f.refine g).fuse)(hx:∀ i:Fin v,Tendsto (u i) ℱ (𝓝 (p i)))(hy:∀ i:Fin v,∃ b:ℝ,∀ᶠ k in f.fuse,size (u i k)≤ b)(hk:∀ i,dims (s i) ≤ m): Tendsto (fun i:Cutoffs=> jointS F s (fun a=>fastU (Y (s a)) (u a) m) Q m i.1 i.2) ℱ
       (𝓝 (integrated F s Q (fun a=> Z (s a) m (p a)) T)):=by
     let F':=fun a=>fastU (Y (s a)) (u a) m; have he(i):Slow C f (F' i):=onboard h (Y _) _ (Anchored.tracks h dims Y hq _) (hk i) _ (hy i).choose_spec
     have hv(i:Fin v): ∀ᶠ k in atTop, ∃ x:Rowe C (s i), Reveals C f (code m k (F' i)) x∧ Tendsto x ℱ (𝓝 (Z (s i) m (p i))):=by
          have hK:= Petals.Tune.projection h (u i) H hT A L hG Y (Anchored.tracks h dims Y hq) hZ (hk i) ht (hx i) (hy i)
          exact hK.2.mono fun k hk=> ⟨hk.choose,hk.choose_spec.1.2,hk.choose_spec.2⟩
     exact passes_limits h F s F' Q H _ (ht.trans (Next.Extract.Tails.refine f g).fused) A hG he hv
end YM.RG05Readout.Chalice
