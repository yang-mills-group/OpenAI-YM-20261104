import YM.AnalyticNext.GRID_STOP_ATTENUATION.Sparse
import YM.MergeProof.Figment
import YM.MergeProof.Marimba
import YM.MergeProof.Parterre
import YM.MergeProof.Canopy
import YM.OPE.Compatible.Eyrie.Fig
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Next.Foundations Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference Opening
open Labels
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}(H:C.Makes)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Scrim C W u ψ φ δ ζ r D)(hF:Fridge C u ζ){f:Extraction.Order} {N p d:ℕ} (V:SectionData (C.labels.level d)) (hV:V.Sound C.params)
set_option quotPrecheck false
local notation "K"=> C.path.levels.budget
local notation "F"=> C.labels.level d
local notation "T"=> C.localSection d
local notation "X"=> V.stencil∪(C.localSection d).stencil
local notation "S!"=> C.path.levels.params
local notation "Q"=> sphere
open scoped Classical
section
-- an additional quantitative local Haar cost at every support horizon
open OPE.Eyrie
def balm (V:SectionData (C.labels.level d))(i p:ℕ)(w:C.label d)(j:(C.labels.level d).Index)(E:ℕ→ℝ):Prop:=∀ k:ℕ,C.ref d≤ k→∀ hm:k≤ i,∀ b:ℝ,0≤b→nik k d p C b → ∀ U,‖OPE.Eyrie.puff C.path i p d (initial V C.path i p (Size.axis (C.labels.level d) j) 0-initial (C.localSection d) C.path i p w 0) hm U‖ ≤ Real.exp (rhoE (C.path.rep i p k))*b*(E i/gainChart C.path i k)
structure Sun (V:SectionData (C.labels.level d)) (E:ℕ→ℝ) (U:ℕ→ℕ→(C.labels.level d).Index→ C.label d) : Prop where
   stamps : ∀ᶠ N:ℕ in atTop,∀ p:ℕ,∀ j, balm V N p (U N p j) j E
end
include H B h hF
variable (hG:G.Simple)
include hG hV
lemma glowT_is {b:ℕ→ℝ}(he: Braze (C:=C) V b): ∃ E P U,Hearth (C:=C) V ζ E P U∧ Sun V E U :=by
    let Y(i):= sphere (S! i) ((X).card) (b i); let Z(i):= storms (BasisCost.price V) (BasisCost.price (T)) C i d; let hE(i):=Real.exp (((K i).supportExponent+2)*81); let E(i):= 4*(1+(S! i|>.columns))*Y i+hE i*Z i*ζ d i*(u i)⁻¹
    have hw : ∀ᶠ N:ℕ in atTop, ∀ p:ℕ,∃ V':C.label d≃ₗ[ℂ] C.label d,∃ Z': (C.labels.level d).Index → C.label d, (∀ i:C.label d,V' i=decor F Z' i)∧(∀ i,(F).coeffSize (V'.symm i)  ≤  2*(F).coeffSize i)∧ ∀ j,matter V N p Z' j ζ E ∧ balm V N p (Z' j) j E:=by
       have hP:= (eventually_all_finset (X)).mpr (fun (x : Cover) (_:x∈X)=> eventually_all.mpr fun i:Axis=> Mark.lengths C.S (20*((x i).natAbs+1)))
       filter_upwards [sanded hG C d (BasisCost.price V) (BasisCost.price (C.localSection d)) (zero_le_one.trans (BasisCost.price_pos _)) (zero_le_one.trans (BasisCost.price_pos _)),cover_tops (C:=C) hG X,mitt (C:=C) hG X, hP,he.arc,he.flight,he.hymns,eventually_gt_atTop (C.ref d)] with i ht hh hi hL hA hB hb hx p
       have hlx(j:(C.labels.level d).Index):∃ w:C.label d,(F).coeffSize (Size.axis F j-w) ≤ sliver F∧ balm V i p w j E∧∀ k m:ℕ,C.ref d  ≤  k→k < i→Stock.Tabs.opens C.path.levels 1 m k→∀ a:Motion,∀ hm:m  ≤  i,(center C.S p hm 0).rootTest (C.beta i p) (dance a (initial V C.path i p (Size.axis F j) 0-initial (T) C.path i p w 0))  ≤  cider C ζ d m k*E i*RelayDifference.flight C (-RelayDifference.gamma) (i,p):=by
          obtain ⟨Y',t',hc',hz⟩:= inviting V hV H hx.le (p:=p) (fun v hv j=> hL v hv j p) hA hb.1 u ζ (hF.candle i) (h.grows _ _ hx.le).le (Classical.choice (hF.full i p)) ⟨hi p,hh p⟩ ht j
          obtain ⟨v,hv,hθ,hT⟩:= FigP C i p d B W u ψ φ δ ζ r D H h (initial V C.path i p (Size.axis F j) 0) Y' (Y i) t' (E i) hx hc'; rw [hz] at hv; refine ⟨_,le_of_mul_le_mul_left (hv.trans hB) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (C.S.block (i-1)).property) _), ?_,fun k m hi ht hb a hm=> hT m k hi ht hb a hm⟩
          intro k hk hm b' hb hC U; exact hθ k hk hm b' hb hC U -- C.O v.simp ?

       choose t he hB hT using hlx; obtain ⟨V',hV,ht⟩:= cheaper F t he; exact ⟨V',t,hV,ht,fun j=> ⟨hT j,hB j⟩⟩
    let candle (N p:ℕ)(V':C.label d≃ₗ[ℂ] C.label d)(Z': (C.labels.level d).Index→ C.label d):Prop:=(∀ i:C.label d,V' i=decor F Z' i)∧ (∀ i,(F).coeffSize (V'.symm i)  ≤  2*(F).coeffSize i)∧ ∀ j,matter V N p Z' j ζ E ∧ balm V N p (Z' j) j E
    have hh (N p:ℕ):∃ V' Z',(∃ v f,candle N p v f)→candle N p V' Z':=by by_cases h:∃ v f,candle N p v f; obtain ⟨v,f,h⟩:=h; exact ⟨v,f,fun _=>h⟩; exact ⟨LinearEquiv.refl ℂ _,fun _=>0,fun he=>(h he).elim⟩
    choose t P hT using hh; have hp:∀ᶠ N:ℕ in atTop,∀ p:ℕ,candle N p (t N p) (P N p):= hw.mono (fun N hi p=>hT N p (hi p)); refine ⟨E,t,P,⟨hp.mono (fun i hi p=>⟨(hi p).1,(hi p).2.1,fun j=> ((hi p).2.2 j).1⟩),fun f=>?_⟩, ⟨hp.mono (fun i hi p j=> ((hi p).2.2 j).2)⟩⟩
    have h₀: Slow C f fun i=> b i.1:= (beta_slow hG).below ((cutoff_grows f).eventually he.hymns)
    have hξ := Slow.pow (roof_of_tabs (f:=f) B) 81; have hX : Slow C f fun i=> Real.exp (81*(K i.1).supportExponent):= hξ.reduce (Eventually.of_forall (fun i=> le_of_eq (by congr 1; rw [← Real.exp_nat_mul]; norm_num)))
    have ht : Slow C f fun i=> hE i.1:= (hX.mul (Slow.const (Real.exp 162))).reduce (Eventually.of_forall fun i=>le_of_eq (by unfold hE; congr 1; rw [← Real.exp_add]; ring_nf))
    have hY : Slow C f fun i=>Y i.1:= (Slow.const (C:=C) 2).add (hX.mul ((h₀.add columns_slow).add (Slow.const _)))
    have hz := Opening.seats_slow (C:=C) (f:=f) (d:=d) hG
    have hZ : Slow C f fun i=> Z i.1:= ((Slow.const _).mul hz).add ((Slow.const _).mul hz)
    exact (((Slow.const (C:=C) (4:ℝ)).mul ((Slow.const _).add columns_slow)).mul hY).add (((ht.mul hZ).mul (hF.smoke d _)).mul (hF.path _))
end YM.MergeProof
