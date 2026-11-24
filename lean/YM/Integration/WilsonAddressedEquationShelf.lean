import YM.Integration.WilsonAddressedEquationTrajectory
import YM.MergeProof.Canopy

/-! Choose the measured Haar-equation filer together with the complete
represented cutoff input and its stable differentiated return. Every basis
coefficient uses its original signed projector and all admitted periods. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedEquationShelf
open MergeProof
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

def Issued (C:Family G) {d:ℕ} (V:SectionData (C.labels.level d)) (N p:ℕ)
    (W:Bid.Worth) (u ψ:ℕ→ℝ) (ζ:ℕ→ℕ→ℝ)
    (D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))
    (j:(C.labels.level d).Index) (E:ℝ) (x:C.label d) : Prop :=
  ∃ (Z:Coefficient (C.labels.level d) (C.side N p)) (t q:ℝ),
    Z.x=Size.axis (C.labels.level d) j ∧
    Cream C N p d u ζ (initial V C.path N p (Size.axis (C.labels.level d) j) 0) Z q t E ∧
    WilsonAddressedEquationTrajectory.NativeReturn C N p d W ψ D Z t
      (4*(1+(C.path.levels.params N).columns)*q) ((C.factory d N p).terminal x)

include H B h hF
variable (hG:G.Simple)
include hG hV
theorem elected {b:ℕ→ℝ}(he: Braze (C:=C) V b): ∃ E P U,Hearth (C:=C) V ζ E P U ∧
    ∀ᶠ N:ℕ in atTop, ∀ p j, Issued C V N p W u ψ ζ D j (E N) (U N p j) := by
    let Y(i):= sphere (S! i) ((X).card) (b i); let Z(i):= storms (BasisCost.price V) (BasisCost.price (T)) C i d; let hE(i):=Real.exp (((K i).supportExponent+2)*81); let E(i):= 4*(1+(S! i|>.columns))*Y i+hE i*Z i*ζ d i*(u i)⁻¹
    have hw : ∀ᶠ N:ℕ in atTop, ∀ p:ℕ,∃ V':C.label d≃ₗ[ℂ] C.label d,∃ Z': (C.labels.level d).Index → C.label d, (∀ i:C.label d,V' i=decor F Z' i)∧(∀ i,(F).coeffSize (V'.symm i)  ≤  2*(F).coeffSize i)∧ ∀ j,matter V N p Z' j ζ E ∧ Issued C V N p W u ψ ζ D j (E N) (Z' j):=by
       have hP:= (eventually_all_finset (X)).mpr (fun (x : Cover) (_:x∈X)=> eventually_all.mpr fun i:Axis=> Mark.lengths C.S (20*((x i).natAbs+1)))
       filter_upwards [sanded hG C d (BasisCost.price V) (BasisCost.price (C.localSection d)) (zero_le_one.trans (BasisCost.price_pos _)) (zero_le_one.trans (BasisCost.price_pos _)),cover_tops (C:=C) hG X,mitt (C:=C) hG X, hP,he.arc,he.flight,he.hymns,eventually_gt_atTop (C.ref d)] with i ht hh hi hL hA hB hb hx p
       have hlx(j:(C.labels.level d).Index):∃ w:C.label d,(F).coeffSize (Size.axis F j-w) ≤ sliver F ∧ Issued C V i p W u ψ ζ D j (E i) w ∧ ∀ k m:ℕ,C.ref d  ≤  k→k < i→Stock.Tabs.opens C.path.levels 1 m k→∀ a:Motion,∀ hm:m  ≤  i,(center C.S p hm 0).rootTest (C.beta i p) (dance a (initial V C.path i p (Size.axis F j) 0-initial (T) C.path i p w 0))  ≤  cider C ζ d m k*E i*RelayDifference.flight C (-RelayDifference.gamma) (i,p):=by
          obtain ⟨Y',t',hc',hz⟩:= inviting V hV H hx.le (p:=p) (fun v hv j=> hL v hv j p) hA hb.1 u ζ (hF.candle i) (h.grows _ _ hx.le).le (Classical.choice (hF.full i p)) ⟨hi p,hh p⟩ ht j
          obtain ⟨v,returned,hv,hT⟩:= WilsonAddressedEquationTrajectory.prescribed C i p d B W u ψ φ δ ζ r D H h (initial V C.path i p (Size.axis F j) 0) Y' (Y i) t' (E i) hx hc'; rw [hz] at hv; exact ⟨_,le_of_mul_le_mul_left (hv.trans hB) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (C.S.block (i-1)).property) _), ⟨Y',t',Y i,hz,hc',by simpa only [LinearEquiv.apply_symm_apply] using returned⟩,fun k m hi ht hb a hm=> hT m k hi ht hb a hm⟩
       choose t he keep hT using hlx; obtain ⟨V',hV,ht⟩:= cheaper F t he; exact ⟨V',t,hV,ht,fun j=>⟨hT j,keep j⟩⟩
    let candle (N p:ℕ)(V':C.label d≃ₗ[ℂ] C.label d)(Z': (C.labels.level d).Index→ C.label d):Prop:=(∀ i:C.label d,V' i=decor F Z' i)∧ (∀ i,(F).coeffSize (V'.symm i)  ≤  2*(F).coeffSize i)∧ ∀ j,matter V N p Z' j ζ E ∧ Issued C V N p W u ψ ζ D j (E N) (Z' j)
    have hh (N p:ℕ):∃ V' Z',(∃ v f,candle N p v f)→candle N p V' Z':=by by_cases h:∃ v f,candle N p v f; obtain ⟨v,f,h⟩:=h; exact ⟨v,f,fun _=>h⟩; exact ⟨LinearEquiv.refl ℂ _,fun _=>0,fun he=>(h he).elim⟩
    choose t P hT using hh; refine ⟨E,t,P,⟨hw.mono (fun N hi p=> ?_),fun f=>?_⟩,hw.mono (fun N hi p j => ((hT N p (hi p)).2.2 j).2)⟩
    · let z := hT _ _ (hi p)
      exact ⟨z.1,z.2.1,fun j=>(z.2.2 j).1⟩
    have h₀: Slow C f fun i=> b i.1:= (beta_slow hG).below ((cutoff_grows f).eventually he.hymns)
    have hξ := Slow.pow (roof_of_tabs (f:=f) B) 81; have hX : Slow C f fun i=> Real.exp (81*(K i.1).supportExponent):= hξ.reduce (Eventually.of_forall (fun i=> le_of_eq (by congr 1; rw [← Real.exp_nat_mul]; norm_num)))
    have ht : Slow C f fun i=> hE i.1:= (hX.mul (Slow.const (Real.exp 162))).reduce (Eventually.of_forall fun i=>le_of_eq (by unfold hE; congr 1; rw [← Real.exp_add]; ring_nf))
    have hY : Slow C f fun i=>Y i.1:= (Slow.const (C:=C) 2).add (hX.mul ((h₀.add columns_slow).add (Slow.const _)))
    have hz := Opening.seats_slow (C:=C) (f:=f) (d:=d) hG
    have hZ : Slow C f fun i=> Z i.1:= ((Slow.const _).mul hz).add ((Slow.const _).mul hz)
    exact (((Slow.const (C:=C) (4:ℝ)).mul ((Slow.const _).add columns_slow)).mul hY).add (((ht.mul hZ).mul (hF.smoke d _)).mul (hF.path _))
end YM.Integration.WilsonAddressedEquationShelf
