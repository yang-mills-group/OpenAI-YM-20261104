import YM.RG12.Arche.Select
import YM.MergeProof.East.Suds
import YM.OPE.Cards.Pressure
/-!
# Unmarked pair comparison at a station
Include arbitrary engineering letter axes (even null), at possibly different horizons, full
comparison to the leading free pair to drive nearfree tests and upper log prices. Ladd uses
mag (ratio to capture spacing) throughout. No actual coefficient matching assumptions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Arche
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open MergeProof Analysis Next.UVStress Climb Ward MergeProof.East
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{ϕ : Filter UVIndex}{l:Filter UVIndex}[l.NeBot] {M:∀ d, ℕ→RepChart C d}
  {d n D k N p m:ℕ}
  {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ β δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (P:ι → Tapes.Panel D) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ β δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
local notation "F!"=> standard C
variable (z:ℝ) (hZ : ∀ i≤D,MergeProof.Accent.generator G i≤ z) (x:ι)
local notation "a!"=> (P x).arc

/- raw estimate from lava_v. Compare *any* y, even on potentially redundant lists (using
full rank estimate machinery). Only call for m = 1 below. -/
include H h hp hZ
lemma literal {R:Set (Points (m+1))} (t:Fin (m+1) → Fin (D+1)) (y:(i:Fin (m+1))→ C.label (t i)) (hR:IsCompact R)(hi:R⊆ conf (m+1))(hn:2≤n)(hn':m+1≤n)
    (f:Extraction.Order) (hF:(F!).Smooth) :
    ∃ c:ℝ,0≤ c ∧ ∀ᶠ k in atTop, ∀ T, Poised P B H O J n z k T→
      ∀ i:Fin (m+1)→ Cover, let y₀:= tag (mag A a! k)⁻¹ i; y₀∈R→y₀∈ generic _→ f.late fun N p=>
      let v j:= ladd C (mag A a! k) k N p (t j) (T N p (t j)) (y j)
      ‖C.numeric N p (q_asked (C:=C) v) (fun x=>location C.S k N p (i x))-disc (jointX y) y₀‖ ≤ c*Ship.budget A n k:=by
  let O' (r):= Poly.price (fun _=>1) (Read.maxProfile C r (jointX y))
  have hT: ContinuousOn O' R:= by
    unfold O' Read.maxProfile Poly.price; exact continuousOn_finsetSum _ fun i _=>continuousOn_const.mul ((Read.profile_part_cont (F!) hF _ _).norm.mono hi)
  obtain ⟨c,hc⟩ := (hR.image_of_continuousOn hT).bddAbove
  obtain ⟨b,hb⟩:= (hR.image_of_continuousOn continuous_norm.continuousOn).bddAbove
  have ha:0<a!:= by have hh:=(P x).huge; linarith [Nat.cast_nonneg (α:=ℝ) D]
  refine ⟨max c 0, le_max_right ..,?_⟩
  filter_upwards [lava_v P B H h hp O J z hZ y x hR hi hn hn', open_read h ha b (A) (m+1)] with k he ht T hT i q hr hΓ
  obtain ⟨h1,h2⟩:= authentic (V:=A) (k:=k) (b:=a!) i
  have hA:Allowed A a! k:=by obtain ⟨l,r,u,h⟩:= hT.supply x; rw [← (P x).factor ((A).clock.J k) ]; exact u.age.allot.permitted
  have hv:Fit A a! k q:= ht hA i hΓ (hb (mem_image_of_mem Norm.norm hr))
  unfold Order.late
  refine Eventually.of_forall fun l=> ?_
  have qc := f.mesh.cofinal.eventually (eventually_all.mpr (fun r : Fin (m+1)=>hv.stencils (F:=C) H (t r)))
  filter_upwards [qc, f.mesh.cofinal.eventually_gt_atTop k] with j hj hx
  let Q:=f.mesh j;let p:=f.per l
  let v:(j:Fin (m+1))→ C.label (t j):=fun j => ladd C (mag A a! k) k Q p (t j) (T Q p _) (y j); let W:= q_asked (C:=C) v
  have hg: ∀ s,s.val.Nonempty→ (Ship.yard C a! (show k≤ Q from hx.le) p).rootTest (C.beta Q p) (fun U=> (Ship.invoice (jointX y) W hv Q p U).part s) ≤ Ship.budget (A) n k:=he T hT Q p hx q (h2.symm ▸ hr) hv
  have hG:∀ j,Interior _ (Read.probes C Q p k (Next.Rank.Station.choose (A) a! k q) W j):=fun j=> (hj j).choose_spec p j (v j)
  have hm:= (Ship.budget_pos (A) n k).le
  have hf:= Read.full_cost H (Ship.fitting hv) hm (Ship.yard C a! (show k ≤ Q from hx.le) p) hG hg
  change Next.Rank.Station.choose A a! k q=i at h1; change Next.Rank.Station.tested A a! k q=q at h2; rw [h1,h2] at hf
  apply hf.trans
  exact mul_le_mul_of_nonneg_right ((hc (mem_image_of_mem O' hr)).trans (le_max_left ..)) hm


variable {S : Table C.book} {f: Extraction.Order}
-- simplification of homogeneous unselected pair reading
def pair (S : Table C.book) {d e : ℕ} (x : Points 2) (v : S.Field d)(w:S.Field e) :=
   disc ![(⟨d,v⟩:S.Tag),⟨e,w⟩] x
-- also works on F! (labels register Maxwell.standard)
def freePair (C : Family G) {d e : ℕ} (x : Points 2) (v : C.label d)(w:C.label e) :=
   let Z:=standard C
   disc ![(⟨d,Z.project d v⟩:Z.Tag),⟨e,Z.project e w⟩] x

def name_pair {j i:ℕ} (v : C.label j)(w : C.label i) : C.book.Vector ![j,i] := Fin.cases v (Fin.cases w fun i=>Fin.elim0 i)
omit H h hp hZ in
private lemma boxed {L : Register G} (S : Table L){j i:ℕ} (x : Points 2) (h:S.Symmetric) (hv:x∈conf _) (v:L.Vector ![j,i]) :
   S.value ![j,i] x v=disc ![(⟨j,S.project j (v 0)⟩:S.Tag),⟨i,S.project i (v 1)⟩] x:=by
   let t:=fun r:Fin 2=> (⟨![j,i] r,v r⟩:L.Token)
   have hf: ![(⟨j,S.project j (v 0)⟩:S.Tag),⟨i,S.project i (v 1)⟩]=S.classTokens ∘ t:=by funext q; fin_cases q<;>rfl
   rw [hf]; exact (S.at_project S h (fun _ => by tauto) hv t).symm -- sig?

/- Compare at the true length, in the unselected physical field quotient of S. Don't take a
  cutoff filter across moving k inside this statement (Poised only prices fixed k in the
  filter limit). In this view varying actual regulator lists with k are accounted through the
  FUSE data for all k and lamps read at any one scale at a time.
-/
lemma at_lamps (hP:f.PointLimits C S) (hF:(F!).Smooth) (hh:S.Symmetric)
    (hobs:Observing C H ϕ M)(hb: ϕ≤ f.fuse) (j i : Fin (D+1)) (v : C.label j)(w:C.label i)
    {R:Set (Points 2)}(hR:IsCompact R)(hi:R⊆ conf 2)(hn:2≤n) :
    ∃ c:ℝ,0≤ c ∧ ∀ᶠ k in atTop,∀ T : ℕ→ℕ→TableL C D, ∀ _:Poised P B H O J n z k T,
      ∀ (Z:∀ i:Fin (D+1),Module.End ℂ (C.label i)), Comparer (ϕ:=ϕ) (hC:=H) l k D T (mag A a! k) Z→
        ∀ b:Fin 2→ Cover, let y:= tag (mag A a! k)⁻¹ b; y∈R → y∈generic 2→
          ‖pair S (Order.grid C k b) (S.project j (aligned C M k (Z j) v)) (S.project i (aligned C M k (Z i) w))- freePair C y v w‖ ≤ c * Ship.budget A n k:=by
  let t(j i:Fin (D+1)):= ![j,i]
  let e:(r:Fin 2) → C.label (t j i r):= Fin.cases v (Fin.cases w fun i=>Fin.elim0 i)
  obtain ⟨c,hc,Hc⟩:= literal P B H h hp O J z hZ x (m:=1) (t j i) e hR hi hn hn f hF
  refine ⟨c,hc,?_⟩
  filter_upwards [Hc] with k hk T hT Z hC b y hy he
  have hd:= hk T hT b hy he
  let t':=![j.val,i.val]; let μ:= mag A a! k
  let W (p:UVIndex)(d:Fin (D+1)):= ladd C μ k p.1 p.2 d (T p.1 p.2 d)
  let Y (i:Fin (D+1)):=aligned C M k (Z i)
  let V:= name_pair (Y j v) (Y i w); let V₀(p:UVIndex):=name_pair (W p j v) (W p i w)
  have hv r : Tendsto (fun p=> V₀ p r) l (𝓝 (V r)):=by
    fin_cases r
    · exact tends_aligned hobs hC j v (hT.early _ j.is_le)
    exact tends_aligned hobs hC i w (hT.early _ i.is_le)
  let U:=Order.grid C k b
  have hμ:0 < μ:= Station.mag_pos ..
  have hab:(U∈generic 2):=by
    intro x' r s hX
    apply (he x')
    have h : ((b r x':ℤ):ℝ) = b s x':=mul_left_cancel₀ (C.S.a_pos k).ne' (show C.S.a k * _ = C.S.a k*_ from hX)
    change μ⁻¹*((b r x':ℤ):ℝ)=μ⁻¹*((b s x':ℤ):ℝ);rw [h]
  have hs:= OPE.Cards.variation b hP hab V V₀ hv (hC.filter_le.trans hb)
  have ht:= (hs.sub_const (freePair C y v w)).norm
  have hK(u:UVIndex):
       let c(r:Fin 2):= ladd C μ k u.1 u.2 _ (T u.1 u.2 (t j i r)) (e r)
       C.ensemble t' (fun x=>location C.S k u.1 u.2 (b x)) (V₀ u)=C.numeric u.1 u.2 (q_asked (C:=C) c) (fun x=> location C.S k u.1 u.2 (b x)):=by
     intro c
     change C.numeric u.1 u.2 (fun i=> (⟨t' i,V₀ u i⟩:C.book.Token)) _=_
     congr 2
     funext q; fin_cases q<;>rfl
  have hD:disc (jointX e) y=freePair C y v w:=by
    unfold freePair; congr 1; funext r; fin_cases r<;>rfl
  rw [show pair S (Order.grid C k b) (S.project j (aligned C M k (Z j) v)) (S.project i (aligned C M k (Z i) w))=S.value t' U V from (boxed _ U hh (generic_conf 2 hab) V).symm]
  refine le_of_tendsto ht (((show ∀ᶠ u : UVIndex in f.fuse,
     ‖C.numeric u.1 u.2 (q_asked (C:=C) (d:=fun r => ((t j i r):ℕ)) (fun r=> W u (t j i r) (e r))) (fun x=>location C.S k u.1 u.2 (b x)) - disc (jointX e) y‖ ≤ c * Ship.budget A n k from hd).filter_mono (hC.filter_le.trans hb)).mono fun i hi' => ?_)
  change ‖C.ensemble t' _ (V₀ i) - freePair _ y v w‖ ≤ _
  rwa [hD,← hK] at hi'
end YM.RG12.Arche
