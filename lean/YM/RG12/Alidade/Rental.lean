import YM.RG12.Alidade.Stamps
/-! # Public criterion. Compared to `March` in Arche, doesn't require every intermediate
  positive-scale ratio; only the grids at k, with actual presentation columns, and
  refinement limit taken before the k tests. No assumed Wilson coefficient identity or
  extraction at all physical phases. In particular, avoids a requirement of interpolating
  aperture bounds at the coarse-to-fine transition between lenses. Still a SHARP
  demand (locally, through the missing anomaly comparison); not claiming that demand
  is proved from our physical comparisons in this checkpoint. Weiner unconditional result.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Set Filter Lattice RG Source Real Frames Commission Rail
open Extraction Bid MergeProof Org Spec PhysicalNext PhysicalNext.RankCovariance PhysicalNext.InteractingRank.Soft
open MergeProof.East Arche Shapes Roof RG12.Frames RG12.Desk.Paired YM.Pert.Dense
open PhysicalNext.Repeat.Legato.Bandage Next.Rank.Tapes.West Next.Rank Next.Rank.Atlas Station Prayer Perch Glimmer
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{d:ℕ}
variable (U:Final C f S) (Q:OPE.Prescription U.sector.derivatives)(hQ:Q.Coherent)
variable {φ:Filter UVIndex}[φ.NeBot]{M:∀ d,ℕ→RepChart C d}
variable (P:Port C){lit:ℕ→Prop}
variable (h:G.Simple)(hO:Observing C U.room.cutoff φ M)(hF: φ ≤ f.fuse) (H:OPE.Facilities C f S)
variable (i:Fin 3)(ax:Axis)
set_option quotPrecheck false
local notation "Z!"=>C.path.levels
local notation "χ"=> C.path.levels.clock.hatBeta
local notation "arc!"=> (P.panels d i).arc
local notation "B!"=> U.sector.derivatives
local notation "V!"=> wheelR U d
local notation "pencil"=>Desk.official Q hQ d
-- maintain exact same cut calendar and APIs
structure Route (P:Port C)(lit:ℕ→Prop)(H:C.Makes):Prop where
    free : Outbound P lit H
    prep : Beacon C.path.levels P.rate lit
    speed : Slurry C.path.levels

/-- Physical measured k requirements. For each lit installation (ports furnished from our
constructor), asks *adjacent lit pairs only*. Arbitrary mesh ratio and log-weight calendar.
Same-grade prices compare the actual pair evaluations at two lengths on later frame in its lens,
and take geometric dilation BEFORE shear as specified. DO NOT postulate this from unnormalized
phase-scheme, calibration Beta or UV existence. This is a producer dependency, e.g. to be derived
from two/three orders of normalized PT on the exact pilots, capturing only short joins. Theorem
below also grades the Stage-Leak version to show what quantitative bounds actually attained.
-/
def Proposal (d:ℕ)(lit:ℕ→Prop) (ax:Axis):Prop:= ∀ (φ:Filter UVIndex)[φ.NeBot],φ ≤ f.fuse→∀ M,Observing C U.room.cutoff φ M →
     let t(N:ℕ):=torchR C.path.levels (P.panels d i).arc N
     ∀ᶠ N in atTop,∀ (Z:ℕ→TableL C d)(Y:ℕ → Col (wheelR U d)≃ₗ[ℂ] S.Field d) (K:ℝ) (p:ℕ),
     Club M P U Q hQ φ d N ax lit i Z Y K p → ∃ s b:ℕ,Clearing C.path.levels Y (lens U d ax N∘t N) (t N) (fun _=>0) s b lit K

def MeltScale (C:Family G)(d k:ℕ):ℝ:=quote C.path.levels (trays d) k
-- export physical price tier; uncond.
structure Credible (P:Table C.book)(B:DiffPlan P)(M:∀ d,ℕ→RepChart C d):Prop where
    presents (d:ℕ)(x:P.Field d):∃ A:ℝ,0 ≤ A∧ ∀ᶠ k in atTop,∃ v:C.label d, P.project d (M d k v)=x∧mass C d v ≤ exp (A*MeltScale C d k)
    erase (d w:ℕ)(L:P.Field d→ₗ[ℂ]ℂ)(hw:w≤d): (∀ i:ℕ,∀ hi:i<w,∀ x:P.Field i,L (B.rise (hi.le.trans hw) x)=0)→∃ A:ℝ,0 ≤ A∧ ∀ᶠ k in atTop,∀ v:C.label d, ‖L (P.project d (M d k v))‖ ≤ exp (A*MeltScale C d k) / C.S.a k^(d-w)*mass C d v
variable (hr:Route P lit U.room.cutoff)
local notation:max "fair"=>U.room.cutoff
include hr h hO hF H
include Q hQ in
lemma weiner: Credible S (B!) M:=by
   have hT:=Rail.charter h U P hr.free H Q hQ hO hF
   obtain ⟨W,r,D,hM⟩:= H.costlier
   have hc(d):=Alidade.planned U Q hQ P hr.free h (hM.toPackage.toTableTickets.system) hO hF (0:Fin 3) hT (0:Axis) d 0 -- order
   choose N Z Y K p hn hC using hc
   have he(d):=melts h hO (hC d) hr.prep hr.speed
   exact ⟨fun d x=> (he d).1 x,fun d=> (he d).2⟩
-- filter output of credible. exact quantifiers
structure Flat (S:Table C.book)(B:DiffPlan S)(φ:Filter (ℕ×ℕ)):Prop where
    inlet (d:ℕ)(x:C.label d):∃ A:ℝ,0≤A∧∀ᶠ k in atTop,∃ (y:C.label d)(q:ℕ×ℕ→C.label d),S.project d y=S.project d x ∧ Tendsto q φ (𝓝 y) ∧ ∀ᶠ i in φ, Next.UVStress.quota C d k i.1 i.2 (q i)≤ exp (A*MeltScale C d k)
    outlet (d w:ℕ)(L:S.Field d→ₗ[ℂ]ℂ)(hw:w≤d): (∀ e:ℕ,∀ he:e<w,∀ x:S.Field e,L (B.rise (he.le.trans hw) x)=0)→∃ A:ℝ,0 ≤ A∧ ∀ᶠ k in atTop,∀ (u':Filter (ℕ×ℕ))[u'.NeBot],u'≤φ→∀ (q:ℕ×ℕ→C.label d)(x:C.label d)(z:ℝ), (∀ᶠ i in u',Next.UVStress.quota C d k i.1 i.2 (q i)≤z)→ Tendsto q u' (𝓝 x)→ ‖L (S.project d x)‖ ≤ exp (A*MeltScale C d k)/C.S.a k^(d-w)*z
omit hr h hF H in
lemma credible_flat (HE:Credible S (B!) M): Flat S U.sector.derivatives φ:=by
   constructor
   · intro d x; obtain ⟨κ,hκ,he⟩:=HE.presents d (S.project d x)
     exact ⟨κ,hκ,(he.and (eventually_ge_atTop (C.ref d))).mono (fun k hk=>(hO.characterize S d k hk.2 (l:=φ) le_rfl _ _).2 hk.1)⟩ -- implicit arg u?
   intro d w L hw hL
   obtain ⟨κ,hκ,he⟩:= HE.erase d w L hw hL
   refine ⟨κ,hκ,(he.and (eventually_ge_atTop (C.ref d))).mono (fun k hk u hu hf q x z hz he=> ?_)⟩
   obtain ⟨v,rfl,hv⟩:= hO.value d k hk.2 hf q x z hz he
   exact (hk.1 v).trans (mul_le_mul_of_nonneg_left hv (div_nonneg (Real.exp_pos _).le (pow_nonneg (C.S.a_pos _).le _)))
open OPE
omit hO hF [φ.NeBot] in
lemma sharps (hq:∀ d,4 ≤ d→Proposal U Q hQ P i d lit ax): (∃ ϕ:Filter UVIndex,ϕ.NeBot∧ϕ≤f.fuse∧OPE.Log.MatrixTicket S U.sector.derivatives ϕ) ∧ OPE.LogTrace U Q:=by
    have ht := matrix_ticket_from_limits h S (B!) f U.room.cutoff (fun b x hb M hM=> by
       have hA:=Rail.charter h U P hr.free H Q hQ hM hb
       have hz(d):RightPrice C S M d ∧ ∀ j, RowPrice C S (B!) M d j:=by
          rcases lt_or_ge d 4 with he|he
          · exact ⟨low_right_price h hM S d he,fun w=>low_row_price h hM S (B!) U.room.kernel.laws U.phase.transport.injection d w he⟩
          obtain ⟨W,r,D,hG⟩:= H.costlier
          obtain ⟨n,hn⟩:= eventually_atTop.mp (hq d he b hb M hM)
          obtain ⟨N,Z,Y,K,p,hδ,hR⟩:=Alidade.planned U Q hQ P hr.free h (hG.toPackage.toTableTickets.system) hM hb i hA ax d n
          obtain ⟨s,B,hS⟩:=hn N hδ Z Y K p hR
          exact supplied_if h hM hR hr.prep hr.speed hS
       exact ⟨fun i=>(hz i).1,fun i=>(hz i).2⟩)
    obtain ⟨φ,hφ,hL,hO⟩:=ht
    exact ⟨⟨_,hφ,hL,hO⟩,tickets_suffice U H hL hO hQ⟩
end YM.RG12.Alidade
