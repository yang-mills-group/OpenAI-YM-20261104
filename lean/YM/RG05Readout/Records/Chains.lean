import YM.RG05Readout.Records.Plaid
/-!
# Oriented crop consistency and placement comparison

At n upper mesh get `Eden` for normal unnormalized product at ANY J; no
constraints across log extrapolations assumed. Use this to initialize physical
coordinate readout signature. At n match result re-bring signed bundle
using TRUE simultaneous branch loans (incl counter). Costs on full policy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Records
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station
open Records.Basket Shadow
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d ℓ:ℕ}{I J V:Type}[DecidableEq V][Fintype V][DecidableEq J][Fintype J][DecidableEq I][Fintype I]
    {j b k g:ℕ}
variable (h:C.Makes){D: Address.Rail C} {ψ:ℕ→ℕ} {w:Worth} {B:ℕ→ℕ→ℝ}
    (Y:OPE.Package C w ψ D)(hC:Storage C D) (hS:Cater C D)
set_option quotPrecheck false
local notation "λ₀"=> C.path.levels.clock
local notation "R!"=> C.path.rep N p
local notation "Z!" => C.path.levels.budget
local notation "L"=>Unit × Recipe J V
local notation "L'"=>Unit × Basket.Root J
open Ribbons.ManyCopies
local notation "X!"=>C.side n p
local notation "J!"=> C.side N p
local notation "d!"=> Fintype.card (Color V)
local notation "t!"=> Ribbons.peepers C.path.levels n
-- continuity: rooted stencil sample finite support at finite N
lemma crops_cut {v:Bin G (C.side N p)}(hv:∀ f, Continuous (v f))(hm:m ≤ N)(ht:n ≤ m)(f:Body): Continuous (crops C m p N d hm v n ht f):=by
   induction ht using Nat.decreasingInduction generalizing f with
   | self=> rw [crops_head]; exact hv _
   | of_succ i hi ih=>
     rw [crops_step _ _ hi]
     change Continuous (fun U=>(replenishes C p i N d _ _ f) U); unfold replenishes; simp_rw [Finset.sum_apply]; apply continuous_finsetSum; intro j _
     apply Continuous.const_smul; unfold stepUp; exact ((ih _).comp (continuous_pull ..))
lemma clinic_cut (v:Palette C d)(t:Motion)(x:Site (C.side n p))(f:Body):Continuous (clinic C p N d v n x t f):=by
   have he(φ:Body): Continuous (precinct C p N d v φ):=by
       change Continuous (fun U=> entrance C d N p v 0 φ U); unfold entrance; simp_rw [Finset.sum_apply]; exact continuous_finsetSum _ (fun i _=> ((((C.localSection _).continuous_places _ _).const_smul _).const_smul _))
   unfold clinic uniform; split
   next hp =>
       let X:= crops C N p N d le_rfl (precinct C p N d v) n hp f; have hX: Continuous X:= crops_cut he le_rfl hp f
       unfold stepUp Motion.scalar; split; exact ((hX.comp (continuous_pull ..)).star); exact hX.comp (continuous_pull ..)
   next hp => exact continuous_const

section propel
variable (e:J→I)(c:J→Site (C.side n p))(E:J→Motion)(y:V→Site (C.side n p))(s:V→ℕ)(F:V→Body)(q:J→Body)
variable (T':(j:V)→Palette C (s j)) (f:Palette C d)
local notation "U!"=> brisk e
local notation "X"=> bunchG (C:=C) (N:=N) y s F T'
variable (ht:n ≤ N)
local notation "qx"=>coarse_base c E y s F q f T' ht
-- normalized tap compares without invoking S schedule at this stage
-- BODY = payment of projected product divided by exponent once normalized

def dyes (C:Family G)(n N p:ℕ)(ht:n ≤ N)(g:Goods G (C.side N p)): Goods G (C.side n p) :=
    gust C.path N p N (fun U=> (( (C.path.rep N p N).eval U:ℝ):ℂ)*g U) n ht
local notation "X'"=>dyes C n N p ht X
local notation "β"=>birth U! (R! N) qx
variable {Y':Unit×Basket.Root J →Three G (C.side n p)} {α:ℝ}
include h
omit [DecidableEq V] in
lemma relation (hP:MenuBoard (R! n) Y' (gust C.path N p N β n ht) (fun i=> c i.snd.fst) (fun _=>α) ((Z! n).supportExponent-2) 1)(hh:Integrable (birth (U!) (R! N) qx) (prior G _)) (i:J):
    (Y' ((),i,true)).fst=stepUp (E i) (c i) X':=by
    let t:= ((),i,true); let L'':= gust C.path N p N (β) n ht
    have hX: Continuous X:=continuous_finsetProd _ (fun j _=>clinic_cut ..)
    let z:= (C.S.toDepth ht p).embed (c i); let r:=E i; let g(A):=((R! N).eval A:ℂ)*X A; have hg: Integrable g (prior G _):= (((Complex.continuous_ofReal.comp (show Continuous (R! N|>.eval) from by rw [(h.wilson.starts ..).2]; exact bare_cont _)).mul hX).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    rw [show X'=gust C.path N p N g n ht from rfl,gust_spin ht _ _ hg]
    have he : (Y' t).1= fun U=> (L'' U).part ((U!).fire t):= funext fun _=> ((hP.check (h.wilson.represents N p n ht).good.labels _).2 t).symm
    rw [he, show (fun U=>(L'' U).part ((U!).fire t))= _ from pushpart ht _ _ hh]; congr 2; funext V₁
    unfold birth Mach; rw [Poly.part_smul,pass_fire,show (U!|>.fire t).val={t} from rfl,Finset.prod_singleton]
    change ((R! N|>.eval V₁):ℂ)*qx t V₁= Motion.scalar (E i) (((R! N).eval (Lattice.pull (E i).1 z V₁):ℂ)* X (Lattice.pull (E i).1 z V₁)); rw [scalar_mul, Motion.scalar_real, WardBin.Wheels.rep_spins (E i).1 h.wilson le_rfl]; rfl
end propel
-- price retrieval for any hue
section cube
local notation "ξ"=> n+1
variable (e:J→I)(c:J→Site (C.side (n+1) p))(E:J→Motion)(y:V→Site (C.side (n+1) p))(s:V→ℕ)(F:V→Body)(q:J→Body) (Q:ℝ)
local notation "o"=> roads c E y
local notation "E!"=>side_E E (V:=V)
local notation "x!"=> toss s d (J:=J)
local notation "T"=> coats c E y F q
local notation "Π"=>partialGroup Unit (basin J V)

variable (T':(i:V)→Palette C (s i)) (P:Sight C d p)(S:Emblems C d) (A:(i:V)→Sight C (s i) p)(U:(i:V)→Emblems C (s i))
local notation "s₁"=> (fun j:V=> Many.point (U j) (T' j) m N)
variable (hm:n+1 < m)(hk:m≤N)
local notation "he"=> hm.le.trans hk
local notation "J₁"=>bunchG (C:=C) (N:=N) y s F s₁
local notation "X'"=>dyes C (n+1) N p he J₁

-- reusable Stamp accepts all f independent widths. For E estimation once payment production
structure Campaign (k d ℓ:ℕ)(m:ℕ)(Q:ℝ) : Prop where
    points : Occupancy (o) ((λ₀).J (n+1))
    light : Clearance (o) (E!) (toss s d (J:=J)) (coats c E y F q) (font e) m
    buys (i:V) : Cap (s i+2) (F i) 1
    helps (i:J): Cap (d+2) (q i) 1
    belt (i:V): size (T' i)≤ Q
    pos : 0 < Q
    warm : Warm C (n+1) (ℓ+1) k
    port : d ≤ ℓ
    b0 (i:V): s i ≤ ℓ
    b1 (i:L) : coverNumber (Z! (n+1)).B ({(o ∘ Π.twig) (Π.bunch i),o i}:Support (C.side (n+1) p)) ≤ Ribbons.peepers C.path.levels (n+1)
-- Cart independent of T.Stamp used
local notation "ρ"=> fee C m (n+1) ℓ k d! Q
variable (hP:Spine D B h (n+1) p d N P S)(hA:∀ i:V,Spine D B h (n+1) p (s i) N (A i) (U i))
    (hp: Campaign e c E y s F q T' k d ℓ m Q) (M:Palette C d)
local notation "R0"=> Many.point S M m
local notation "U₀"=> brisk e
local notation "Γ"=> turnL J
local notation "T0"=>coarse_base c E y s F q (R0 N) s₁ he
local notation "Q0"=> birth U₀ (R! N) T0
local notation "Ω"=> C.path.levels.clock.op
include Y hC hS h hP hp hA
lemma steered (h_M:size M ≤ Q):
    0< ρ ∧ Integrable Q0 (prior G _) ∧ ∃ X:L'→Three G (C.side (n+1) p), MenuBoard (R! (n+1)) X (gust C.path N p N (Q0) (n+1) he) (fun i=> c i.2.1) (fun _=> ρ) ((Z! (n+1)).supportExponent-2) 1 ∧
    ∀ i:J, Signpost (R! (n+1)) (E i) (c i) ((P (n+1) (R0 (n+1))) (q i)) (X ((Γ).symm (i,false))) ∧ (X ((Γ).symm (i,true))).fst=stepUp (E i) (c i) X' ∧ MergeProof.Float.Blade (R! (n+1)) (c i) ((X ((Γ).symm (i,true))).snd.1) (profile ((R! (n+1)).activities) ((X ((Γ).symm (i,true))).snd.2)) 0 (4*(1/ρ)):=by
    obtain ⟨hρ,h_Q,hX,hH,h_s⟩:=shoot h Y hC hS e c E y s F q M T' P S A U hP hA (Nat.succ_pos _) hm hk hp.points hp.light hp.buys hp.helps hp.belt h_M hp.pos hp.warm hp.b0 hp.port hp.b1
    exact ⟨hρ,h_Q,hX,hH,fun i=> ⟨(h_s i).1, relation h e c E y s F q s₁ (R0 N) he hH h_Q i,(h_s i).2⟩⟩
omit hP
local notation "ζ"=> debit C n d (4*(1/ρ))
variable (w':PulseC)(t:Motion) (W:Site (C.side n p))
omit hC Y hS hp hA in
lemma Spine.tail (hv:Spine D B h b p d N P S)(hp:b ≤ i): Spine D B h i p d N P S:=⟨hv.starts,fun _ hm=> hv.legal _ (hp.trans hm),fun _ hm=> hv.follows _ (hp.trans hm)⟩
lemma starts_record (ι:Address.Bud C p n→ J)(hw:Awake D B b d)(hv:Spine D B h b p d N P S) (hg:b≤ n)(h_t:d+3 ≤ (λ₀).J n) (hW:Priced d w' 1)
   (hy:∀ i,c (ι i)= affine t.1 ((Ω n p).ratio.embed W) (child C p n i)∧ E (ι i)= t) :
   ∃ R Q', Signature C p b n N d h D P (amplitude C n N p d w' X') ζ R Q':=by
    obtain ⟨hξ,hQ,X,hX,hq⟩:= steered h Y hC hS e c E y s F q Q T' P S A U hm hk (Spine.tail h P S hv (hg.trans n.le_succ)) hA hp 0 (Address.size_zero.trans_le hp.pos.le)
    let a:=(4*(1/ρ)); let H:=(D N p n (Nat.lt_of_succ_le he)); let f:=fun i => X ((Γ).symm (ι i,true))
    have hU: Eden (N:=N) W t f a X' :=by
        refine ⟨fun i=> hX.fettled _,fun i=>?_ ,fun i=>?_⟩
        · dsimp only; rw [← (hy i).1]; exact (hq (ι i)).2.1.trans (by rw [(hy i).2])
        dsimp only; rw [← (hy i).1]; exact (hq _).2.2
    exact bornSig h hw hv W t w' hU hS hg (Nat.lt_of_succ_le he) h_t (by positivity) hW
end cube
end YM.RG05Readout.Records
