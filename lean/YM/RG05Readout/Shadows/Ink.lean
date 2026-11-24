import YM.RG05Readout.Shadows.Wigwam
/-!
# First solder. Signed polynomial.

Reintroduce true counterterms at upper graph leg with their own labels.
Apply combination to recovered triples only with consistent K. Plaques
are guarded by shape choice (protect all perforations), then coalesce
parent marks with the power supplied by Census. Keep proof covariances
at each orientation. This encodes any authenticated Spice with these
placements and bounds from `Fronds`. REFERENCE readout on product-only;
travels as computed there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Shadow
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets Copper View Address Many Pressure
open Legato Bandage Next.Rank.Station Accent Marker Menu Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G} {N n b m p d:ℕ}{D:Address.Rail C}{B:ℕ→ℕ→ℝ} {x e E a r y z:ℝ}
set_option quotPrecheck false
variable (h:C.Makes){V:Sight C d p}{S:Emblems C d}
local notation "Z!"=> C.path.levels
local notation "R₀"=> C.path.rep N p
local notation "Ω"=> C.path.levels.clock.op n p
local notation "L"=> C.S.block n
local notation "F₀" => Palette C d
local notation "κ₁"=> kappa C.path
local notation "ℓ"=> Copper.ld C.path.levels n
local notation "ν₁"=> C.path.levels.clock.J
local notation "O"=> Address.Bud C p n
local notation "χ"=> ((C.path.S.block n).val:ℂ)^d
local notation "X'"=> R₀ (n+1)
local notation "X"=> R₀ n
local notation "Ch"=> Address.child C p n
local notation "Z₀"=> C.path.levels.budget
local notation "δ0"=> renal C.path.levels
local notation "TR"=> (fun i:O=> Many.headFee C p n i)
variable (hw:Awake D B b d)(hv:Spine D B h b p d N V S) (hc:Cater C D)
section
variable (F:Goods G (C.side (n+1) p))(w:PulseC)
variable {H:∀ i:ℕ,Tape G (C.side i p)} {Y:ℕ→Palette C d} (ht: Signature C p b n N d h D V (amplitude C n N p d w F) e Y H)
    (hm:b ≤ n)(hN:n<N)(hg:12 ≤ C.path.levels.clock.J b)
local notation "z'" => advances S Y b n
local notation "M'"=> repayment S Y b n
local notation "S!"=> tab C E n
local notation "W0"=> focus C E n n
variable {I:ℕ→Type}{J:Type}{J':Type}[∀ i,DecidableEq (I i)][∀ i,Fintype (I i)] [Fintype J'] [DecidableEq J']
    (A: Planner C p b I J) (F':∀ i,I i→Body) {G':∀ i,Census (I i)}
variable {P:I (n+1)→Three G (C.side (n+1) p)}{Z Y': I (n+1)→Three G (C.side (n+1) p)}
    (θ : J' ≃ I (n+1)× Bool)
local notation "B'"=> A.narrows n hm
local notation "U"=> Prod.fst ∘ B'
local notation "ψ"=> A.supportX
local notation "Γ"=> Prod.fst ∘ θ
-- P_plus index via true .snd, counter via .false
local notation "E'"=> (fun i=>A.motion (A.labelY (n+1) i)) -- quotation metadata

local notation "i!"=> fun i:I n => fun j: O => (B').symm (i,j)
noncomputable def pens (A:Planner C p b I J) (θ:J' ≃ I (n+1)×Bool) (F:I (n+1)→ Body)(w:PulseC)(i:J'):ℂ:= if (θ i).2 then Motion.scalar (A.motion (A.labelY (n+1) (θ i).1)) (w (F (θ i).1)) else -1
variable {θ}
-- certificate linking authenticity
structure LotusNotes (f:J'→ Three G (C.side (n+1) p))(a:ℝ):Prop where
   issued i : let j:= θ.symm (i,true); (f j).fst=stepUp (A.motion (A.labelY (n+1) i)) (A.supportX (n+1) i) F ∧ MergeProof.Float.Blade (X') (A.supportX (n+1) i) ((f j).snd.1) (profile (X'|>.activities) ((f j).snd.2)) 0 a
   counter i : let j:= θ.symm (i,false); Signpost (R₀ (n+1)) (A.motion (A.labelY (n+1) i)) (A.supportX (n+1) i) ((V (n+1) M') (F' (n+1) i)) (f j)
variable (θ)(f:J'→ Three G (C.side (n+1) p))
local notation "P!"=> fun i=> f (θ.symm (i,true))
local notation "K!"=> fun i=> f (θ.symm (i,false))
local notation "v!"=> pens A θ (F' (n+1)) w
variable {R: Census J'}
include h hc hw hv ht hN hg
local notation "ε"=> Many.apron C.path.levels n
local notation "λ'"=> (Ω).ratio
set_option maxHeartbeats 880000 in
lemma stepFirst (T:Config G (C.side (n+1) p)→ Poly R)(hξ:MenuBoard (R₀ (n+1)) f T (A.supportX (n+1) ∘ Γ) (fun _=>r) ((Z₀ (n+1)).supportExponent-2) 1)
    (hp: LotusNotes (S:=S) (V:=V) (Y:=Y) (N:=N) (θ:=θ) F A F' f a) (hP:∀ i:I n,Cap (d+2) (F' n i) 1)(h_F:∀ i:I (n+1), F' (n+1) i= headFee C p n (B' i).2 (F' n (U i)))
    (ht':d+3 ≤ ν₁ n)(hY: Priced d w 1)(ha:0 ≤ a)(hR: 0 < E)
    (hk:License (G' (n+1)) R Γ) (hM:License (G' n) (G' (n+1)) U) (ho:Occupancy ((λ').parent ∘ ψ (n+1)) (ε))(hO: Occupancy (ψ (n+1)) ε)
    (hG: 0< x)(he:x ≤ r) (hS:2*x*fare C n d a e ≤ 1) (hW: focus C E n n * ((C.S.block n).val:ℝ)^d ≤ (renal C.path.levels n)*x)(heX : bid C n d (debit C n d a) ≤ E) :
    let y:=fun U'=> feed v! hk (T U')
    Aura (S:=S) (V:=V) H Y A F' (N:=N) (n:=n) (G':=G') n (downdraft (N:=N) A G' (fun _=> d) n hm hM y) E ((Z₀ n).supportExponent):=by
    intro y; have hr:= hG.trans_le he; let Z:= P!; let Z':= K! -- name Z' notation!
    let B(i:I n):= A.motion (A.labelY n i)
    let g:=(A.narrows n hm); let q(i):= g.symm i; let v':= v!
    have hvv(i:J') : ‖v' i‖≤1:=by
       unfold v' pens; split
       next he=>
        let v:=(θ i).1; have hv:Cap (d+2) (F' (n+1) v) 1:=by rw [h_F]; apply cap_aff _ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast (L).property)) (dist_box ..) (hP _)
        rw [norm_scalar]; exact (hY _ _ hv).trans (le_of_eq (one_mul _))
       next=>simp
    let v(i:I (n+1)):=Motion.scalar (A.motion (A.labelY (n+1) i)) (w (F' (n+1) i)); let γ:= U
    have hΦ(i:I n)(j:O): g (i! i j)=(i,j):=Equiv.apply_symm_apply ..
    have h₁(i:I n)(j:O):ψ (n+1) (i! i j)=affine (B i).1 ((λ').embed (ψ n i)) (Ch j):=by
       rw [A.future n hm, hΦ]
    have h₂ (i:I n)(j:O): A.labelY (n+1) (q (i,j))= A.labelY n i:=by rw [A.loyal n hm, Equiv.apply_symm_apply] -- q let
    let δ (i:I (n+1)):= v i • (P! i)- K! i
    have hh: combine Γ v' f=δ:=by
       funext i; unfold Many.combine; rw [← Equiv.sum_comp θ.symm]; simp only [Function.comp_apply,Equiv.apply_symm_apply,Fintype.sum_prod_type,Fintype.sum_bool]; rw [Finset.sum_eq_single i]
       · simp only [v',pens, Equiv.apply_symm_apply, Bool.false_eq_true, if_false, if_true, neg_smul,one_smul]; exact (sub_eq_add_neg ..).symm
       intro j _ hi; rw [if_neg hi,if_neg hi,zero_smul,zero_smul,zero_add]; simp
    have hX : MenuBoard (X') δ y (ψ (n+1)) (fun _=>x) ((Z₀ (n+1)).supportExponent-2) 1:=by
       rw [←hh]; exact hξ.blend _ hk (h.wilson.represents N p (n+1) hN).good rfl (fun i=> (mul_le_of_le_one_right hG.le (hvv i)).trans he) (fun _=>hr) (fun _=>hG)
    -- acquire per parent
    obtain ⟨a',t,hT,-⟩:=hc.tiers n N p hN
    let c:=fare C n d a e; let W:=wheel h A n hN.le
    have heD(i:I n):Eden (N:=N) (ψ n i) (B i) ((P!) ∘ (i! i)) a F:=by
       refine ⟨fun j=> hξ.fettled _, fun j=> ?_,fun j=>?_⟩
       · let k:= i! i j; have he:= hp.issued k|>.1; rw [show ψ _ k= _ from h₁ i j,show A.labelY _ k= _ from h₂ i j] at he; exact he
       let k:=i! i j; dsimp only; rw [← h₁]; exact (hp.issued k).2
    have hPa(i:I n) (j:O): let k:=q (i,j); Useful (X') (K! k)∧ Signpost X' (B i) (affine (B i).1 ((λ').embed (ψ n i)) (Ch j)) (V (n+1) (repayment S Y b n) (TR j (F' n i))) (K! k):=by
       intro k; refine ⟨hξ.fettled _,?_⟩; have hk:=hp.counter k; dsimp only at hk
       rw [h_F,Function.comp_apply,show g k= _ from hΦ i j] at hk -- `g` red? adjust
       rw [show ψ _ k = _ from h₁ i j, show A.labelY _ k= _ from h₂ i j] at hk; exact hk
    choose P' Vv' hV' hJ hz h using fun i=> earns (d:=d) h hw hv hc ht hm hN hg (B i) (ψ n i) _ ((K!) ∘ i! i) (F' n i) (W i) ht' (heD i) hY ha (hP i) (hPa i)
    let Q i:= Vv' (γ i) (g i).2; have hg(i:I (n+1)): Ride Ω (ψ (n+1) i) ((λ').parent (ψ (n+1) i)) (D N p n hN) χ (δ i) (Q i) c:=by
       let p:=γ i; let z:= (g i).2; have he' : (B').symm (p,z)=i:= Equiv.symm_apply_apply ..; have hx:= h p z; dsimp only [Function.comp_apply] at hx; rw [he'] at hx; unfold δ v; rw [h_F,A.loyal n hm, A.future n hm,parent_affine _ (C.S.block_odd _),Address.Bud.personal, show affine _ _ 0=ψ n p by change (B p).1.act 0+ (ψ n p)=_; simp]; exact hx
    let w':ℝ:=W0*((L).val:ℝ)^d; have hw':0<w':= mul_pos (focus_ge hR) (by positivity)
    let u(_i:I (n+1)):=w'
    have hpegs : Repegs ((λ').parent ∘ ψ (n+1)) (Z₀ n).B (fun i=>δ0 n*x) u (1/2) 1 (G' (n+1)):=by
       intro j _ i _
       rw [one_mul]; apply (Finset.prod_le_prod (fun _ _=> hw'.le) (fun _ _=> hW)).trans (le_mul_of_one_le_right (Poly.worth (fun i=>hw'.trans_le hW) j).le (Real.one_le_exp (by positivity))) -- change toll
    have hT1: 1 ≤ ‖χ‖:=by rw [norm_pow,Complex.norm_natCast]; exact one_le_pow₀ (by exact_mod_cast (L).property)
    have hp_ := hT.send ‹C.Makes›.wilson hN hX (by linarith only) (fun _=> hT1) (fun _=>hG) hg hO ho (fun _=>hS) (fun i=>hw') hpegs
    let V₀(i):= View.spin (B i) (W i) ((P' i+V n z') (F' n i))
    have hpC : combine γ (fun _=> budwgt C p n d) (fun i=> χ⁻¹ • Q i)= V₀:=funext fun i=> (congr_fun (ave_merge (ν:=g) (s:=fun _=>d) Vv') i).trans (hz i).symm
    refine ⟨V₀,P',?_,fun i=>⟨hV' i,?_,View.spin_at ..⟩⟩
    rw [← hpC]; exact hp_.blend _ hM (‹C.Makes›.wilson.represents N p n hN.le).good (parentExact (δ:=B) (ν:=B') (A.future n hm)) (fun _=> mul_le_mul_of_nonneg_left (bud_price d) (focus_ge hR|>.le)) (fun _=>hw') (fun _=>focus_ge hR)
    rw [tab_one]; obtain ⟨x,hx⟩:=hJ i; exact ⟨x,hx.grow heX⟩
end
end YM.RG05Readout.Shadow
