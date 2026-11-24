import YM.Agora26.Marks.Inflate
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe
namespace Vista26
open Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
local notation "V" => Site (C.side m p)
local notation "Z" => royal C m p
local notation "r*" => stepUp
open Yarn.SitePlan Next.Rank.Station
local notation "B" => ((fun i=>(C.path.levels.budget i).B))
local notation "X" => (C.path.levels.clock.hatBeta)
open GridApprox
variable (v : C.label d) (a:ℕ) (o x:Site (C.side k p))(hk:k≤N)(he:C.ref d≤k)(ic:Bool)
include H he hk
-- literal identity at arbitrary jointly translated anchors
lemma writeNudge : writeF C v N k p a (o+x) hk ic = writeF C v N k p a o hk ic ∘ pull 1 (anchor C.S p hk x):=by
   let u:= anchor C.S p hk x; let f:=betaDrop C d k N p a v o ic
   have hz: betaDrop C d k N p a v (o+x) ic=f ∘ pull 1 x:=by
       cases ic
       · rfl
       simp only [f,betaDrop, ↓reduceIte]
       funext U
       let Y:= Vitrines.enamel (C.localSection d) (C.path.rep N p k) (Spindle.parcel C d k N p v) a
       change -(alto C.path k d*Y (pull 1 (o+x) U))= -(alto C.path k d*Y (pull 1 o (pull 1 x U)))
       rw [pull_pull]; simp [affine]
   unfold writeF; rw [hz]
   have hA: x=anchor C.S p (le_refl k) x:= ((there x).symm.trans (vect C k p k x le_rfl))
   have hp:= backTo_orient C.path N p (h:=k) le_rfl hk x (1:Signed) (show Envelope f from cylinder_env (dropped H o v he hk a ic)); rw [← hA] at hp; rw [hp]; funext U
   change C.O N p v (anchor C.S p hk (o+x)) U+_ = C.O N p v (anchor C.S p hk o) (pull 1 u U)+_
   rw [pull_one, C.translation]; congr 2
   exact (C.S.toDepth hk p).root.map_add o x

omit he in
set_option maxHeartbeats 200000 in
lemma writesHeard (pk:Finset J) {d':J→ℕ}(v':∀ j,C.label (d' j))(o':J→ Site (C.side k p))(hr:∀ j,C.ref (d' j)≤k)(ice:J→Bool) :
    moment (C.beta N p) (fineJob (fun j=>writeF C (v' j) N k p a (o' j+x) hk (ice j)) pk) =
    moment (C.beta N p) (fineJob (fun j=>writeF C (v' j) N k p a (o' j) hk (ice j)) pk):= Function.const _ (by
    let F j:= writeF C (v' j) N k p a (o' j) hk (ice j); let l:= (law G (C.side N p) (C.beta N p)); let u:= anchor C.S p hk x
    have hi : Envelope (fineJob F pk) := Envelope.prodC _ _ (fun i _=>Strobe.write_e H (v' i) a (o' i) hk (hr i) _)
    have hprod: fineJob (fun j=>writeF C (v' j) N k p a (o' j+x) hk (ice j)) pk= fineJob F pk ∘ pull 1 u:=by
       funext Q; show (∏ j∈pk, writeF C (v' j) N k p a (o' j+x) hk (ice j) Q)=∏ j∈pk,F j (pull 1 u Q) -- LHS binder dependence? 
       apply Finset.prod_congr rfl; intro i _; exact congr_fun (writeNudge H (v' i) a _ x hk (hr i) (ice i)) Q
    rw [hprod,moment_pull _ _ _ (fineJob F pk) (hi.integrableC _)]) (‹Fintype J›, ‹DecidableEq J›)
omit he hk
structure Sites26 (br dis:ℕ) (x:J→Site (C.side k p)): Prop where
    close : ∀ i j, separation (x i) (x j) ≤ br*dis
    apart: ∀ i j,i≠j→ dis ≤ separation (x i) (x j)

section
variable {br:ℕ} {φ:Filter I} {k dis:I→ℕ} (L:GracesP C φ k dis)
variable (hS:Citizen C W r D) (hbr:0<br) (d':J→ℕ) {src tar:I→ℝ}
include L hS hbr
lemma shellLaw (hv:Coins φ (C.S.scale ∘ k) src)(hvpos:∀ᶠ i in φ,0<src i)
    (hs:Coins φ (C.S.scale ∘ k) tar)(ht:∀ᶠ i in φ,0<tar i):
    ∀ᶠ i in φ, ∀ N p:ℕ,∀ hk:k i<N,∀ x:J→Site (C.side (k i) p), Sites26 (C:=C) br (dis i) x → ∀ v:(j:J)→ C.label (d' j),
      (∀ j, Spindle.paid C (d' j) (k i) N p (v j) ≤ src i)→ ∀ ice:J→Bool,(∃ j,ice j=true)→
        ‖moment (C.beta N p) (fineJob (fun j=>writeF C (v j) N (k i) p ((C.path.levels.budget (k i)).B) (x j) hk.le (ice j)) univ)‖ ≤ tar i:=by
   let U(i:I)(ice:J→Bool):Prop:= ∀ N p:ℕ,∀ hk:k i<N,∀ x:J→Site (C.side (k i) p), Sites26 (C:=C) br (dis i) x → ∀ v:(j:J)→ C.label (d' j), (∀ j, Spindle.paid C (d' j) (k i) N p (v j) ≤ src i)→ ‖moment (C.beta N p) (fineJob (fun j=>writeF C (v j) N (k i) p ((C.path.levels.budget (k i)).B) (x j) hk.le (ice j)) univ)‖ ≤ tar i
   suffices hh:∀ ice:J→Bool,∀ᶠ i in φ,(∃ j,ice j=true)→ U i ice by
      filter_upwards [eventually_all.mpr hh] with i hi N p hk x hx v he ice hχ; exact hi ice hχ N p hk x hx v he
   intro ice
   by_cases hχ:∃ j,ice j=true; swap
   · exact Eventually.of_forall (fun _ h=> (hχ h).elim)
   obtain ⟨i₀,hj⟩:=hχ
   obtain ⟨z,hz,hM⟩:= ((eventually_gt_atTop (C.ref 0)).and (rolls H 0 (Fintype.card J))).exists
   filter_upwards [inflated H L ice i₀ hM hz d' hbr hS i₀ hj hv hvpos hs ht,eventually_all.mpr fun j=>L.seeks.eventually_ge_atTop (C.ref (d' j))] with i hi ht _ N p hk x hx v he
   let u:=x i₀; let x' j:=x j-u
   have hy: Range26 C (k i) p (dis i) br x' i₀:=by
      refine ⟨sub_self _,fun j=> ?_,fun l j hel=>?_⟩
      · exact (Loom.separation_alt (x j) u) ▸ hx.close j i₀
      simpa [x',sub_eq_add_neg] using hx.apart l j hel -- simp only rhs has no x'!
   have hh:= hi N p hk x' hy v he
   let f (x:J→Site (C.side (k i) p)):=fineJob (fun j=>writeF C (v j) N (k i) p ((C.path.levels.budget (k i)).B) (x j) hk.le (ice j)) univ
   have hq : moment (C.beta N p) (f x) = moment (C.beta N p) (f x'):=by
      have he:= writesHeard H (p:=p) (N:=N) (a:=((C.path.levels.budget (k i)).B)) u hk.le univ v x' ht ice
      simpa only [x',sub_add_cancel] using he
   change ‖moment (C.beta N p) (f x)‖ ≤ _; rw [hq]; exact hh
-- technical `(k,gap)` inf-principal syntax following Strobe/Helio
omit L in
lemma uniformShell (e t s:ℕ):
    ∀ᶠ k:ℕ in atTop, ∀ dis:ℕ,(C.path.levels.budget k).B^8 ≤ dis → (dis:ℝ) ≤ C.path.levels.clock.hatBeta k^e→
    ∀ N p:ℕ,∀ hk:k<N,∀ x:J→Site (C.side k p), Sites26 (C:=C) br dis x → ∀ v:(j:J)→ C.label (d' j),
      (∀ j, Spindle.paid C (d' j) k N p (v j) ≤ C.path.levels.clock.hatBeta k^t)→ ∀ ice:J→Bool,(∃ j,ice j=true)→
        ‖moment (C.beta N p) (fineJob (fun j=>writeF C (v j) N k p ((C.path.levels.budget k).B) (x j) hk.le (ice j)) univ)‖ ≤ (C.path.levels.clock.hatBeta k^s)⁻¹:=by
   let K:ℕ×ℕ→ℕ:= Prod.fst; let n:ℕ×ℕ→ℕ:= Prod.snd
   let a:= C.path.levels.clock.hatBeta; let M:=(Filter.comap K atTop)
   let A : Set (ℕ×ℕ):={q | B (K q)^8≤ n q ∧ (n q:ℝ)≤ a (K q)^e}; let M0:= M ⊓ Filter.principal A
   have h:Tendsto K M0 atTop:= tendsto_iff_comap.mpr inf_le_left
   have hB:∀ᶠ i in M0,i∈A:= (Filter.Eventually.filter_mono (show M0 ≤ Filter.principal A from inf_le_right) ((eventually_principal).mpr (fun _ h=>h)))
   have hw:Height C.S M0 (C.S.scale ∘ K) K 1:= ⟨h,tendsto_const_nhds.congr' (((C.S.divergent.comp h).eventually_gt_atTop 0).mono fun i hi=>(div_self («a»:=C.S.scale (K i)) (ne_of_gt hi)).symm)⟩
   have hz:= C.S.divergent.comp h
   have hp:= hat_price hz hw
   have hk (t:ℕ):Coins M0 (C.S.scale ∘ K) (fun i=>a (K i)^t):= Coins.power hp hz _
   have hv(i)(t:ℕ):0<a i^t:=pow_pos (zero_lt_one.trans ((T).fits.delayed _)) _
   have hx:= shellLaw H (show GracesP C M0 K n from ⟨h,(Cheap.power hp.up hz e).norm_le (hB.mono fun i (hi:i∈A)=> (Real.norm_of_nonneg (Nat.cast_nonneg _)).trans_le (hi.2.trans (Real.le_norm_self _))),hB.mono fun i (hi:i∈A)=> hi.1⟩) hS hbr d' (hk t) (Eventually.of_forall fun i=> hv (K i) _) (Coins.inv (hk s)) (Eventually.of_forall fun i=> inv_pos.mpr (hv (K i) _)); rw [Filter.eventually_inf_principal] at hx
   obtain ⟨u,hu,hU⟩:= hx; filter_upwards [hu] with i hi b he hx
   exact hU (show (i,b)∈ K ⁻¹' u from hi) ⟨he,hx⟩
end
end Vista26
end YM.OPE.Strobe

