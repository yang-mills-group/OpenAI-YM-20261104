import YM.MergeProof.South.Hearth
/-! # Recover the full exponent after a lowered projection. Adapted from South/Window and South/Hearth. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Menu Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V : Type} [Fintype V][DecidableEq V]{B:Census V}{G:Gauge}
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi
section
variable (A:History G) (r:ℕ→ℕ)(δ u:ℕ→ℝ)(D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m))
variable (N p:ℕ) {j k:ℕ} (e:j ≤ N) (o:∀ i:ℕ,V → Site (A.S.side i p))(w:ℕ →V→ℝ)
set_option quotPrecheck false
local notation "P"=>A.levels.budget
local notation "R"=> (A.rep N p)
variable (f:∀ m:ℕ,V  → Config G (A.S.side m p)→ℂ)(g:∀ m:ℕ,V→ℕ → Config G (A.S.side m p)→ℂ)
local notation "M"=> manifest A p N f g
local notation "T"=> tapes A p N g
variable {X:Config G (A.S.side j p)→Poly B}
    (h:A.Selected)(ht:Matchup A r δ p j k o w B) (hh:Moonlit A r δ u D)
    (hl:∀ i:V,Wakes A k j N p (fun m=>o m i) (fun m=>w m i) (fun m=>f m i) (fun m=>g m i) D e)
    (hQ:Served (A.rep N p j) (f j) (tapes A p N g j) X (o j) (w j) ((A.levels.budget j).supportExponent-3) 1) (he: Integrable X (prior G _))
local notation "C"=> gust A N p j X
include h ht hh hl hQ he
-- hQ usual purchase at retained exponent. can reduce by one or two at top intermediate if necessary.
set_option maxHeartbeats 800000 in
lemma window3 (m:ℕ)(hK:k ≤ m)(hm:m ≤ j): Served (R m) (f m) (T m) (C m hm) (o m) (w m) (if m=j then (A.levels.budget m).supportExponent-3 else (A.levels.budget m).supportExponent) 1:=by
   induction hm using Nat.decreasingInduction with
   | self =>rw [gust_base]; rw [if_pos rfl]; exact hQ
   | of_succ m hm IH=>
       have hm': k  ≤  m+1:= hK.trans m.le_succ
       let q:= gust A N p j X (m+1) hm; have hR : Integrable q (prior G _):= gust_live _ _ _ _ _ he hm
       have hc:=IH hm'; rw [gust_step A N p j X hm]; let P':=(A.levels.clock.op m p).push ((R (m+1)).beta) q
       have hN : m<N:=hm.trans_le e
       have hY(i):(fun U=> (q U).part (B.fire i))=M (m+1) i:=funext fun U=> hc.relay (fun i=> (hl i).stocked (m+1) hm' hm) ((h.represents _ _ _ hN).good.labels) U |>.1 i
       have hy(i):(fun U=>(P' U).part (B.fire i))= M m i:= (push_get (A.levels.transition_mass ..) hR _).trans (by rw [hY]; exact (hl i).feeds m hK hm|>.symm)
       choose ψ ν y x hf hs hX hD using fun i=> (hl i).sways m hK hm
       obtain ⟨v,g',hj,hb⟩:= hh.days N p m hN
       have hk:= ht.pins m hK hm
       let Z:= A.levels.clock.op m p; let x':=Z.ratio.parent ∘ o (m+1); have hP:x'=o m:=hk
       have hC:Occupancy x' (r m):=by rw [hP]; exact ht.occ _ hK hm.le
       have hA:Repegs x' (P m).B (fun i=>δ m*w (m+1) i) (w m) (1/2) 1 B:=by rw [hP]; exact ht.runs _ hK hm
       have hu(U i): (P' U).part (B.fire i)=coin (R m) (f m i) (g m i) U:= congr_fun (hy i) U
       have hΨ(i:V): ∃ Z': Set PhysicalNext.Repeat.Lotus.Wing, Z'.Finite∧Tale Z' (o (m+1) i) (x' i) 1 (f (m+1) i) (T (m+1) i) (T m i) (ν i) (y i) (x i) (D N p m hN):=by rw [hP]; exact ⟨ψ i,hf i,hD i⟩
       have hT := Duty.pre A N m p r h hN hb hj (ht.pos _ hm' hm) (ht.pos _ hK hm.le) (F':=f m) (δ:=ν) (s:=y) (r:=x) hc (by split <;> linarith only) (ht.next _ hK hm) hC hA (fun i=> (hl i).stocked _ hK hm.le) hu hs hX hΨ
       rw [if_neg hm.ne]; exact (congr_arg (fun (z: V → Site (A.S.side m p)) =>Served (R m) (f m) (T m) P' z (w m) (P m).supportExponent 1) hP).mp hT
end
end YM.MergeProof.Accent
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
local notation "ζ!"=> ζ d
section
variable {I V:Type}[Fintype I][Fintype V][DecidableEq V] {B:Census V}(h:Scrim C W u ψ φ δ ζ r D)
variable (o:∀ i:ℕ,V→Site (C.side i p)){x:I→ℝ}(s:V→Motion)(a:V→I→ℂ) (Z:I→∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)) {g:I→ℕ→ℝ}
   (e:k≤N)(hw:0<w)(hx:∀ i,0 < x i)(hz:∀ i,∑ j,w*‖a i j‖/x j≤1)
local notation "t!"=> march (fun _ : V=>w) φ m
local notation "f"=> fun i j=>∑ n, a j n • liftF T Y! N p (s j) (fun l=>o l j) (Z n) i
local notation "p!"=> fun i j=>∑ n, a j n • liftK T N p (s j) (fun l=>o l j) (Z n) i
include H h
set_option maxHeartbeats 800000 in
lemma prolonged3 {M:Config G (C.side k p)→Poly B} (ht:ℓ ≤ m)(hk:m≤k) (hy:m < k)(hi: Integrable M (prior G _))(hη:Migrating T m p k o)(hM:Occupancy (o m) (r m)) (hm:Drake B (T|>.levels.budget m).B (o m)) (he:∀ i:I,Club T C.params Y! (ζ d) ψ m k N p (stair φ (x i) m) D (Z i) (g i) e) (hQ:Served (R k) (f k) (p! k) M (o k) (t! k) ((C.path.levels.budget k).supportExponent-3) 1) (hw:0<w)(hx:∀ i,0<x i)(hz:∀ i,∑ j,w*‖a i j‖/x j≤1): Served (R m) (f m) (p! m) (gust T N p k M m hk) (o m) (fun i=>w) (C.path.levels.budget m).supportExponent 1∧ Vault (fun _=>w) (f m) (p! m) 2 1:=by
    let X i j:= liftF T Y! N p (s i) (fun l=>o l i) (Z j); let Y i j:=liftK T N p (s i) (fun l=>o l i) (Z j)
    let q:= gust T N p k M; let f':= f; let p':= p!; let W':= t!
    choose G' H' hp' hP using fun (i:V)(j:I)=>beams C N k m p d H (x j) h (s i) (o:=fun l=>o l i) (Z j) ht hk e (hx j) (fun l hl hL=> (congr_fun (hη.mare l hl hL) i).symm) (he j)
    let K j (i:V):= ∑ l, a i l • G' i l j
    have hh (i:V) : (fun j=> W' j i)=stair φ w m:=by
       funext j; induction j with
       | zero=> rfl
       | succ j hj=> by_cases hp : m ≤ j
                     · unfold W' stair;simp only [march,if_pos hp]; exact congr_arg (φ j * ·) hj
                     unfold W' stair;simp only [march,if_neg hp]
    have hW (i:V) : Wakes T m k N p (fun j=>o j i) (fun j=>W' j i) (fun j=>f' j i) (fun j=>K j i) D e:=by rw [hh i]; exact rearranged C N k m p H w h (a i) e hw hx (hz i) (H' i) (fun j l hl hL=> (hp' i j l hl hL).2)
    have hj(j)(hr:m ≤ j)(hn:j ≤ k): tapes T p N K j=p' j:=by
       unfold p'; funext i; change profile _ (K j i)=_
       have hx(l): Dominated (a i l • G' i l j):= rainbow ((H' i l).stocked j hr hn) _
       simp_rw [K, prof_sum _ hx, profile_scale]; exact Finset.sum_congr rfl fun n _=> congr_arg _ ((hp' i n j hr hn).1)
    have hF:Brine C.path m δ φ:=⟨fun i _=> h.costs.stay.water _ (Nat.zero_le i),fun i _=> h.costs.stay.mint _ (Nat.zero_le i),fun i _=> h.costs.stay.split _ (Nat.zero_le i),fun i _=> h.costs.stay.support _ (Nat.zero_le i)⟩
    have H':=Accent.window3 T r δ u D N p e o W' f' K H.wilson (desal C.path r m p k δ φ o (fun _=>w) (fun _=>hw) hF B hη hm h.costs.mom hM) h.costs.night hW (show Served _ (f' k) (tapes T p N K k) M _ (W' k) _ _ from (hj k hk le_rfl).symm ▸ hQ) hi m le_rfl hk
    rw [hj m le_rfl hk, show W' m=(fun _=>w) from marines m φ _ (fun _=>hw), if_neg hy.ne] at H'
    refine ⟨H',⟨fun i U=>?_,fun i U=>?_⟩⟩
    · refine le_trans ?_ (fare1 w _ hw hx (hz i) (fun j=> X i j m U) zero_le_two (fun j=> hP i j U|>.1)); simp_rw [Finset.sum_apply]; rfl
    rw [← Finset.mul_sum]
    simp_rw [Finset.sum_apply]; exact fare w _ hw hx (hz i) (fun j l=>Y i j m l U) zero_le_one (fun j=>by
       have h:= (hP i j U).2; rw [(hp' i j m le_rfl hk).1] at h; exact h)
end
end YM.MergeProof
