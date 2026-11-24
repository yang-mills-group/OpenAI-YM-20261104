import YM.MergeProof.South.Window
import YM.MergeProof.Badlands
/-! Start flexibility: handle thin provisional birth (or rebirth from a compatible
literal product at an intermediate scale) separately from renewal in the same
actual vacuum. Based on Frost / Wakes.
-/
noncomputable section
namespace YM.RGGapR2.Harbor
open Function Filter MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V : Type} [Fintype V][DecidableEq V] {B:Census V}{G:Gauge}
open MergeProof MergeProof.Accent MergeProof.Menu
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi

def pitch (H:History G)(j i:ℕ):=((H.levels.budget i).supportExponent - if i=j then 4 else 0)
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
    (hQ:Served (A.rep N p j) (f j) (tapes A p N g j) X (o j) (w j) (pitch A j j) 1) (he: Integrable X (prior G _))
local notation "C"=> gust A N p j X
include h ht hh hl hQ he
-- hQ usual purchase at retained exponent. can reduce by one or two at top intermediate if necessary.
set_option maxHeartbeats 800000 in
lemma windowFin (m:ℕ)(hK:k ≤ m)(hm:m ≤ j): Served (R m) (f m) (T m) (C m hm) (o m) (w m) (pitch A j m) 1:=by
   induction hm using Nat.decreasingInduction with
   | self =>rw [gust_base]; exact hQ
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
       have hT := Duty.pre A N m p r h hN hb hj (ht.pos _ hm' hm) (ht.pos _ hK hm.le) (F':=f m) (δ:=ν) (s:=y) (r:=x) hc (by unfold pitch;split <;> linarith) (ht.next _ hK hm) hC hA (fun i=> (hl i).stocked _ hK hm.le) hu hs hX hΨ
       have h7:m ≠ j:=hm.ne; rw [show pitch A j m=(P m).supportExponent by unfold pitch; split <;> simp_all]
       exact (congr_arg (fun (z: V → Site (A.S.side m p)) =>Served (R m) (f m) (T m) P' z (w m) (P m).supportExponent 1) hP).mp hT
end

section
open Bid Motion
variable {A:History G}{r:ℕ→ℕ}{δ u:ℕ→ℝ}{D:∀ N p m:ℕ,m<N →GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}
variable (N p:ℕ){j:ℕ}
local notation "R"=> (A.rep N p)
local notation "P"=> A.levels.budget
local notation "S"=> A.S
variable (o:V → Site (A.S.side j p))(w:V → ℝ)(f:V → Config G (A.S.side j p)→ℂ)(b:V → Config G (A.S.side j p)→ℂ)(g:V → ℕ → Config G (A.S.side j p)→ℂ)

def relax (A:History G)(u:ℕ→ℝ)(j:ℕ):ℕ→ℝ:=fun _=> u j*mintK ((A.levels.budget j).B)
set_option maxHeartbeats 800000 in
lemma launching (B:Census V)(h:A.Selected)(he:j ≤ N)(hw:∀ i,0 < w i)(ht:Drake B (P j).B o)(ho:Occupancy o (r j)) (hd:8 ≤ (P j).B)(hh:Moonlit A r δ u D)
   (hv:∀ i,Dominated (g i))(hx:∀ i U,((R j).eval U:ℂ)*b i U=coin (R j) (f i) (g i) U)
   (hr:∀ i,∃ (z:MergeProof.Response G (A.S.side j p))(t:ℝ), Attainment ((R j).p) (o i) z t ∧ w i *t ≤ relax A u j j ∧ hook (R j).activities (R j).p.threshold z=profile (R j).activities (g i)) :
   Served (R j) f (fun i=>profile (R j).activities (g i)) (birth B (A.rep N p j) b) o w (pitch A j j) 1:=by
   choose z t hZ hJ hf using hr
   let π:ℝ:= mintK ((P j).B)
   have hπ:0<π:= Real.exp_pos _
   let s (i):= w i/π
   have hs(i):0<s i:=div_pos (hw i) hπ
   let X:=birth B (R j) b; let L:= P j; let c:= A.levels.clock.forcedAllowance j; let wC:= c+(r j)*siteFactor ((R j).p.B)*u j
   have hR:= h.represents N p j he; have hE:= hh.endow j; have hp: (R j).p=P j:=hR.vac
   let d₀:=L.supportExponent-3
   have h1: ((((R j).p.B+(R j).p.B+1:ℕ)):ℝ)^4*wC ≤ (R j).p.supportExponent-d₀:=by
      dsimp only [wC]; rw [hp]; exact hE.2.2.1.trans_eq (by unfold d₀ L;ring)
   have h2: Real.exp wC-1 ≤1:=by dsimp only [wC]; rw [hp]; exact hE.2.2.2
   have hl:= cloth hZ (fun i=> show s i*t i ≤ u j from (mul_comm (s i) _).le.trans (by unfold s; rw [← mul_div_assoc]; exact (div_le_iff₀ hπ).mpr ((mul_comm ..).trans_le (hJ i)))) (fun i=> (hs i).le)
   have h₁ : Served (R j) f _ X o s d₀ 1:= unveiled B s hs (R j) b hR.good.labels z hl ho (c:=c) (K:=g) (L:=f) hE.1 le_rfl hE.2.1 h1 h2 (fun U=>Tour.bright A h N p j he U|>.ne') zero_le_one hv (show ∀ i, _ from hf) hx
   rw [← hp] at ht hd
   apply h₁.prune hs hw (ht.palms (fun i=>show w i ≤ s i*mintK ((R j).p.B) from by unfold s; rw [hp,show mintK ((P j).B)=π from rfl,div_mul_cancel₀ _ hπ.ne']) hw hs hd) zero_le_one _ (mul_one _).le
   unfold pitch; split
   · unfold d₀ L; linarith only
   simp_all

omit [Fintype V] in
lemma migrateDrake {o:∀ i:ℕ,V→Site (A.S.side i p)}{k:ℕ}{φ:ℕ→ℝ}(hp:Migrating A k p N o)(ht:Drake B (P k).B (o k))(hB:Brine A k δ φ) (i:ℕ)(hK:k ≤ i)(he:i ≤ N) : Drake B (P i).B (o i):=by
    induction hK with
    | refl=>exact ht
    | step hi ih=>rename_i i; let f:=(A.levels.clock.op i p).ratio
                  rw [← hp.mare i hi he]; refine ⟨fun s ht i' hi' j hj hij=> ?_⟩; exact (hB.split _ hi).trans ((Nat.mul_le_mul_left f.count.val ((ih (show i ≤ N by omega)).spread s ht i' hi' j hj hij)).trans (Corona.below f ..))
end
end YM.RGGapR2.Harbor
