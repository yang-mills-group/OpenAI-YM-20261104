import YM.OPE.Compatible.Bard.Office
/-!
# Signed line. At tip price and fan spend. Continues at mark of child
before losing alignment in ancestor's cells; enhancement duty reimburses
geometric powers. Other authorities use *same ticket*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open scoped Topology BigOperators Classical
variable {V:Type}[Fintype V][DecidableEq V]{G:Gauge}{C:Family G}{A:Allot C}{P:Ensemble V}
    {d b k N p m n:ℕ}{w:ℝ}{E o:Track C.path V p}
    (X: ∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p))
set_option quotPrecheck false
local notation "p!"=> lantern C.path w d k
local notation "Q"=> C.labels.level d
local notation "f"=> C.localSection d
local notation "F"=> C.path.rep N p
variable (A)
include A
lemma keep_on {t:Stem V G (C.side k p)} (hC:C.Makes)(hG:G.Simple)
    (hp:Guided (C.localSection d) C.params C.path N p (C.ref d) k X A.D p!)
    (ht:Stamp (N:=N) P (C.localSection d) (E k) (X k) t)(h:t.home=o k)
    (hv:0<w)(hy:C.ref 0 ≤ m)(hn:C.ref d<n)(he:m ≤ n)(hw:n ≤ k)(hx: d ≤ b)
    (ho:Migrating C.path n p k o)(hB:Migrating C.path m p n E)
    (hX:∀ i,m ≤ i → i< n → (C.path.levels.clock.op i p).ratio.parent ∘ o (i+1)=o i)
    (hA:∀ i,n ≤ i → i ≤ k→ ∀ v:V,v ≠ P.v → o i v=affine (P.move v).1 (E i v) (o i P.v)):
    ∃ L:Line A P N p m k b E o,L.X k=t ∧ L.w k=w/2∧ L.w m=Run.Below C.path (lantern C.path w d k n/2) n m:=by
   have hz(i:ℕ)(h':i<N) := A.buy.system.costs.night.days N p i h'; have hf(i:ℕ)(he:i<N) : SoundDoor (C.path.levels.clock.op i p) (A.D N p i he):=by obtain ⟨x,y,h,_⟩:=hz i he; exact h.propagate
   obtain ⟨T,hT,hK,hL⟩:= prints P (C.localSection d) hp hC.wilson (hC.sections d) (fun i _=> hf i) hn.le hw t ht h ho hA
   let Q':Line A P N p n k b E o:= ⟨T,p!,hT,(Creep.lamp A hG hv).higher hx (fun i hi hz=> (lan_pos C.path hv).le)⟩
   let L:= Q'.damp (2:ℝ)⁻¹ (by norm_num) (by norm_num); cases n
   next=>omega
   next n=>
      obtain ⟨_,_,hy',_⟩:= hz n (by have h:=hp.paid; omega); let w':= lantern C.path w d k (n+1); have hb := root_cut P (C.localSection d) hp hC.wilson (fun i _=> hf i) (by omega : _ ≤ n) hw hy'.tunes _ (hL (n+1) le_rfl hw)
      have hL : L.w (n+1)=w'/2:= by change (2:ℝ)⁻¹*w'=_; ring
      have hg:=L.hold.fees (n+1) le_rfl hw; have h0:=hp.spice (n+1) hn.le hw
      let C':= alto C.path (n+1) d*((X (n+1)).x 0)
      obtain ⟨W,hX,hW⟩:= Line.roll_below (v:=L.w (n+1)) (b:=b) A P hC hy he (hw.trans hp.paid) hB C' (L.hold.marks (n+1) le_rfl hw) (by rw [show 1/(2*(L.w (n+1)))=(1:ℝ)/w' by rw [hL]; ring]; exact hb) (le_trans (mul_le_mul_of_nonneg_right (show L.w (n+1) ≤ w' from by linarith only [hg,hL]) (norm_nonneg _)) h0) hg ((L.hold.steers (n+1) le_rfl hw).symm) hX
      obtain ⟨Y,hY,hZ⟩:= W.continueW L hX (by rw [hW,Run.below_main])
      exact ⟨Y,((hZ k hw).2).trans hK, (hZ k hw|>.1).trans (show 2⁻¹*(p! k)=w/2 from by rw [lan_home]; ring), (hY m he|>.1).trans ((congr_fun hW m).trans (congr_arg (fun v=> Run.Below C.path v (n+1) m) hL))⟩
end YM.OPE.Allot
