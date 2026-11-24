import YM.Integration.WilsonMixedTaggedAdmission
import YM.RG05Readout.Many.Reel

/-! Actual stored singleton training on the adjacent edge of the original
Wilson interval admits the single tagged finite-source program. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedCourseEntry

open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View
open Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage
open WilsonMixedTaggedRoster WilsonMixedTaggedOutput
open scoped BigOperators Classical

variable {G:Gauge} {C:Family G} {n b m N per d k:ℕ} {V:ℕ → Type}
variable [∀i,DecidableEq (V i)] [∀i,Fintype (V i)] {W:Type*}
variable (A:Planner C per n V W) (s:W → ℕ) (I:∀i,V i → Body)
variable (h:C.Makes) {D:Address.Rail C} (stock:Storage C D)
variable {q f:ℕ → ℝ} {T:Pens C per W} {J:Census (V (m+1))}
set_option quotPrecheck false
local notation "Ξ" => C.path.rep N per
local notation "α₁" => (C.path.levels.budget (m+1)).supportExponent
local notation "K" => C.path.levels.clock.op m per
local notation "O" => Address.Bud C per m
local notation "ℓ" => Copper.ld C.path.levels m
local notation "r" => apron C.path.levels
local notation "z" => west C q f k (m+1)
local notation "t" => fun i:O=>Native.pull (Address.displacement C per m i) (((C.S.block m).val:ℝ)⁻¹)
local notation "rows" => imprint h A I T (m+1)
include stock in
theorem original (nb:n ≤ b) (bm:b ≤ m) (mN:m < N)
    (purse:Purse C f q b (m+1) d k)
    (lamp:Lantern s h (p:=per) (b:=b) (D:=D) (m+1) N q T)
    (prep:PreparedA A I b (m+1) nb)
    (caps:∀i:V b,Cap (s (A.labelY b i)+2) (I b i) 1)
    (occupied:Occupancy (A.supportX (m+1) ∘ (Prod.fst:V (m+1)×Bool → V (m+1))) (r m))
    (fettled:∀i,Useful (Ξ (m+1)) (rows mN i)) {δ:ℝ} (positive:0 < δ)
    {X:Config G (C.side (m+1) per) → Poly J}
    (paid:Served (Ξ (m+1)) (fun i=>(rows mN i).2.1)
      (fun i=>profile (Ξ (m+1)).activities (rows mN i).2.2)
      X (A.supportX (m+1)) (fun _=>z) (α₁-1) δ) :
    ∃Z:Config G (C.side (m+1) per) → Poly (census J),
      MenuBoard (Ξ (m+1)) (liveRow (rows mN)) Z (A.supportX (m+1) ∘ Prod.fst)
        (fun _=>z) (α₁-1) 1 ∧ 
      (∀U,specialize J (δ:ℂ) (Z U)=X U) ∧ 
      (∀U,specialize J 0 (Z U)=restore (Ξ (m+1)) (fun i=>(rows mN i).2.1)
        (fun i=>profile (Ξ (m+1)).activities (rows mN i).2.2)
        (0:Support (C.side (m+1) per) → Config G (C.side (m+1) per) → Poly J) 0 U) := by
  obtain ⟨a,price,hv⟩:=stock.exactMoon.days N per m mN
  have course : Coursework C.path (r) (D N per m mN) ((renal C.path.levels) m) a price :=
    ⟨hv.2,hv.1⟩
  let e:=A.narrows m (nb.trans bm)
  let col (v:V m):=A.labelY m v
  let cut (v:V m):=s (col v)
  let move (v:V m):=A.motion (col v)
  let μ (v:V m):=wheel h A m mN.le v
  let χ (i:V (m+1)):ℂ:=((C.S.block m).val:ℂ)^cut (e i).1
  let fine (v:V m):=T (col v) (m+1)
  let charge:=ℓ*(ℓ*q m)
  have trained (v:V m) : ∃ j:O → Tape G (C.side m per),
      (∀ a',Travel C N m per (cut v) (Address.child C per m a') (D N per m mN)
       ((Address.orient (keys0 h mN) (fine v) a').comp (t a')) (j a') charge) ∧ 
      T (col v) m=Address.average j := by
    obtain ⟨f,hf,he⟩:=lamp.brings m bm (Nat.lt_succ_self _) mN (col v)
    exact ⟨f,hf,he⟩
  choose j training _ using trained
  let next (i:V (m+1)):=View.spin (move (e i).1) (μ (e i).1) ((j (e i).1 (e i).2) (I m (e i).1))
  have cc:=cap_lives A s I nb bm m.le_succ prep caps
  have future:=A.future m (nb.trans bm)
  have parents:=parentExact (δ:=move) future
  have rides (i:V (m+1)) : Ride K (A.supportX (m+1) i) ((K).ratio.parent (A.supportX (m+1) i))
      (D N per m mN) (χ i) (rows mN i) (next i) (charge*1) := by
    let v:V m:=(e i).1
    let a':O:=(e i).2
    let θ:=((Address.orient (keys0 h mN) (fine v) a').comp (t a')) (I m v)
    have paid:=training v a' (I m v) 1 (cc v)
    have ht:Signpost (Ξ (m+1)) (move v) (A.supportX (m+1) i)
        ((fine v) ((t a') (I m v))) (rows mN i) := by
      have phase:A.labelY (m+1) i=col v:=A.loyal m (nb.trans bm) i
      rw [← show I (m+1) i=headFee C per m a' (I m v) from prep m bm (Nat.lt_succ_self _) i]
      change Signpost _ (A.motion (col v)) _ (T (col v) (m+1) _) _
      rw [←phase]
      exact View.spin_at ..
    rw [future] at ht
    have shifted:Signpost (Ξ (m+1)) (move v) ((K).ratio.embed (A.supportX m v)) θ (rows mN i) :=
      ht.at_child View.shift_at
    have fixed:Motion.scalar (move v) (χ i)=χ i:=by
      unfold Motion.scalar
      split
      · simp [χ]
      rfl
    have sale:Ride K (A.supportX (m+1) i) (affine (move v).1 (A.supportX m v) 0)
        (D N per m mN) (χ i) (rows mN i) (next i) (charge*1) := by
      apply (show A.supportX (m+1) i=_ from future i).symm ▸
        (View.paid h mN course.publishes.propagate fixed paid (fettled _)
         (View.signpost_use h mN.le _ (μ v) paid.tomorrow) shifted (spin_at ..))
    rw [show affine _ _ _=A.supportX m v by simp [affine]] at sale
    rw [show (K).ratio.parent (A.supportX (m+1) i)=A.supportX m v from congr_fun parents i]
    exact sale
  have bs:=bm.trans m.le_succ
  have hq:=purse.headV m bm m.le_succ
  have hq':=purse.headV (m+1) bs le_rfl
  have hp:=purse.upper (m+1) bs le_rfl
  have head:= (purse.control m bm (Nat.lt_succ_self _)).1
  have cost:2*z*(charge*1) ≤ 1 := by
    simpa only [charge,mul_one,west] using head.first (q m) (q (m+1)) (f (m+1)) hq hq' hp.2 hp.1
      (purse.nextV m bm (Nat.lt_succ_self _)).1
  have normed (i:V (m+1)) : 1 ≤ ‖χ i‖ := by
    rw [show χ i=((C.S.block m).val:ℂ)^_ from rfl,norm_pow,Complex.norm_natCast]
    exact one_le_pow₀ (by exact_mod_cast (C.S.block m).property)
  apply WilsonMixedTaggedAdmission.original (rows mN) _ positive paid
  intro Z served
  exact WilsonAllDateHarvestEndpointIntegrability.original (N:=N) (p:=per) (m:=m)
    (I:=liveRow (rows mN)) (Q:=liveRow (fun i=>(χ i)⁻¹ • next i)) (l:=liveRow (fun _=>charge*1))
    (o:=A.supportX (m+1) ∘ Prod.fst) (w:=fun _=>z) course h.wilson mN
    (fun _=>mul_pos hp.1 (grantw hq')) (WilsonMixedTaggedRide.doubled (fun i=>
      WilsonMixedTaggedRide.normal (rides i) (normed i))) occupied
    (WilsonMixedTaggedRide.room (w:=fun _=>z) (fun _=>cost)) served

end YM.Integration.WilsonMixedTaggedCourseEntry
