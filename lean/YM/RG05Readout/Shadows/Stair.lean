import YM.RG05Readout.Shadows.Reserve
/-!
# Actual steps on signed packet

Planner along separation. B through all copying uses separated licenses per
root selection. Parent polynomial price restored THEN gathered. Sells actual
signature on all copy child's test relations; doesn't delete K payment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Shadow
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets Copper View Address Many Pressure
open Legato Bandage Next.Rank.Station Accent Marker Menu Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G} {N m n b p d j:ℕ}{D:Address.Rail C}{B:ℕ→ℕ→ℝ}{x e E e':ℝ}
set_option quotPrecheck false
variable (h:C.Makes){V:Sight C d p}{S:Emblems C d}
local notation "Z!"=> C.path.levels
local notation "R₀"=> C.path.rep N p
local notation "Ω"=> C.path.levels.clock.op
local notation "ζ"=> C.S.block
local notation "F₀" => Palette C d
local notation "W₀"=> fun i =>C.side i p
local notation "κ₁"=> kappa C.path
local notation "ℓ"=> Copper.ld C.path.levels
local notation "νδ"=> C.path.levels.clock.J
local notation "O"=> Address.Bud C p m
local notation "λ!"=> C.path.S.block m
local notation "χ"=> ((C.path.S.block m).val:ℂ)^d
local notation "q"=> trim (C.path.S.block m)
local notation "X'"=> (R₀ (m+1))
local notation "X"=> R₀ m
local notation "Y!"=> Address.child C p m
local notation "Z₀"=> C.path.levels.budget
local notation "δ0"=> renal C.path.levels
local notation "w"=> focus C E n
variable (hw:Awake D B b d)(hv:Spine D B h b p d N V S)
section day
variable (H:∀ i:ℕ,Tape G (C.side i p))(Y:ℕ→ Palette C d)(ht:Halo D (eC:=h) b b n p N d V Y H e)
local notation "W"=> tab C E n
local notation "K₁"=> advances S Y b
local notation "Π"=> Ω m p
local notation "Σ!"=> (R₀ (m+1))
local notation "TR"=> (fun i:O=> Many.headFee C p m i)
local notation "Q"=> apron C.path.levels
variable {I:ℕ→Type}{J:Type}[∀ i,DecidableEq (I i)][∀ i,Fintype (I i)]
    (A: Planner C p b I J) (F:∀ i,I i→Body) {G':∀ i,Census (I i)}
local notation "B₁"=> A.labelY
local notation "o"=> A.supportX
local notation "p₁"=> A.narrows
-- Prepared polynomial at given scale specified
structure Aura (i:ℕ)(f:Config G (C.side i p)→Poly (G' i))(e t:ℝ) : Prop where
   ship : ∃ P,∃ S':I i→Tape G (C.side i p), MenuBoard (R₀ i) P f (A.supportX i) (fun _=> focus C e n i) t 1∧
       ∀ j:I i,pulseOut (S' j)=pulseOut (H i) ∧ (∃ z, Printed C d (R₀ i) 0 (κ₁ i) (S' j) z 0 (tab C e n i)) ∧ Signpost (R₀ i) (A.motion (A.labelY i j)) (A.supportX i j) ((S' j+ V i (K₁ i)) (F i j)) (P j)
variable (hs:Storage C D)
include ht hv hw hs
-- Parent charge from malice.core; Route evaluation.
local notation "V'"=>Aura (S:=S) (V:=V) (N:=N) (n:=n) H Y A F (G':=G')
set_option maxHeartbeats 900000 in
lemma forecast (f:Config G (C.side (m+1) p)→Poly (G' (m+1))) (hE:0<E)(hF:e ≤ E) (hx:b ≤ m)(hy:m<n)(hN:n ≤ N)(hg:12 ≤ C.path.levels.clock.J b)
    (hb:∀ i:I m,Cap (d+2) (F m i) 1)(he:∀ i, F (m+1) i = Many.headFee C p m ((A.narrows m hx i).2) (F m (A.narrows m hx i).1)) (hP: License (G' m) (G' (m+1)) (Prod.fst ∘ (A.narrows m hx)))
    (ho:Occupancy ((A.supportX (m+1))) (Q m))(ho':Occupancy ((Π).ratio.parent ∘ ((A.supportX (m+1)))) (Q m))
    (hY: Drake (G' (m+1)) (Z₀ m).B ((Π).ratio.parent ∘ ((A.supportX (m+1)))))
    (hC: Aura (S:=S) (V:=V) (N:=N) (n:=n) H Y A F (G':=G') (m+1) f E x)(hξ:(Z₀ (m+1)).supportExponent-4 ≤ x)
    (hU: Pin C m d):
       V' m (downdraft (N:=N) A G' (fun _=>d) m hx hP f) E ((Z₀ m).supportExponent):=by
    let R':= p₁ m hx; obtain ⟨P,S',hV,hD⟩:= hC.ship; have hi:m<N:=hy.trans_le hN; let L i:= A.motion (A.labelY m i)
    let K:= wheel h A m hi.le; let γ:=Prod.fst ∘ (p₁ m hx); let T (i:I m)(j:O):= S' (R'.symm (i,j));
    obtain ⟨a,t,hX,hQ⟩:= hs.exactMoon.days N p m hi; have hu : Coursework C.path Q (D N p m hi) (δ0 m) a t:=⟨hQ,hX⟩
    choose T' hS hS' U' hM hY' using fun i=> Spirits h hw hv H Y ht hg hx hy hN hF hE.le (T:=T i) (fun j=>(hD ..).2.1) (fun j=>(hD ..).1)
    -- intake rides charged with tested geometry
    let U(i:I m)(s:O): Three G (C.side m p):= spin (L i) (K i) ((U' i s) (F m i)); let Q'(i:I (m+1)):= U (γ i) (R' i).2; let v(_i:I (m+1)):=χ; have hR' := parentExact (ν:=R') (x:=o (m+1)) (δ:=L) (fun x=> A.future _ hx x)
    let c(_i:I (m+1)) := 32*(ℓ m)^2*W (m+1);
    have hR(i:I (m+1)): Ride Π (o (m+1) i) ((Π).ratio.parent (o (m+1) i)) (D N p m hi) (v i) (P i) (Q' i) (c i):=by
       let j:=γ i; let s:= (R' i).2; have hv':= hY' j s (F m j) 1 (hb j); rw [mul_one] at hv'; have ht:= hV.fettled i
       let z:= (o m j)
       let U' := T j s; let X₁ := ((S' i+ V (m+1) (advances S Y b (m+1))) (F (m+1) i)) -- shadow S was Emblems, redecl now problem
       have heS := hD i; have he': Signpost (R₀ (m+1)) (L j) (o (m+1) i) X₁ (P i):=by
          change Signpost (R₀ (m+1)) (A.motion (A.labelY m j)) _ _ _; rw [← show A.labelY (m+1) i=A.labelY m j from A.loyal m hx i]; exact heS.2.2
       have hJ : (Π).ratio.parent (o (m+1) i)= z:=congr_fun hR' i
       rw [hJ,A.future m hx]; rw [A.future m hx] at he';
       have hK : T j s=S' i:= congr_arg S' (R'.symm_apply_apply _);
       unfold X₁ at he'; rw [← hK, he] at he';
       have hη:Motion.scalar (L j) (v i)=v i:=by unfold Motion.scalar; split; simp [v]; rfl
       have hy: Ride Π (affine (L j).1 ((Π).ratio.embed z) (Y! s)) (affine (L j).1 z 0) (D N p m hi) (v i) (P i) (Q' i) (c i):=View.paid h hi hu.publishes.propagate hη hv' ht (signpost_use h hi.le (L j) (K j) hv'.tomorrow) (View.Signpost.at_child he' View.shift_at) (View.spin_at ..)
       rw [show affine (L j).1 z 0=z from by simp [affine]] at hy; exact hy
    let q' (_i:I (m+1)):= w m *(((C.S.block m).val:ℝ)^d); have hκ(i):0<q' i:=mul_pos (focus_ge hE) (by positivity)
    have hZ':Repegs ((Π).ratio.parent ∘ ((A.supportX (m+1)))) ((Z₀ m).B) (fun _=>δ0 m*w (m+1)) q' (1/2) 1 (G' (m+1)):=hY.palms (fun _=> hU.gifts E n hE) hκ (fun _=> mul_pos hu.poses.hats.1 (focus_ge hE)) hU.lit.2
    have h_a(i: I (m+1)):1≤‖v i‖:=by unfold v; rw [norm_pow,Complex.norm_natCast]; exact one_le_pow₀ (by exact_mod_cast (C.S.block m).property)
    have hF := hu.send h.wilson hi hV hξ h_a (fun _=> focus_ge hE) hR ho ho' (fun _=> hU.small E n hE) hκ hZ'
    let K' i:=View.spin (L i) (K i) ((T' i+ V m (advances S Y b m)) (F m i));
    have h : combine γ (fun _=> Many.budwgt C p m d) (fun i=> (v i)⁻¹ • Q' i) = K':=by
       rw [show _= (fun i=> Address.average (U i)) from ave_merge (s:=fun _=>d) U]; funext i
       unfold K'; rw [← hM i]; unfold Address.average U; let r':=(Fintype.card O:ℂ)⁻¹; rw [LinearMap.smul_apply,LinearMap.sum_apply,spin_real,spin_sum]; unfold Motion.scalar; split; simp; rfl
    refine ⟨K',T',?_,fun i=> ⟨hS' i,hS i, View.spin_at ..⟩⟩
    rw [← h]; exact hF.blend (fun _=>_) hP (‹C.Makes›.wilson.represents N p m hi.le).good hR' (fun _=> mul_le_mul_of_nonneg_left (bud_price _) (focus_ge hE|>.le)) hκ (fun _=> focus_ge hE)
end day
end YM.RG05Readout.Shadow
