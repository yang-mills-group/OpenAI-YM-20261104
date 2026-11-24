import YM.GapsContact.Dusk.Sum
import YM.MergeProof.South.Window

/-!
# Continuing full Serves during the coast through genuinely short final span

This is a port for stencils/measuring lanes, not last-word contract. Don't
spread pins except occupancy & old exact anchor relations. For close uses bring
the SINGLETON exponent & forced-profile Wakes book only once for full period J..m.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Dusk
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open Pressure Pressure.Tube MergeProof Accent Menu Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y:Type} [Fintype V] [DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi

-- From one common factor. See `Rates` friendly certificate later (not yet constructed).
structure Shipper (A:History G) (r:ℕ→ℕ) (D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m)) : Prop where
    exp (m:ℕ) : 100≤ (A.levels.budget m).supportExponent
    grants (N p m:ℕ)(h:m<N) : let X:= A.levels; let x:= X.clock.hatBeta m; let y:= X.clock.hatBeta (m+1); let E:= (X.budget (m+1)).supportExponent; let v:=(X.budget m).supportExponent
                               ∃ a:ℝ, Volant (X.clock.op m p) (D N p m h) (r m) (E-4) (ipo y) (v+1/2) (v+1) (precious x) a ∧ Ticks x y a (r m)
section
variable (A:RG.History G) (D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m))
variable (N m p:ℕ) (r:ℕ→ℕ) (K:Shipper A r D)
local notation "f"=> A.S.side (m+1) p
local notation "c"=> A.S.side m p
local notation "X0"=> A.rep N p m
local notation "X1"=> A.rep N p (m+1)
local notation "Z"=> A.levels.clock.op m p
local notation "P0"=> A.levels.budget m
local notation "P1"=> A.levels.budget (m+1)
set_option quotPrecheck false
local notation "x"=> A.levels.clock.hatBeta m
local notation "y"=> A.levels.clock.hatBeta (m+1)
variable {I J:V→ℝ}
    {θ:Config G (A.S.side (m+1) p)→Poly B} {o:V→Site (A.S.side (m+1) p)}
    {F: V→ Config G (A.S.side (m+1) p)→ℂ} {L: Menu.Specialty G (A.S.side (m+1) p) V}
    {F': V→ Config G (A.S.side m p)→ℂ} {L': V→ℕ→ Config G (A.S.side m p)→ℂ}
local notation "P"=> ((Z).push (X1).beta θ)
include K
set_option maxHeartbeats 600000 in
lemma shift (h:A.Selected) (hm:m<N)
    (he:Served X1 F L θ o I (P1).supportExponent (precious y))
    (hI:∀ i,0< I i) (hJ:∀ i,0<J i) (hb:∀ i,J i ≤ aBrake y * I i)
    (hO:Occupancy o (r m)) (hO':Occupancy ((Z).ratio.parent ∘ o) (r m))
    (hB:∀ i,Dominated (L' i)) (he':∀ U i,(P U).part (B.fire i)=coin X0 (F' i) (L' i) U)
    {s b:V→ℝ}{δ:V→ℂ}(hc:∀ i,2*J i*s i≤coupon y)(hy:∀ i,J i*b i≤coupon y)(hK:∀ i,∃ Z':Set PhysicalNext.Repeat.Lotus.Wing,Z'.Finite∧Tale Z' (o i) ((Z).ratio.parent (o i)) 1 (F i) (L i) (profile (X0).activities (L' i)) (δ i) (s i) (b i) (D N p m hm)): Served X0 F' (fun i=>profile (X0).activities (L' i)) P ((Z).ratio.parent ∘ o) J (P0).supportExponent (precious x):=by
   let A0:= A.levels; obtain ⟨a,hV,hv⟩:= K.grants N p m hm; have hx := A0.fits.delayed (m+1)
   let E:= (P1).supportExponent; let v:=(P0).supportExponent; have hz:0<aBrake y:=inv_pos.mpr (pow_pos (gate_pos hx) _); have hℓ:0 ≤ coupon y:= Real.rpow_nonneg (zero_le_one.trans hx.le) _
   have hX:= le_trans (a:=aBrake y) (inv_le_one_of_one_le₀ (one_le_pow₀ hv.met)) le_rfl
   have hK': (P0)=(X0).p:=(h.represents N p m hm.le).vac.symm; have hk:(P1)=(X1).p:=(h.represents N p _ hm).vac.symm
   have hp := he.prune (d:=aBrake y*precious y) hI hJ (slighter hI hJ hb hz.le hX) hz.le (show E-4+0≤ E from by linarith) le_rfl
   apply Menu.stroke (o:=o) (a:=1) hV hJ hJ (h.represents N p _ hm).good ?_ ?_ (h.represents N p m hm.le).good.labels hp he' hB hK hO hO' hℓ hc ?_ hy hℓ ?_ ?_ ?_ ?_ zero_le_one ?_ ?_ (A.levels.transition_mass ..) (fun U=>(Tour.bright A h N p m hm.le U).ne')
   · linarith only [K.exp (m+1)]
   · rw [← hk]; linarith only
   · rw [← hk]; exact hv.capE
   · rw [← hK']; linarith only
   · linarith only [K.exp m]
   · rw [← hK']; exact hv.capK.1.trans_eq (by ring)
   · intro i hi p hp; rw [one_mul]; apply le_mul_of_one_le_right (Marker.Poly.worth hJ _).le; exact Real.one_le_exp (by positivity)
   · rw [one_mul]
   rw [← hK',one_mul]; exact hv.capK.2
end
section
variable (A:History G) (r:ℕ→ℕ)(D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m))
variable (N p:ℕ) {j k:ℕ} (e:j ≤ N) (o:∀ i:ℕ,V → Site (A.S.side i p))(w W:ℕ→ V→ℝ)
set_option quotPrecheck false
local notation "P"=>A.levels.budget
local notation "R"=> (A.rep N p)
local notation "β"=> A.levels.clock.hatBeta
variable (f:∀ m:ℕ,V → Config G (A.S.side m p)→ℂ)(g:∀ m:ℕ,V→ℕ → Config G (A.S.side m p)→ℂ)
local notation "M"=> manifest A p N f g
local notation "T"=> tapes A p N g
variable {X:Config G (A.S.side j p)→Poly B}
    (h:A.Selected) (K:Shipper A r D)
    (hl:∀ i:V,Wakes A k j N p (fun m=>o m i) (fun m=>W m i) (fun m=>f m i) (fun m=>g m i) D e)
    (hr:∀ m,k ≤ m→m≤j→∀ i,0<w m i)
    (hb:∀ m,k ≤ m→m<j→∀ i, w m i ≤ aBrake (A.levels.clock.hatBeta (m+1))*w (m+1) i ∧ w m i ≤ coupon (A.levels.clock.hatBeta (m+1))*W (m+1) i)
    (ht:∀ m,k ≤ m→m<j→ Occupancy (o (m+1)) (r m) ∧ Occupancy (o m) (r m) ∧ (A.levels.clock.op m p).ratio.parent ∘ o (m+1)= o m)
    (hQ:Served (A.rep N p j) (f j) (tapes A p N g j) X (o j) (w j) (A.levels.budget j).supportExponent (precious (A.levels.clock.hatBeta j))) (he: Integrable X (prior G _))
local notation "C"=> gust A N p j X
include h hr ht K hl hQ he hb
set_option maxHeartbeats 800000 in
lemma windowed (m:ℕ)(hK:k ≤ m)(hm:m ≤ j): Served (R m) (f m) (T m) (C m hm) (o m) (w m) (P m).supportExponent (precious (β m)):=by
   induction hm using Nat.decreasingInduction with
   | self=>rw [gust_base]; exact hQ
   | of_succ m hm IH=>
       have hm': k  ≤  m+1:= hK.trans m.le_succ
       let q:= gust A N p j X (m+1) hm; have hR : Integrable q (prior G _):= gust_live _ _ _ _ _ he hm
       have hc:=IH hm'; rw [gust_step A N p j X hm]; let P':=(A.levels.clock.op m p).push ((R (m+1)).beta) q
       have hN : m<N:=hm.trans_le e
       have hY(i):(fun U=> (q U).part (B.fire i))=M (m+1) i:=funext fun U=> hc.relay (fun i=> (hl i).stocked (m+1) hm' hm) ((h.represents _ _ _ hN).good.labels) U |>.1 i
       have hy(i):(fun U=>(P' U).part (B.fire i))= M m i:= (push_get (A.levels.transition_mass ..) hR _).trans (by rw [hY]; exact (hl i).feeds m hK hm|>.symm)
       choose ψ ν y x hf hs hX hD using fun i=> (hl i).sways m hK hm
       obtain ⟨ho,hO,hk⟩:= ht m hK hm
       let Z:= A.levels.clock.op m p; let x':=Z.ratio.parent ∘ o (m+1); have hP:x'=o m:=hk
       have hu(U i): (P' U).part (B.fire i)=coin (R m) (f m i) (g m i) U:= congr_fun (hy i) U
       have hΨ(i:V): ∃ Z': Set PhysicalNext.Repeat.Lotus.Wing, Z'.Finite∧Tale Z' (o (m+1) i) (x' i) 1 (f (m+1) i) (T (m+1) i) (T m i) (ν i) (y i) (x i) (D N p m hN):=by rw [hP]; exact ⟨ψ i,hf i,hD i⟩
       let c:= coupon (β (m+1)); have hp:0≤c:=Real.rpow_nonneg (zero_le_one.trans (A.levels.fits.delayed (m+1)).le) _
       have hw(b i)(hh:W (m+1) i*b ≤ 1): w m i*b ≤ c:=by
          rcases le_total b 0 with hb'|hb'
          · exact (mul_nonpos_of_nonneg_of_nonpos (hr m hK hm.le i).le hb').trans hp
          exact (mul_le_mul_of_nonneg_right (hb m hK hm i).2 hb').trans (le_trans (le_of_eq (mul_assoc ..)) (mul_le_of_le_one_right hp hh))
       have hf(i:V) : 2*w m i*y i ≤ coupon (β (m+1)) :=(show 2*w m i*y i=w m i*(2*y i) from by ring).trans_le (hw (2*y i) i (by linarith only [hs i]))
       have hT:=Dusk.shift A D N m p r K h hN hc (hr _ hm' hm) (hr _ hK hm.le) (fun i=>(hb m hK hm i).1) ho (hk.symm ▸ hO) (F':=f m) (fun i=>(hl i).stocked _ hK hm.le) hu hf (fun i=> hw (x i) i (hX i)) hΨ
       exact (congr_arg (fun z:V→Site (A.S.side m p)=>Served (R m) (f m) (T m) P' z (w m) (P m).supportExponent (precious (β m))) hP).mp hT
end
end YM.GapsContact.Dusk
