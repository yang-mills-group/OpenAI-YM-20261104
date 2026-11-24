import YM.OPE.Compatible.Glades.Restrict
/-! turn the terminal single copy at its aligned pivot into the exact oriented column, then the stock comparison available. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.CutOrder
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset
open Ribbon
open scoped Topology Classical
variable {X V:Type}[PartialOrder X][OrderBot X]
open YM.OPE.Allot Series Lights
variable {G:Gauge}{C:Family G} (A:Allot C){P: Ensemble V}{l:ℕ→ℕ}
variable {N p b d j:ℕ} {E o: Track C.path V p}
variable [Fintype V][DecidableEq V]
section
variable (V) {I:Type} [Fintype I][DecidableEq I]
def pairAt (i:I) : V ↪ (V×I):= ⟨fun j =>(j,i),fun _ _ h=> Prod.mk.inj h|>.1⟩
variable (I) (i₀:I) (hs:∀ i:I,i=i₀)
include hs
lemma trim_allPair (p:Marker.Poly (Names V I)) : Mirror.trim (pairAt V i₀) p=(Fibers.reap (finishGroup V i₀)) p:=by
    ext x; change p.part (Mirror.imageM (pairAt V i₀) x)=p.part _; apply congr_arg (p.part) (Subtype.ext ?_); ext b; rcases b with ⟨v,i⟩; rw [Fibers.reaped]; rw [hs i]; exact mem_image_of_injective _ (pairAt V i₀).injective
end
set_option quotPrecheck false
variable (f:V→ Config G (C.side N p)→ℂ) {a w u : ℝ} {w': V→ℝ}
-- accepts mixed huge Ys continuous incl indicator lifts
local notation "m"=> j+1
local notation "I"=> ({⊥}:Finset X)
local notation "J"=> Names V ↥({⊥}:Finset X)
local notation "R"=> C.path.rep N p
local notation "H₀"=> birth J (R N) (fun i=> f i.fst)
local notation "Y"=> gust C.path N p N H₀
local notation "δ"=> renal C.path.levels j
local notation "α"=> C.S.a (j+1)^d*(β C (j+1)*(4*(1/a)))
omit [Fintype V] in
private lemma full_relax {I':Type}[Fintype V][Fintype I'][DecidableEq I']{j:ℕ}{Z:Config G (C.S.side j p)→Marker.Poly (Names V I')}{X:I'→Stem V G (C.S.side j p)}{v:I'→ℝ} (h : Owned (full V I') (C.path.rep N p j) (E j) P X v a Z): Owns (C.path.rep N p j) (E j) P X v a Z:=by
   obtain ⟨X',hy,hP,hx⟩:= h.issues; have hv:Z=X':= funext fun i=> (show Marker.Poly.inject ((Z i).part)=Marker.Poly.inject ((X' i).part) from congr_arg Marker.Poly.inject (funext fun s=> hP i s trivial)); exact hv ▸ hx -- inspect
set_option maxHeartbeats 200000 in
lemma badge (hp:C.ref d ≤ j) (hp':C.ref 0 ≤ j)(h:C.Makes)(hn:j<N)(ha:0<a)(hR: Head ({⊥}:Finset X) A P (j+1) N p b E o f a hn) (hC':∀ i,Continuous (f i))
    (hM:Migrating C.path j p (j+1) E)(hO:Migrating C.path j p (j+1) o)(hm:Injective (o j))(hI:Injective (o (j+1)))
    (hw:0<w)(ht:w ≤ a)(hW:4*w*(4*(1/a)) ≤ 1)(hX: w*(β C (j+1)*(4*(1/a)))≤1) {w₀:ℝ} (hv:0<w₀)(hy:w₀ ≤ renal C.path.levels j * w) :
    ∃ y:Coefficient (C.labels.level d) (C.side j p), (C.labels.level d).coeffSize y.x ≤ α ∧ y.Format 0 C.params (R j) ∧ y.remBound 0 (R j) (kappa C.path j) α ∧
       Served (R j) (fun i=> radiant (alto C.path j d) (P.move i) (o j i) (y.exponentialEntry 0 (C.localSection d) (R j))) (fun i=> sunny (R j) y.forced (P.move i) (o j i) (alto C.path j d)) (gust C.path N p N (birth (Bud V) (R N) f) j hn.le) (o j) (fun _=>w₀) (C.path.levels.budget j).supportExponent 1 :=by
    obtain ⟨L,hL,hP,hB⟩:= hR.ready; let i₀ : ({⊥}: Finset X):= ⟨_,mem_singleton_self _⟩
    let Z:=L.tips i₀; let u:=L.asks i₀; have hu: a ≤ u:= le_trans hP (le_of_eq (b:=_) ?_)
    swap; · apply Finset.prod_eq_single; intro i hi hp; exact False.elim (hp (Subsingleton.elim i _)); exact fun hz=> False.elim (hz (mem_univ _)) -- try
    have he(j'): L.tips j'=Z:= congr_arg L.tips (Subsingleton.elim j' _); have hX': (L.tips i₀).home=o m:= (L.steered i₀)
    have hP':= full_relax hL.owns; have hF(i): w ≤ L.asks i:= ht.trans (Subsingleton.elim i i₀ ▸ hu)
    let w1 (_: ↥({⊥}:Finset X)):=w; let D:= A.D N p j hn; let c:= C.path.levels.clock.op j p; let s:ℝ:=4*(1/a); let B':= C.localSection d
    obtain ⟨z,hZ,hY,hK,Z',hx,hZ',hΔ⟩:= convert_path A P hp hn h (show 0 ≤ s by unfold s; positivity) hw hW hX ((hM.mare j le_rfl j.lt_succ_self).symm ▸ hP'.earned i₀) ((hB _).more (mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le ha hu) (by norm_num))) ((hO.mare j le_rfl j.lt_succ_self).trans hX'.symm)
    refine ⟨z,hZ,hY,hK,?_⟩
    let V' (i: ↥({⊥}:Finset X)):=Z'
    let Z₁:= R (j+1); let Z₀:= R j; have hμ := A.admits (N:=N) (p:=p) hp' hn; have hD:= hμ.staff; have hC:= h.wilson; let o':= Stem.tags V'; have he' : Injective o':=by
       rintro ⟨t,i⟩ ⟨t',i'⟩ h
       change Z'.home t=Z'.home t' at h; rw [hx] at h; exact Prod.ext (hm h) (Subsingleton.elim i i')
    have hν: Occupancy (Stem.tags L.tips) (A.r j):=by
       intro i; refine le_trans (Occupancy.of_injective ?_ i) (A.buy.system.back _); rintro ⟨x,l⟩ ⟨y,q⟩ h; unfold Stem.tags at h; rw [L.steered,L.steered] at h; exact Prod.ext (hI h) (Subsingleton.elim l q)
    have hν':Occupancy o' (A.r j):=fun i=> (Occupancy.of_injective he' i).trans (A.buy.system.back _)
    let Q:= gust C.path N p N (birth (Names V ↥({⊥}:Finset X)) (R N) (fun i=>f i.1)); obtain ⟨hr,hv'⟩:= spring_step (A:=C.path) P ((hM.mare j le_rfl j.lt_succ_self).symm ▸ (hP'.scaleSlot (W':=w1) (fun _=>hw) hF)) hL.live hC hn hμ (by linarith only) (X':=V') (fun _=>hZ'.homes) (C:=0) (fun i=>he i ▸ hΔ) hν hν'
    -- thru
    rw [← gust_step _ _ _ _ _ hn] at hr hv'; let Q0:= C.path.levels.budget j; have Hb:= hC.represents N p j hn.le
    have hu : Repegs o' Q0.B (quota V (dropFunds (renal C.path.levels j) w1)) (fun _=>w₀) (1/2) 1 J:=by
       intro x he p hp; rw [one_mul]; apply le_trans _ (le_mul_of_one_le_right (Poly.worth (w:=quota V (dropFunds (renal C.path.levels j) w1)) (fun i=> mul_pos hD.hats.1 hw) x|>.le) (Real.one_le_exp (by positivity))); exact prod_le_prod (fun _ _=>hv.le) (fun _ _=> hy)
    have hh: ∀ i,Dominated (color V' i):= fun i=> hZ'.homes.spends _
    have H:ManyCopies.Serves Z₀ (lights V') (Stem.ink V' Z₀) (Q j hn.le) P.v P.move (E j) P.perms o' (fun _=>w₀) Q0.supportExponent 1:= ManyCopies.thru (Z:=1) hr Hb.good.labels (fun i=>mul_pos hD.hats.1 hw) hD.hats.1.le hν' (by linarith only [hD.exp.1]) (by rw [Hb.vac]; exact hD.stakes.1.trans_eq (by ring)) (fun _=>hv) (Hb.vac ▸ hu) zero_le_one (by simp) (by rw [Hb.vac,one_mul]; exact hD.stakes.2) hv' hh (fun U=>(Tour.bright C.path hC N p j hn.le U).ne') -- Stem.tags vac
    let x':=pairAt V i₀; have ht := Mirror.kiosk x' H.sold (fun _=>hv)
    have hf(i : V×↥({⊥}:Finset X)): Continuous ((fun i': V×↥({⊥}:Finset X)=> f i'.1) i):= hC' _
    have hF:Integrable (birth (Names V ↥({⊥}:Finset X)) (R N) (fun i=>f i.1)) (prior G _):= (hatCont C N p _ hf (show Continuous (R N|>.eval) by rw [(hC.starts ..).2]; exact bare_cont _) _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have he : Mirror.trim x' ∘ Q j hn.le=gust C.path N p N (birth (Bud V) (R N) f) j hn.le:=by
       have hZ:= ripe (A:=C.path) i₀ hn.le hF
       have hv:(fun i U=>∏ _j: ↥({⊥}:Finset X), f i U)=f:= by ext; simp
       rw [show (fun i:V=> fun U=> ∏ _j: ↥({⊥}:Finset X), f i U)=f from hv] at hZ; exact (funext fun i=> trim_allPair V _ i₀ (fun i=>Subsingleton.elim i _) _).trans hZ.symm -- hZ y i.snd redex
    have hx : o'∘x'=o j:=hx -- projection definitional
    have hT : lights V'∘ x'=fun i=> radiant (alto C.path j d) (P.move i) (o j i) (z.exponentialEntry 0 (C.localSection d) (R j)):= funext fun i=> ((hZ'.rays _ i).1).trans (by rw [show Z'.home= _ from hx]) -- shadow
    have hU : Stem.ink V' Z₀ ∘ x'=fun i=> sunny (R j) z.forced (P.move i) (o j i) (alto C.path j d):=funext fun i=> ((hZ'.rays _ i).2).trans (by rw [show Z'.home= _ from hx])
    rw [hT,hU,hx,he] at ht; exact ht
end YM.OPE.Arboreal.CutOrder
