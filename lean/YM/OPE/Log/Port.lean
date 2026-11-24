import YM.OPE.Log.Measuring
import YM.OPE.Log.Stylist
/-!
# Log costs at grid, keeping the full discrepancy's match estimate at ordinary rates
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open Function Set Filter Lattice RG Wilson MergeProof Accent Ribbons Source Overlay Bid
open Next.UVStress Extraction
open scoped Topology BigOperators
set_option quotPrecheck false
variable {G: Gauge}{C:Family G}{ι:Type}{I:Type}[Fintype I] {l:Filter ι}[l.NeBot]{T A V:ι→ℝ}{a b:ℝ} {k m j:ι→ℕ}{t:ℕ}
variable {𝓕:Filter (ℕ×ℕ)} [𝓕.NeBot]{f: Extraction.Order} {S:Table C.book} (U:Spec.Final C f S)(hT:Tendsto T l atTop){p:Prescription U.sector.derivatives} (hP:p.Coherent) {W r D}(L:LogPackage C W r D)(hG:G.Simple)(i₀:I)(v:I→ C.book.Token)
    {s:ι→ I→ Cover}{x:ι→ C.label t}(h:MatrixTicket (C:=C) S U.sector.derivatives 𝓕)(hm:Height C.S l T m a)
open scoped Classical
include U h hP hm hT
local notation "Γ"=> C.path.levels
local notation "α"=> C.S.a
lemma grade_stamp (w: Mode U.sector.derivatives)(he:w.fst≤t)
    (hS:∀ᶠ i in l, Dress (C:=C) 𝓕 S (k i) (m i) (j i) (A i) (V i* C.S.a (m i)^t /C.S.a (j i)^sigma v) v (s i) t (x i))(hv:Wallet l T V) : Wallet l T (fun i=> (C.S.a (j i)^sigma v/C.S.a (m i)^w.1 :ℝ) • p.test w t (S.project t (x i))):=by
    let d i:= C.S.a (j i)^sigma v/C.S.a (m i)^w.1; obtain ⟨q,hq⟩:= h.outlet t w.fst (p.test w t) he (fun e he' x=>by rw [Prescription.affinity U.room.kernel.laws.toSymmetric U.phase.transport.injection p, Prescription.highVan U.room.kernel.laws.toSymmetric U.phase.transport.injection hP w he']);
    apply (((betaStamp hT hm).up.pow hT q).mul hv).of_est; filter_upwards [hm.grows.eventually hq,hS] with i hf hS; obtain ⟨𝓛,ξ,hV,h𝓛,hY,_,hQ⟩:= hS.wins
    have hh:= hf 𝓛 h𝓛 ξ (x i) _ hQ hY; have hU(i):0<d i:= div_pos (pow_pos (C.S.a_pos _) _) (pow_pos (C.S.a_pos _) _); rw [norm_smul,Real.norm_of_nonneg (hU i|>.le)]; apply (mul_le_mul_of_nonneg_left hh (hU i|>.le)).trans_eq; rw [show C.S.a (m i)^t=C.S.a (m i)^(t-w.fst) * C.S.a (m i)^w.fst  from by rw [← pow_add,Nat.sub_add_cancel he]] -- rewrites excess
    have hx:= C.S.a_pos (m i); have hy:= C.S.a_pos (j i); unfold d; field_simp <;> ring -- t−w+w−w lemma

include hG L i₀
lemma grid_ticket (hk:Height C.S l T k b)(hj:Height C.S l T j a)(hb:b<a)(ha:0<b)(hx:∀ᶠ i in l,m i+1<j i)(hM: ValueStamp l T (fun i=> C.S.a (j i)/ C.S.a (m i)))(ht:∀ᶠ i in l, Plot C (k i) (m i) (j i) (s i)) (hU: extentWithin l T (fun i=> C.S.gridPoint (j i) ∘ s i) a)(hY:Kept l T a (fun i=> C.S.gridPoint (j i) ∘ s i))(he:∀ᶠ i in l,Screen (C.S.gridPoint (j i) ∘ s i))(h𝓕:𝓕 ≤ f.fuse)(hr:Org.Grill C f)(w:Mode U.sector.derivatives) :
    Wallet l T (fun i=> (C.S.a (j i)^sigma v/C.S.a (m i)^w.fst :ℝ) • p.ope w (C.S.gridPoint (j i) ∘ s i) v 0):=by
    have hf:Tendsto (fun r:ℕ=>((r:ℝ)+1/16)*(a-b)) atTop atTop:= (tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop (R:=ℝ))).atTop_mul_const (sub_pos.mpr hb)
    let u:= (↑w.fst:ℝ)*a; obtain ⟨n,hN,hn⟩:= ((hf.eventually_gt_atTop u).and (eventually_ge_atTop w.fst)).exists
    obtain ⟨g,o,Q,hg,ho,H⟩:= for_plots (t:=n) U hT L hG i₀ v h𝓕 h hk hm hj hb hx hM ht
    let x i:= (C.S.a (j i)^sigma v/C.S.a (m i)^w.fst :ℝ); have hC : RateIs l T x (u- sigma v*a):= ((hj.mesh.power (sigma v)).div (hm.mesh.power w.fst)).swap (by unfold u; ring); let y i:= p.ope w (C.S.gridPoint (j i) ∘ s i) v 0; let z i:= p.test w n (S.project _ (Q i))
    have hZ := grade_stamp U hT hP v h hm w hn H hg.up; have hD:= det_L (R:=p) U v hT H h𝓕 hr w he hU hY (ha.trans hb) hk hj ha hb ho; have hW:= Wallet.of_strict hT ((hC.pays hT).smul hD) (by change u<((n:ℝ)+ _)*_ at hN; linarith only [hN]); exact (hW.add hT hZ).congr (Eventually.of_forall (fun i=> by change x i • (y i-z i)+x i • z i=x i • y i; rw [smul_sub,sub_add_cancel]))
end YM.OPE.Log
