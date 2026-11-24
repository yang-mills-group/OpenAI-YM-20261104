import YM.OPE.Screens.Slot
import YM.OPE.ElementaryLog
/-! # Copper down.Meter-grade costs for pixels in any rank order -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Shuttle
open Function Filter Finset MeasureTheory Lattice RG Wilson Next.UVStress Spec
open Rhythm Payments Booking
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Z : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] {G: Gauge}
    {H t n b k l d e:ℕ}{Q: Rhythm I}{C: Family G}
set_option quotPrecheck false
variable {F:Extraction.Order}{S:Table C.book}(U: Final C F S)
variable {Y:Type}{f:Filter Y}[f.NeBot]{x:Y→ I→ Cover}{X:Y→ I→ E4}{y:Y→ E4}{T a a' o q c r': Y→ℝ}{R r:Y→ℕ→ℝ}{α:ℕ→ℝ}{η M P₀:ℝ}
    {P:Y→Loom Q} {B: Border f T Q.limit R r α} (D:Oscars B P₀ P C) {W r'' D'} (L:LogPackage C W r'' D')
    (w:Mode U.sector.derivatives) {φ:Filter (ℕ×ℕ)} [φ.NeBot] (h:φ≤ F.fuse) {k':Y→ℕ}
    (V:MatrixTicket (C:=C) S U.sector.derivatives φ)(LL : Services C F S){G':Prescription U.sector.derivatives}(hG:G'.Coherent)
    {z:Y→ C.label d}
local notation "μ!"=> C.S.a
local notation "L!"=> (fun i=> (P i).launch Q.limit)
local notation "K"=> C.path.levels.clock.hatBeta
local notation "κ"=> Wallet f T
local notation "D0"=> U.sector.derivatives
local notation "m!"=> (fun i=> (P i).below t)
local notation "O!"=> (fun i=> c i/R i t^w.1)
variable (v:I→ C.book.Token)
local notation "v'"=> (fun j=> (v j).1)
include D
lemma resize (h:t ≤ Q.limit) : κ (fun i=> run (R i t)):=by
    have hy:= B.ahead h; apply (Wallet.from_tends B.life hy.rate).neg.mul (Wallet.id B.life)|>.congr; filter_upwards [B.life.eventually_gt_atTop 0] with i hi; unfold run; field_simp
lemma soon (h:t ≤ Q.limit) (hk:∀ᶠ i in f,‖y i‖ ≤ R i t*M): Tendsto (fun i=> ‖y i‖) f (𝓝 0):= squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) hk (by simpa only [zero_mul] using! ((B.narrows t h).mul_const M))
lemma closing (hX:∀ᶠ i in f,draft Q (R i) (r i) M η H (X i))(hH:H ≤ Q.age Q.star)(hm:0 ≤ M) (j:I): Tendsto (fun i=> ‖X i j‖) f (𝓝 0):=by
    refine soon D (Nat.zero_le _) (M:=2*M) ?_; filter_upwards [B.envelope hH hm hX (Nat.zero_le _)] with i hi; have h:=hi j; rw [Q.lead_zero (Q.pinned_init _) _,sub_zero] at h; exact h.trans_eq (by ring)
include U V h L LL hG
lemma shifted (hp:t ≤ Q.limit)(hm:0 ≤ M)(hk:∀ᶠ i in f,‖y i‖ ≤ R i t*M) (e: Mode D0) : κ (fun i=> (R i t^e.fst/R i t ^ w.fst:ℝ) • G'.ope w v0 (sole (G'.letter e)) (y i)) := by
    let r i:=R i t; have ht:Tendsto r f (𝓝[>]0):= tendsto_nhdsWithin_iff.mpr ⟨B.narrows t hp,(B.ahead hp).pos⟩; let P:= sole (G'.letter e); have he:= Log.compensated_coeff U P LL L h V hG (r:=r) (z:=y) (x:=fun _=>v0) ht hm zero_lt_one (show ∀ᶠ i in f,WithinRoom _ _ _ _ _ from ?_) w; rw [show sigma P=e.fst from (by unfold sigma P; simp; rfl)] at he; exact Wallet.raise (run_towards ht) he (resize D hp)
    filter_upwards [hk] with i hi using ⟨fun j=> (by change ‖(0:E4)-y i‖ ≤ _; simp only [zero_sub,norm_neg]; linarith only [show ‖y i‖ ≤ r i*M from hi]), fun i j h=> (h (Subsingleton.elim ..)).elim⟩
omit h L LL
local notation "Pχ"=> (fun i q=> G'.test q d (S.project d (z i)))
lemma outletPrice (hp:t ≤ Q.limit)(ht:w.1 ≤ d)(ha:Wallet f T (fun i=> a i * c i /(R i t)^d))(hy:∀ᶠ i in f,0< c i)
    (hz:∀ᶠ i in f,∃ (g:Filter (ℕ×ℕ))(V:ℕ×ℕ→ C.label d),g.NeBot ∧ g ≤ φ ∧ Adoption C ((P i).below t) (a i) d (z i) g V) : κ (fun i => (c i/(R i t)^w.fst:ℝ) • Pχ i w):=by
    obtain ⟨p,hp'⟩:= V.outlet d w.fst (G'.test w d) ht (fun e he x=>by rw [Prescription.affinity U.room.kernel.laws.toSymmetric U.phase.transport.injection G',Prescription.highVan U.room.kernel.laws.toSymmetric U.phase.transport.injection hG w he]); have hx:= D.lower t hp; have hT:= B.life; have hw:= D.loggap t hp
    apply (((betaStamp hT hx).up.pow hT p).mul ((hw.inv.up.pow hT (d-w.1)).mul ha)).of_est; filter_upwards [hz, hx.grows.eventually hp',hy,(B.ahead hp).pos] with i hi hv hc hR; obtain ⟨g,v,hg,he,hv'⟩:=hi; let x:= m! i; let y:= R i t; have he':= hv g he v (z i) (a i) hv'.tickets hv'.wins; rw [norm_smul,Real.norm_of_nonneg ((div_pos hc (pow_pos hR _)).le)]
    apply (mul_le_mul_of_nonneg_left he' (show 0 ≤ c i/(R i t)^w.fst from (by positivity))).trans_eq; have hx:= C.S.a_pos (m! i); rw [show (R i t)^d=(R i t)^(d-w.fst) * R i t ^ w.fst from by rw [← pow_add,Nat.sub_add_cancel ht]]; rw [inv_div,div_pow]; field_simp
include h L LL
lemma fare (hp:t≤ Q.limit)(ht:w.1 = d)(hy:∀ᶠ i in f,0< c i)(ha: Wallet f T (fun i=> a i *c i / (R i t)^d))(hm:0 ≤ M)(hk: ∀ᶠ i in f, ‖y i‖ ≤ R i t*M)
    (hz:∀ᶠ i in f,∃ (g:Filter (ℕ×ℕ))(V:ℕ×ℕ→ C.label d),g.NeBot∧ g ≤ φ∧ Adoption C ((P i).below t) (a i) d (z i) g V) : κ (fun i=> (c i/(R i t)^w.fst:ℝ) • G'.ope w v0 (negative (z i)) (y i)):=by
    let x'(q: Mode D0)(i:Y):= Pχ i q * G'.ope w v0 (sole (G'.letter q)) (y i); let P:= U.room.kernel; let f i:= G'.ope w v0 (negative (z i)) (y i); have hf(i): f i=∑ j ∈ bands D0 d,x' j i:=Prescription.phaseAtOne G' P.laws.toSymmetric U.phase.transport.injection hG w (z i) 0 (y i)
    have he(q:Mode D0)(he:q∈ bands D0 d): κ (fun i=> (O! i:ℝ) • x' q i):=by
       apply ((outletPrice U D q V hG hp ((full_bands ..).1 he) ha hy hz).mul (shifted U D L w h V LL hG hp hm hk q)).congr; filter_upwards [(B.ahead hp).pos,hy] with i hi hy; rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]; -- inspect
       have hy' : c i/R i t^q.fst*(R i t^q.fst/R i t^w.1)=c i/R i t^w.1:=by field_simp
       rw [hy']
    apply (Wallet.sum B.life he).congr; filter_upwards with i; change _=(O! i:ℝ) • f i; rw [hf,smul_sum]
end YM.OPE.Log.Trunk.Shuttle
