import YM.OPE.Screens.Coppers
/-!
# Unselected coefficient liability on real grids

Parameterization over a fixed membership: λ determined once by P. Readers
at the cell viewpoint, not necessarily its origin. Keep sign until proceeding
in other rows. Center-core observations are continued at that horizon exactly
once. The signed variants first measured against one term in which the
child marker is the *matched physical field* at another captured horizon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Shuttle
open Function Filter Finset MeasureTheory Lattice RG Wilson Next.UVStress Spec
open Rhythm Payments Booking
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Z : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] {G: Gauge}
    {H t n b k l d e:ℕ}{Q: Rhythm I}{C:Family G}
set_option quotPrecheck false
variable {F:Extraction.Order}{S:Table C.book}(U: Final C F S)
variable {Y:Type}{f:Filter Y}[f.NeBot]{x:Y→ I→ Cover}{X:Y→ I→ E4}{y:Y→ E4}{T a a' o q c r': Y→ℝ}{R r:Y→ℕ→ℝ}{α:ℕ→ℝ}{η M P₀:ℝ}
    {P:Y→Loom Q} {B:Border f T Q.limit R r α} (D:Oscars B P₀ P C) {W r'' D'} (L:LogPackage C W r'' D')
    (w:Mode U.sector.derivatives) {φ:Filter (ℕ×ℕ)} [φ.NeBot] (h:φ≤ F.fuse) {k':Y→ℕ}
    (V:MatrixTicket (C:=C) S U.sector.derivatives φ)(LL : Services C F S){G':Prescription U.sector.derivatives}(hG:G'.Coherent)
local notation "L!"=> (fun i=> (P i).launch Q.limit)
local notation "ξ!"=> (fun i=> C.S.gridPoint (L! i) ∘ x i)
variable (v:I→ C.book.Token)
include D L h V LL hG
local notation "M!"=> (fun i=> priceSet Q univ v (R i))
local notation "Fo" => (fun i=> M! i/(R i 0)^w.fst)
variable (hm:0 ≤ M)(hq:8*M<P₀)(hc:0<η)(hy:∀ᶠ i in f,‖y i‖ ≤ R i 0 *M) (hV:∀ᶠ i in f,Seated Q C (P i) (C.S.gridPoint ((P i).launch Q.limit) ∘ x i) H)
    (hh: H ≤ Q.age Q.star)
    (hU:∀ᶠ i in f,draft Q (R i) (r i) M η H (C.S.gridPoint ((P i).launch Q.limit) ∘ x i))
include hm hq hc hy hh hU hV
lemma survey : Wallet f T (fun i=> (Fo i:ℝ) • G'.ope w (ξ! i) v (y i)):=by
    let v':= LL.simpleGate; obtain ⟨b,hv,hu,hs⟩:= ((enough U (G'.sheet w).support (soon D (Nat.zero_le _) hy)).and ((eventually_ge_atTop (C.ref w.fst)).and (eventually_gt_atTop (C.ref 0)))).exists; have hγ:= B.for_grid D hh hm hU L v' b x EventuallyEq.rfl hq hc hV; let k:=w.fst; let y':= Fo
    obtain ⟨a,a',z,ha,hA,hZ⟩:= ticks U D h L LL.simpleGate v V hs hu hh (hγ.mono fun i hi=>hi.laughs) hU hm; have hP:∀ᶠ i in f,0 < y' i:=by filter_upwards [mass_pos D v univ,(B.ahead (Nat.zero_le _)).pos] with i hi hh using div_pos hi (pow_pos hh _)
    have hC := firstTicket U w h LL.schedule v (hγ.mono fun i hi=> hi.comps) (closing D hU hh hm) hv (show Wallet f T (fun i=> y' i * a' i) from hA.congr (Eventually.of_forall (fun i=>by dsimp only [y']; ring))) hP ((D.upper (Q.limit) le_rfl).grows.eventually_ge_atTop b) B.life hZ
    have he:= fare U D L w h V LL hG (t:=0) (z:=z) (Nat.zero_le _) rfl (mass_pos D v univ) ha hm hy (hZ.mono (fun i hi=>by obtain ⟨g,p,z',v,hg,hh,h₁,h₂,hX⟩:= hi.ready; exact ⟨g,v,hg,hh,h₂⟩)); apply (hC.add B.life he).congr; filter_upwards with i; unfold y'; rw [smul_sub,sub_add_cancel]
local notation "G₁"=> (fun i=> Payments.priceSet Q (Q.focus H) v (R i))
local notation "Ω"=> (fun i=> Payments.fuel (R i) H l e)
local notation "s!"=> Q.focus H
-- analytic mismatch: main residual plus child exact coefficients
local notation "Λ"=> U.sector.derivatives
omit hh
lemma swipe (hH:Q.Strike H l)(e:ℕ) : ∃ z:Y→ C.label e,
    Wallet f T (fun i=> (priceSet Q univ v (R i) * Payments.fuel (R i) H l e / R i 0 ^ w.fst:ℝ) • (G'.ope w (ξ! i) v (y i)-G'.ope w (substituted s! (ξ! i)) (substituted_row s! v (z i)) (y i))) ∧
    ∀ b∈ bands Λ e, Wallet f T (fun i=> (G₁ i/R i H^e:ℝ) • (G'.ope b (chunk s! (ξ! i)) (chunk s! v) 0-G'.test b e (S.project _ (z i))))∧ Wallet f T (fun i=> (G₁ i/R i H^b.fst:ℝ) • (G'.test b e (S.project _ (z i)))):=by
    let v':=LL.simpleGate; let k:=w.fst; have he:H ≤ Q.age Q.star:= hH.exists_.symm.le; let s:= bands Λ e; let Z(_:Y):=(0:E4)
    obtain ⟨b,hv,hQ,hZ,hu,hp⟩:= ((enough U (G'.sheet w).support (soon D (Nat.zero_le _) hy)).and ((eventually_gt_atTop (C.ref 0)).and (((eventually_all_finset s).mpr fun i hi=> enough (y:=Z) U (G'.sheet i).support (show Tendsto _ f _ from by simp only [norm_zero,Z]; exact tendsto_const_nhds)).and ((eventually_ge_atTop (C.ref e)).and (eventually_ge_atTop (C.ref k)))))).exists
    have hγ:= B.for_grid D he hm hU L v' b x EventuallyEq.rfl hq hc hV; let M(i):= priceSet Q univ v (R i) * Payments.fuel (R i) H l e; let M'(i):= G₁ i; let q(i):= M i /R i 0 ^ k; let q'(i):= M' i/R i H^e
    obtain ⟨a,a',c,c',z,y',ha,hA,hd,hD,hW⟩:= responsible U D h L LL.simpleGate v V (d:=k) hQ hp (hγ.mono fun i hi=> hi.laughs) hU hm hH hu hc
    have ht0:=(B.ahead (Nat.zero_le _)).pos; have hH₁ := (B.ahead hH.atMost).pos; have hξ:∀ᶠ i in f,0 < M i:=by filter_upwards [mass_pos D v univ,fuel_pos D e (hH.before.le.trans hH.atMost) hH.atMost] with i hi he using mul_pos hi he
    have hΦ:= (hξ.and ht0).mono (fun i hi=>show 0 < q i from div_pos hi.1 (pow_pos hi.2 _)); have hs:∀ᶠ i in f,Screen (ξ! i):=hγ.mono fun i hi=> hi.comps; have hΛ:= (D.upper _ le_rfl).grows.eventually_ge_atTop b
    let p':= Q.focus H; have hΓ:∀ᶠ i in f,Screen (substituted p' (ξ! i)):= by
       filter_upwards [hγ] with i hi; apply Screen.reserve.mpr; refine ⟨(fun j=>injective_of_subsingleton _),Probe.pinned hi.comps, fun _ j a=>?_⟩; have hx:j.val∉ p':= (mem_sdiff.mp j.property).2; have he:(C.S.gridPoint (L! i) ∘ x i) j.val a≠ 0:=hi.avoids j.val ((Q.flip Q.star j.val).trans_lt ((hH.reserve j.val hx).trans_lt hH.before)) hx a; exact he.symm
    have hK := mainTicket U w h LL.schedule v hs (closing D hU he hm) hv (show Wallet f T (fun i=> q i * a' i) from hA.congr (Eventually.of_forall (fun i=>by dsimp only [q,M,k]; ring))) hΦ hΛ B.life hΓ hW
    have hU' := fare U D L (z:=z) (c:=M) w h V LL hG (t:=0) (Nat.zero_le _) rfl hξ ha hm hy (hW.mono (fun i hi=>by obtain ⟨g,p,z',v,u,hg,hh,h₁,h₂,h₃,hX⟩:=hi.ready; exact ⟨g,v,hg,hh,h₂⟩))
    refine ⟨y', (hK.add B.life hU').congr ?_,fun i hi=>?_⟩; · filter_upwards with i; change q i • _+q i • _= q i • _; rw [smul_sub,sub_add_cancel]
    have hU₁:∀ᶠ i in f,0 < M' i:= mass_pos D v p'; have h₁:= (hU₁.and hH₁).mono (fun i hi=>show 0 < q' i from div_pos hi.1 (pow_pos hi.2 _))
    refine ⟨(childTicket U i h LL.schedule v hs (closing D hU he hm) (hZ i hi) (show Wallet f T (fun i=> q' i*c' i) from hD.congr (Eventually.of_forall fun i=>by dsimp only [q',M']; ring)) h₁ hΛ B.life hW).congr ?_,outletPrice U D i V hG hH.atMost ((full_bands ..).1 hi) hd hU₁ (hW.mono (fun i hi=> by obtain ⟨g,v,z',u,y,hg,hg',hp,hy,he,hX⟩:=hi.ready; exact ⟨g,y,hg,hg',he⟩))⟩
    filter_upwards with j; rw [show G'.ope i v0 (negative (y' j)) (Z j)= _ from Prescription.insertOne _ G' (y' j) U.room.kernel i] -- arg order
end YM.OPE.Log.Trunk.Shuttle
