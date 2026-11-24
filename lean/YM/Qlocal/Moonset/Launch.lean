import YM.Qlocal.Moonset.Fireplace
/-!
### Initialization for CURTAIN (masked real analytic mark class)

This particular startup pays zero on the inherited discrepancy (that's just an example for the
 general recurrence theorem), at any number of iterations later on the unmarked path, permits any
 admissible orientations & *stipulated analytic log interactions*, with exactly these stencil/mask
 realizations and the ACTUAL unmarked vacuum & its own K, firing at the true period and hulls.

 Doesn't start here with other stencils (e.g. a full unmasked cutoff test with a dynamically
 assembled forced input partner). Doesn't construct or assume existential affordability of the
 zero jet with arbitrary precision in a heavy operator. This one starts on matter as it is.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Moonset.Rooms
open Function Filter RG Lattice Wilson Tree Gauge
open Marker Multi Extra.Trajectories Finset
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Integration Integration.LocalComparison Integration.RiderTastePresentation
open Quipu Quipu.Sonnet Quipu.Sonnet.Tern
open Publishing Parabola Reckoner
open Quipu.Eluder.Incline.Bookworm
open Push Push.AbsoluteSums MeasureTheory
open scoped Topology BigOperators Classical ContDiff YM.Qlocal.Payload Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side}{V J:Type}[DecidableEq V] [Fintype V][Nonempty V]
variable (Ω:Type)
variable (B: Marker.Census V)(ξ:V→ℕ)(d b:ℕ)(o:V→Site n) (s:V→Support n)(P:RG.Rep G n)
-- all support choices present in the wallet, even when testing inactive. Mark-slot padding requires at least one mark present in Type.
noncomputable def null (Ω:Type)(B:Marker.Census V)(P:RG.Rep G n)(o:V→Site n)(s:V→ Support n) : Taste Ω o P B:=
 let v :V:=Classical.ofNonempty; ⟨⟨o,fun _=> B.fire v,fun _=> s v,fun _ _=>B.fire v,0,0,0⟩, rfl, fun _=>B.fire v, fun _=> s v,0⟩
local notation "Ψ"=> null Ω B P o s
variable (ho:∀ i,o i∈s i)(q:Ray B) (hq:Rental q){a A C C' E ε δ:ℝ}
include ho
local notation "v!"=>(Classical.ofNonempty:V)
lemma retain_v : RetainsDeclared ∅ (null Ω B P o s) s := by
 refine ⟨ho,?_,fun i j h=>False.elim h,fun i j h x=>rfl,?_⟩
 all_goals intro i a ha; change s a⊆ s _; rw [show a=v! from mem_singleton.mp ha]
lemma peak_v : Peak P o Ψ q a 0 0 := by
 let v:=v!; let T:=Ψ; have hm (j:V) (he:j∈(B.fire v).val) : j=v:=mem_singleton.mp he; have hx(j:V) (he:j∈(B.fire v).val): o j∈s v:= ((hm j he) ▸ (ho j)) -- ▸ order
 constructor
 · intro x; refine ⟨⟨fun _=> Finset.singleton_nonempty _, fun _ _=> hx _,fun _=> (Extra.Histories.regular0 P.p (s v) (o v)).1, fun _ _=> Finset.singleton_nonempty _, fun i j h =>?_, fun i j u l _ _=>rfl, fun i j U h=> False.elim (h rfl), fun _ _=> measurable_const,fun _ _ _ _=>rfl ⟩,fun _=> Finset.singleton_nonempty _,fun _ _ h=> hx _ h ⟩; exact False.elim (h rfl)
 · intro _ _; rfl
 · refine ⟨0,fun i=>le_rfl,fun _ _ j _=>(Extra.Histories.regular0 _ _ _).2,fun i=> ?_⟩; simp only [Pi.zero_apply,mul_zero,zero_mul,ite_self]; exact budget_of_sum (fun _=> le_rfl) (by simp)
 · refine ⟨0,fun i=>le_rfl,fun _ _=>by simp [null],fun i=> ?_⟩; simp only [Pi.zero_apply,mul_zero,zero_mul,ite_self]; exact budget_of_sum (fun _=> le_rfl) (by simp)
 refine ⟨0,fun i=>le_rfl,fun _ _ _=> by simp [null],fun i j h=> by simp at h,fun i=>?_⟩; simp only [Pi.zero_apply,mul_zero,zero_mul,ite_self]; exact budget_of_sum (fun _=>le_rfl) (by simp)
variable (x:Ω)(U:Config G n)(he:P.Lawful a A C C' E)
set_option quotPrecheck false
local notation "H"=> (Ψ).leaf x
include he
--open Caption
lemma real_density : Deck.density (H) U=Poly.bead B (P.eval U:ℂ):= by
 let p:Ray B:=fun i=> Poly.toll (fun _=>1) i; have hw i:p i>0:=Poly.worth (fun _=>zero_lt_one) i; have ht:= peak_v Ω B o s P ho p (a:=P.p.supportExponent); let T:= (H).contents; have h :∀i,T.each i U= Poly.bead B (P.activities.K i U):= by
    intro i; unfold T Bands.each; simp only [Bands.tagged,Taste.leaf,View.terms,null, Pi.zero_apply,Poly.send_zero,tsum_zero,add_zero]; rfl
 have hr(i:ℕ):T.ray i U=0:=by unfold Bands.ray T; simp [Taste.leaf,View.terms,null,masked]; -- simp
 have hg : T.extra U=0:= by unfold Bands.extra; simp_rw [hr]; simp [T,Taste.leaf,View.terms,null];
 have hs:(H).log U=0:= by rw [Deck.log,hg]; simp [Captions.chord,null,Taste.leaf]
 let z:= (Ψ); have hE:= Peak.rotor (w:=fun _=>1) (fun _=>zero_lt_one) ht x; have hp i: T.packet i U=Poly.bead B (P.activities.gasOccurrence P.p i U):= by unfold Bands.packet Activities.gasOccurrence; split; rw [Complex.ofReal_prod,map_prod]; exact Finset.prod_congr rfl (fun i _=> h i); simp
 let hQ:= Bands.population T (ht.active x|>.articles) hE he.labels U; have hX:Nonempty Ω:= ⟨x⟩; apply Marker.Poly.ext; intro i; by_cases h': i=B.quiet; · rw [h',Peak.same ht hw x he U]; exact (show _ from (show (Poly.bead B (P.eval U)).part B.quiet=(P.eval U:ℂ) from (by unfold Poly.bead; change (Poly.send B.quiet _).part _=_; rw [Poly.part_send,if_pos rfl])).symm)
 rw [Deck.density,hs,pass_zero,one_mul]; let v:=(Poly.bead B); have hi(q:ℂ):(Poly.bead B q).part i=0:= by change (Poly.send B.quiet q).part i=_; rw [Poly.part_send,if_neg h']
 rw [hi,Poly.part_smul]; unfold Bands.cluster; change _*(∑' j,T.packet j U).part i=_; rw [Poly.share hQ.1]; simp_rw [hp,hi,tsum_zero,mul_zero]
-- the exact birth with analytic masks intact
variable (Y:Ω→Stanza B G ξ d)(T:∀ i,(Stanza.son (Y i) b).Decision) (v:Ω→Senses B→ℝ)
noncomputable def begin : Wallet Ω o P B ξ d b:= ⟨Y,T,v,Ψ⟩
local notation "C0"=> begin Ω B ξ d b o s P Y T v
lemma opening (W:ℕ)(z:ℝ) : (C0).density W z x U = Poly.pass ((C0).render W z x U)*Poly.bead B (P.eval U:ℂ):= by unfold Wallet.density; rw [show (C0).other=_ from (show _=Ψ from rfl),Rooms.real_density Ω B o s P ho x U he] -- binder notation
omit he
variable {e p t:ℝ}
include hq
lemma usable (hT:∀ i,s i⊆ Calendars.Uplink.habitat n t (o i))(hP:∀ x,(Stanza.son (Y x) b).Allows e 1)(hz:∀ i x,q (x:Senses B).val* |v i x| ≤1)(he:0<p)(hv:p≤1): Wallet.Usable C0 s q e t p:= ⟨hq,hP,hz,hT,⟨∅,retain_v Ω B o s P ho⟩,⟨he,hv⟩,(peak_v Ω B o s P ho q).loosen he.le he.le⟩
end YM.Qlocal.Moonset.Rooms
