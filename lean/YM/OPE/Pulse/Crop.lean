import YM.OPE.Pulse.Baton
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
/-!
# Also get the Resources on the projection
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Menu
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type}[Fintype I][DecidableEq I][Fintype V][DecidableEq V] {B:Census V} {G:Gauge}{n:Side}{R:Census I}
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi
variable {A:Rep G n}{t a e :ℝ}(X:Names R B)
-- field support downstream
variable {r:J→Support n}
private lemma bill (w:V→ℝ)(F:Y→Poly B) (hw:∀ i,0<w i)(hq:Loci w F t) : Loci (w ∘ X.e) (X.restriction ∘ F) t:=by
   obtain ⟨s,hs,hE,hT⟩:=hq; refine ⟨s ∘ X.share,fun i=>hs _,fun i p=>hE _ _, le_trans ?_ hT⟩
   have hh(p): Poly.toll w (X.share p)= Poly.toll (w ∘ X.e) p:= Finset.prod_image X.e.injective.injOn
   unfold wordsPrice; simp_rw [← hh]; exact (le_of_eq (show ∑ i,Poly.toll w (X.share i)*(s ∘ X.share) i= ∑ i∈univ.image X.share,Poly.toll w i*s i from (Finset.sum_image (f:=fun i=> Poly.toll w i*s i) X.inj.injOn).symm)).trans (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> mul_nonneg (Poly.worth hw _).le (hs _))) -- edit sum_image
lemma accountant {q: J→Y→Poly B}{w:V→ℝ}{b:ℕ} (hp:Towed w r q b e t)(hw:∀ i,0<w i): Towed (w ∘ X.e) r (fun i=> X.restriction ∘ q i) b e t := by obtain ⟨a,hh,hp,hz⟩:=hp; exact ⟨a,hh,hp,fun i=> bill X w _ hw (hz _)⟩
variable {p:Support n}{o:V→Site n}{Z:Config G n→Poly B}
lemma nearWill (hr:Borne o p Z t) : Borne (o ∘ X.e) p (X.restriction ∘ Z) t := by
   refine ⟨fun U V hp hh=> congr_arg X.restriction (hr.home U V hp hh), fun k U=> congr_arg X.restriction (hr.turns k U), fun i=> hr.me _,fun i p'=> ?_⟩
   intro h; apply hr.scope i (X.share p'); intro he; apply h; intro v hv; exact he (mem_image_of_mem X.e hv)
lemma carton_here {F K} (h:Carton (G:=G) (B:=B) o F K t): Carton (o ∘ X.e) (fun i=> X.restriction ∘ F i) (fun i=> X.restriction ∘ K i) t:=by
    have hM (p : Poly B)(h:rises p): rises (X.restriction p):=fun i hi=> (h (X.share i) hi).trans_eq (card_image_of_injective _ X.e.injective)
    refine ⟨fun i=>⟨{ nearWill X (h.exp i).1.toBorne with permits:=fun U he=>(h.exp i).1.permits U (fun hh=> he (by simp [Function.comp_apply,hh])), sil:=fun U=>?_ },fun U=>hM _ ((h.exp i).2 U)⟩,fun i=>⟨{ nearWill X (h.flag i).1.toBorne with permits:=fun U he=>(h.flag i).1.permits U (fun hh=>he (by simp [Function.comp_apply,hh])) },fun U=>hM _ ((h.flag i).2 U)⟩⟩
    change (F i U).part (X.share R.quiet)=0; rw [X.quiet]; exact (h.exp i).1.sil U
lemma bead_read (b:ℂ) : X.restriction (Poly.bead B b)= Poly.bead R b:=by ext s; change (Poly.send B.quiet b).part (X.share s)=(Poly.send R.quiet b).part s; simp only [Poly.part_send,← X.quiet,X.inj.eq_iff]
lemma mach_read (f: V→ℂ) : X.restriction (Mach B f)= Mach R (f ∘ X.e):=by
   ext i; change (Mach B f).part (X.share i) = _; by_cases he:2 ≤ i.val.card; rw [hush _ _ (le_trans he (le_of_eq (Finset.card_image_of_injective i.val X.e.injective).symm)),hush _ i he]; rcases Nat.eq_zero_or_pos i.val.card with h|h
   · rw [show i=R.quiet from Subtype.ext (card_eq_zero.mp h),X.quiet, mute,mute]
   obtain ⟨j,hj⟩:= card_eq_one.mp (show i.val.card=1 from by omega); rw [show i=R.fire j from Subtype.ext hj,X.fire, Accent.sing, Accent.sing]; rfl
lemma field_r (p : Support n)(F: Box n→Poly B): X.restriction (field F p)= field (X.restriction ∘ F) p:=by unfold field; rw [map_sum]; apply sum_congr rfl; intro i _; unfold grid; split; exact map_prod ..; exact map_zero _
variable {X} in
lemma Served.read (X:Names R B){w:V→ℝ}{L₀:V → Config G n→ℂ}{S}(h:Served A L₀ S Z o w t a) (hw:∀ i,0<w i) : Served A (L₀ ∘ X.e) (S ∘ X.e) (X.restriction ∘ Z) (o ∘ X.e) (w ∘ X.e) t a:=by
   obtain ⟨F,K,ht,hq,he,rfl⟩:=h; refine ⟨_,_,carton_here X ht,accountant X hq hw,accountant X he hw,?_⟩
   funext U; unfold restore; dsimp only [Function.comp_apply]; rw [X.smul, map_mul,X.pass_restrict (by rw [Poly.part_plus,mute,zero_add,Poly.part_sum]; exact sum_eq_zero fun i _=> (ht.exp i).1.sil _), map_add,map_sum,mach_read, field_r]; congr 2
   apply congr_arg (fun f=> Accent.field f (flags A.p.threshold U)); funext p; unfold bar; simp_rw [Function.comp_apply,map_add,mach_read,bead_read];rfl
end YM.MergeProof.Accent
