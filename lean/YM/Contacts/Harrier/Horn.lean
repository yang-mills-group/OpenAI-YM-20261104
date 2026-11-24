import YM.Contacts.Harrier.First
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
open Cartons Pierian Font MultiNext.SignedSource Pattern Tensor Barrage.Reserve.Oasis
variable {H:Labels.Frame G h}(v:Badge H){x:Dye G}{P V:Sketch G} (hp:Living x M D V ζ)(hζ:0<ζ)
include hp hζ
lemma Badge.key_add (h:Living x M D P ζ): v.key (V+P) M i=v.key V M i+v.key P M i:= by simpa only [Badge.key,Pi.add_apply,one_mul,one_smul] using fill_linear H (hp.lineage v.phi) (h.lineage _) hζ 1 i v.loc -- order resolution
lemma Badge.key_scale (a:ℝ) : v.key (a • V) M i=a*v.key V M i:= by simpa only [Badge.key,Pi.smul_apply,Pi.zero_apply,add_zero,fill_null H x] using fill_linear H (hp.lineage v.phi) (Based.zero (v:=x) (ζ:=ζ) (M:=M)) hζ a i v.loc
omit hp
lemma Badge.key_many {F:A→Sketch G}(q:Finset A)(hq:∀ i∈q,Living x M D (F i) ζ): v.key (∑ i∈q,F i) M i=∑ j∈q,v.key (F j) M i:= by induction q using Finset.induction with| empty=> simp [Badge.key,fill_null H x]| insert i p hi ih=>rw [sum_insert hi,sum_insert hi,Badge.key_add _ (hq i (mem_insert_self ..)) hζ (Living.sum p _), ih] <;> exact fun _ h => hq _ (mem_insert_of_mem h)
lemma cursor_rate (H:Labels.Frame G hval)(k j:ℕ):∃ C≥(0:ℝ),∀ (X:Field (Fin k) (Node (Dye G))) (x:Dye G) (b:ℝ),b≥0 →Rest (terrain ζ _) (0,x) X b → ‖cursor H j k X‖ ≤ C*b:= by
    obtain ⟨a,ha,h⟩:= choice_bill (X:=bins G hval k) (Y:=H.Coeff) (peek H j k); let T:= hval; -- shadows h from binder
    obtain ⟨c,hc,P⟩:= Pocket.tower_exp (G:=G) k hval hζ; refine ⟨_,mul_nonneg ha hc, fun X x b hb ht=>?_ ⟩; unfold cursor; rw [tower_express]; exact (h _).trans ((mul_le_mul_of_nonneg_left (P (Pi.single k X) x b hb (fun r he=> by by_cases hw:r=k; subst r; rwa [Pi.single_eq_same]; rw [Pi.single_eq_of_ne hw]; exact Rest.ist Rest.zero hb)) ha).trans_eq (mul_assoc ..).symm)
lemma Badge.head_price (hk:v.slot ≤ M) (x:Dye G): ∃ C≥(0:ℝ),∀ (V:Sketch G), Living x M D V ζ→∀ b≥(0:ℝ), Harrier.Before (terrain ζ _) D x V i v.slot b→ ‖v.key V M i-(cursor H v.pull v.slot (sail V i v.slot v.phi) v.loc).re‖ ≤ C*b:= by
    obtain ⟨a,ha,Q⟩:= choice_bill (X:=bins G h v.slot) (Y:=H.Coeff) (peek H v.pull v.slot); obtain ⟨y,hy,hV⟩:= Pocket.tower_exp (G:=G) v.slot h hζ; obtain ⟨s,hs,hp'⟩:= Cards.reach D v.phi; refine ⟨_, mul_nonneg (mul_nonneg ha hy) hs,fun V hv b hb hZ' =>?_⟩;
    obtain ⟨H',Z,hZ⟩:= hv.lineage v.phi; let k:= v.slot; let n:=M+4+i-k; let Y:= V v.phi; let R:= coil Y M n; let P:=Y i k; have h': R k=P:= Pocket.current_coil _ _ (hk.trans (by omega)); have hB:=coil_tags H' hZ hζ n; let T:= tower R h k; let X: Cohort G:=update R k 0; let U:=h*(h+1); let F:= subcode (d:=h) (Shuttle.sheet k P (Tide.lens G U)); let f:=peek H v.pull k; have he j (hj:j ≤ k): Rest (terrain ζ _) (0,x) (X j) (b*s):= by
        unfold X; by_cases he:j=k; · subst j; rw [update_self]; exact Rest.ist Rest.zero (mul_nonneg hb hs)
        rw [update_of_ne he]; exact (Pocket.subprice (M:=M) hb hZ' (hk.trans (Nat.le_add_right ..)) j (lt_of_le_of_ne hj he)) _ _ hs hp'
    have hm : T-F=tower X h k:= by
       funext j; refine Fin.lastCases ?_ (fun i=>?_ ) j; swap
       · have hh : (i.castSucc.val)≠k:=(by simp; omega); -- scope
         unfold T X F subcode tower; simp only [Pi.sub_apply,Pi.single_eq_of_ne (Fin.castSucc_ne_last _),sub_zero,update_of_ne hh]
       let a:= Fin.last k; unfold T X F Cartons.tower subcode; simp_rw [Pi.sub_apply,Pi.single_eq_same,Fin.val_last,update_self,h']; -- R k -> P or proof wrong
       change Shuttle.sheet k P (Tide.lens G U)- Shuttle.sheet k P (Tide.lens G U)=Shuttle.sheet k 0 (Tide.lens G U); rw [sub_self]; exact (show 0= ∑' i : Fin k→Node (Dye G), blanket k 0 (Tide.lens G U) i from Eq.trans tsum_zero.symm (tsum_congr fun i=> ContinuousMultilinearMap.ext fun v=> by simp [blanket_response]))
    unfold Badge.key fill; rw [if_pos (by change k ≤ _; omega)]; have hk' : (↑(velum H R v.loc):ℂ)= f T v.loc:= (cane hB v.loc).symm; rw [show velum H _ v.loc= (f T v.loc).re from Eq.trans (show velum H _ v.loc=(Complex.ofReal (velum H R v.loc)).re from rfl) (congr_arg Complex.re hk')]; change ‖(f T v.loc).re-(f F v.loc).re‖ ≤ _; calc
        _ ≤ ‖(f (T-F)) v.loc‖:= by rw [map_sub]; exact (Complex.abs_re_le_norm (f T v.loc - f F v.loc)) -- norm≤ ???? 
        _ ≤ _:= (norm_le_pi_norm (f _) v.loc).trans ?_
    rw [hm]; exact (Q _).trans ((mul_le_mul_of_nonneg_left (hV X x _ (mul_nonneg hb hs) he) ha).trans_eq (by ring))
end
end YM.Contacts.Harrier
