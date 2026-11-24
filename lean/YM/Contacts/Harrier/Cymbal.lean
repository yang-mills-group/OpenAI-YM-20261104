import YM.Contacts.Harrier.Horn
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
namespace Transfer
open Parcel Prairie Planned.PrimaryIntegral295
variable {e:Parcel G} {p:Word}{s:Parcel.Step}{S:Boom} (T:e.License S ζ)(hp:OK S p)(hs:s∈S)
local notation "Γ" => terrain ζ (Dye G)
local notation "Υ" => terrain (2*ζ) (Dye G)
open Cartons Pierian Font MultiNext.SignedSource Pattern Tensor Barrage.Reserve.Oasis
variable {X: Sketch G} {H:Labels.Frame G h}{K:ℕ} (x:Dye G)(hT:Demand S e M K)(hi:i≤ K){v:Site s.L}
-- earlier generations on one port.S.No assumption of ability across history
include hs T hT hi
lemma prior_passed (v:Site s.L): ∃ C≥(0:ℝ),∀ p:Word,OK S p→∀ F:Sketch G,Living x M D F ζ→∀ b≥(0:ℝ), Harrier.Before Γ D x F i r b→ Harrier.Before Υ D x (pass e p s M v F) i r (C*b):= by
   let R (q:ℕ×ℕ) (a:ℝ):Prop:= ∀ p:Word,OK S p→∀ F: Sketch G,Living x M D F ζ→ ∀ b≥(0:ℝ),Harrier.Before Γ D x F i r b→Past i r q.1 q.2→ Enroll Υ D x (pass e p s M v F) q.1 q.2 (a*b) -- type q
   let W:= Finset.Iic i ×ˢ Finset.Iic (M+i); have hX (q:ℕ×ℕ)(hv: Past i r q.1 q.2)(hr : q.2≤ M+q.1) :q∈ W:= by unfold Past at hv; simp only [W,mem_product,Finset.mem_Iic]; omega
   have HH (p:Word)(hp:OK S p)(F:Sketch G)(H:Living x M D F ζ)(q z:ℕ)(a:ℝ)(ha:0≤a)(he:M+q<z): Enroll Υ D x (pass e p s M v F) q z a:= by rw [Enroll,show sail _ q z=0 from (show sail (pass e p s M v F) q z=0 from funext fun i=> ((received T hp hs H).lineage i).1.incarnate.thin q z he)]; exact w_raise w_zero ha
   have hR (q:ℕ×ℕ)(hq:q∈W):∃ a≥(0:ℝ),R q a:= by
    by_cases ht:q.2 ≤ M+q.1; · obtain ⟨a,ha,h⟩:= (Transfer.passport (D:=D) (v:=v) T hs x hT _ (((mem_Iic.mp (mem_product.mp hq).1)).trans hi) q.2 ht).2; exact ⟨a,ha,fun p hp F H b hb g ht=> (h F H _ hb (g.earlier ht)).1 p hp⟩
    exact ⟨_,show 0≤(0:ℝ) from le_rfl,fun p hp F hF b _ _ _=> HH p hp F hF q.1 q.2 (0*b) (zero_mul ..|>.ge) (by omega)⟩
   obtain ⟨C,hc,h⟩:= collective (P:=R) W (fun _ _ _ ha h p hp F H b hb hv ht=> w_raise (h p hp F H b hb hv ht) (mul_le_mul_of_nonneg_right ha hb)) hR
   exact ⟨C,hc,fun p hp F hF b hb ht j k h'=> by by_cases hg : k≤ M+j; exact h (j,k) (hX (j,k) h' hg) p hp F hF b hb ht h'; exact HH p hp F hF _ _ _ (mul_nonneg hc hb) (by omega) ⟩
omit hT hi hs
variable (u: Badge H)
include T
lemma motion_remains {X : Sketch G} (hx: Living x M D X ζ)(h': (u.pull) ≤ e.J)(hr:r≤M+i)(hH:∀ v:Badge H,∀ i,v.key X M i=0) : Remains u.pull (motion e p s v i r X u.phi) := by
    let L:= s.L; let Y:= desk s v u.phi; let T':=M+4+i-r; have hv:x=x:= rfl; obtain ⟨he,Q,hC⟩:= hx.lineage Y; have hz:Tags (coil (X Y) M T'):= coil_tags he hC T.light T'; have hK:= H.bound u.loc; have ha: Remains u.pull (coil (X Y) M T' r):= Pierian.remains_story H hz hK (fun i hi=> ?_)
    · rw [Pocket.current_coil _ _ hr] at ha -- args
      let X':= X Y i r; show Remains u.pull (printRun (Trace.wreath (curb s v) (install (Origin.bleed G (e.gas p s))) X')); exact reveals (e.path p s) e.K.penalty_pos e.ready h' (he.incarnate.sym i r) ha T.light (hC.lands i r) _
    · rw [Cartons.fueled he x T.light hC]; split; swap; · rfl
      let f:= (card_price hx T.light i
            (T'+(H.grades i).2-(M+4))).mk' _; change f Y=0; unfold Y desk; change f (Cards.onRoute _ _ (plait _))=0; rw [Font.translate,map_sum]; apply Finset.sum_eq_zero; intro l hl; have hu:=u.win_le; exact inner_void (r:=h) hx T.light le_rfl (fun i _=> hH i _) l _ i (lit _) (by have h : l ≤ u.num:= Nat.le_of_lt_succ (Finset.mem_range.mp hl); unfold Badge.win at hu; omega)
include hs hT hi
-- projection estimate: vital doesn't reuse gain rate $L^-c$ then amplify L.Fr.`
theorem projected (z:Site s.L)(hk:h≤e.J)(hv:u.slot ≤ M): ∃ a≥(0:ℝ),∀ V:Sketch G,Living x M D V ζ→∀ b≥(0:ℝ), Harrier.Before Γ D x V i u.slot b→(∀ v:Badge H,∀ i,v.key V M i=0) → ∀ p:Word,OK S p→ ‖u.key (pass e p s M z V) M i‖ ≤ a*b := by
    let k:=u.slot; have hr :u.slot ≤ M+i:= hv.trans (Nat.le_add_right ..); obtain ⟨a,ha,A⟩:= prior_passed (D:=D) (r:=u.slot) T hs x hT hi z; have he (V:Sketch G)(v:Word)(b:ℝ) (H:Harrier.Before Υ D x (pass e v s M z V) i u.slot b) : Harrier.Before Γ D x (pass e v s M z V) i u.slot b:= H.weaken le_rfl (fun i a=> terrain_le T.down a)
    obtain ⟨q,hq,Y⟩:= u.head_price (D:=D) T.light hv x; obtain ⟨c,hc,C⟩:= keep_est (k:=0) (D:=D) T hs z x hr; obtain ⟨d,hd,O⟩:= (passport (D:=D) (v:=z) T hs x hT i hi u.slot hr).1; obtain ⟨t,ht,H'⟩:=cursor_rate T.light H k u.pull; obtain ⟨w,hw,hW⟩:=Cards.reach D u.phi -- H collision
    refine ⟨_,add_nonneg (mul_nonneg hq ha) (mul_nonneg (mul_nonneg ht (add_nonneg hd hc)) hw), fun V hv b hb hp hh p Hq=> ?_⟩; let Z:= pass e p s M z V; have hv':= (received T Hq hs hv (v:=z)).lower T.down; let K:= u.key Z M i; let P:= Z u.phi i k; let D':= motion e p s z i k V u.phi; let x':Fin 0→ℝ:=0 -- dummy
    have h':= he _ _ _ (A _ Hq V hv b hb hp); have ht':=Y _ hv' (a*b) (mul_nonneg ha hb) h'; have hD: Rest Γ (0,x) (P-D') ((d+c)*w*b):= by
       let W:=keep e p s z M i k V u.phi; let Q:=lead e p s z i k V u.phi; have hm:Q=D'-W:= congr_fun (primogen T Hq hs z hr hv) _; have hvP:= w_lower ((O V hv b hb hp).1 p Hq) T.down; have hy: Weight (keep e p s z M i k V) D Γ x (c*b):= w_upped (C V b hb hp p) le_rfl (fun _=> bath_terrace _); rw [show P-D'= P-Q-W from (by rw [hm]; abel)]; refine ((hvP u.phi w hw hW).sub (hy u.phi w hw hW)).ist (le_of_eq (by ring))
    obtain ⟨hk',g,hg⟩:= hv'.lineage u.phi; have hy: Rest Γ (0,x) P _:= hg.lands i k; have hy':=hy.sub hD; change Rest _ _ (P-(P-D')) _ at hy'; rw [show P-(P-D')=D' by abel] at hy'; let C':= cursor H u.pull k; have hp : C' P = C' (P-D') := by refine Eq.symm ?_; rw [show C' (P-D')= C' P-C' D' from curs_sub H hy hy' T.light T.light (hk'.incarnate.sym i k) (print_even _) u.pull, show C' D'=0 from Pierian.skims H (print_even _) hy' T.light (H.bound u.loc) (motion_remains T x u hv ((H.bound u.loc).trans hk) hr hh), sub_zero]
    let Q:=(C' P) u.loc; have h: ‖Q.re‖≤ t*((d+c)*w*b):= calc
          _ ≤ ‖Q‖:= Complex.abs_re_le_norm Q
          _ ≤ _:= (norm_le_pi_norm (C' P) u.loc).trans (by rw [hp]; apply H' _ _ _ hD.cash hD)
    change ‖K‖≤ _; have he:= (norm_add_le (K-Q.re) Q.re).trans (add_le_add (show ‖K-Q.re‖ ≤ q*(a*b) from ht') h); rw [sub_add_cancel] at he; exact he.trans_eq (by ring)
omit hT hi
include hp
lemma concert (h':Living x M D X ζ)(t:ℕ): u.key (Transfer.mean e p s M t X) M i= pay s t *∑ v:Site s.L,u.key (pass e p s M v X) M i:= by
   have hV v:= received T hp hs (v:=v) h'; unfold Transfer.mean; rw [u.key_scale (Living.sum univ (fun v _=>hV v)) (lt_of_lt_of_le T.light T.down),u.key_many (lt_of_lt_of_le T.light T.down) Finset.univ (fun v _=>hV v)]
omit hp
include hT hi
lemma priority (hk:h≤e.J)(hv:u.slot ≤ M) (t:ℕ) : ∃ a≥(0:ℝ),∀ V:Sketch G,Living x M D V ζ→∀ b≥(0:ℝ), Harrier.Before Γ D x V i u.slot b→(∀ v:Badge H,∀ i,v.key V M i=0) → ∀ p:Word,OK S p→ ‖u.key (Transfer.mean e p s M t V) M i‖ ≤ a*b := by
    choose a ha H using fun z=> projected T hs x (D:=D) hT hi u z hk hv; refine ⟨_,mul_nonneg (pay_pos s t).le (sum_nonneg (s:=univ) fun i _=>ha i),fun V hv b hb ht hh p hp=> ?_⟩; rw [concert T hp hs x u hv t,norm_mul,Real.norm_of_nonneg (pay_pos s t).le,mul_assoc,Finset.sum_mul]; exact mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum fun i _=> H i V hv b hb ht hh p hp)) (pay_pos s t).le
end Transfer
end
end YM.Contacts.Harrier
