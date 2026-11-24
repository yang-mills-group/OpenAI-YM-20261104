import YM.Contacts.Harrier.Control
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
open Cartons Font Pierian Planned.PrimaryIntegral295 Place Carrier MultiNext.SignedSource Pattern Tensor Barrage Barrage.Reserve.Oasis Analysis PowerSeries
local notation "Γ" => terrain ζ (Dye G)
local notation "η" => bath ζ k (Dye G)
variable (x:Dye G) (A: Ink G h M) (v:Badge A.prism) {K:ℕ} {P F:Sketch G} (hT:Demand S e M K)(hi:i ≤ K)(hh:h ≤ D)(hk:h≤e.J)
lemma before_sub {P V: Sketch G}{Q:Pulse.Range (Node (Dye G))}(h:Harrier.Before Q D x P i r b)(he:Harrier.Before Q D x V i r c): Harrier.Before Q D x (P-V) i r (b+c):= fun i j ht=> w_sub (h i j ht) (he i j ht)
lemma all_clear (F:Sketch G)(hp:Living x M D F ζ)(hq:h≤D)(ht:0<ζ)(u:Badge A.prism): u.key (A.left F) M i=0:= by have he:= A.left_zero hp ht hq; change u.key (A.left F) M _=_; exact (PowerSeries.coeff_mk i _).symm.trans ((congr_arg (PowerSeries.coeff i) (congr_fun he u)).trans (map_zero _))
include T hT hi hh hs
-- chart mean linear for bounty.CP7 builds. 
omit hi hT hh in
lemma means_add (t:ℕ) (hp:OK S p)(h:Living x M D F ζ)(hx:Living x M D P ζ):Transfer.mean e p s M t (F+P)=Transfer.mean e p s M t F+Transfer.mean e p s M t P:= by simpa only [one_smul] using mean_tilt T hp hs t 1 h hx
include hk
lemma fed : ∃ t≥(0:ℝ),∀ p,OK S p→∀ V:Sketch G,Living x M D V ζ→∀ b≥0,Harrier.Before Γ D x V i v.slot b→(∀ u:Badge A.prism,u.slot=v.slot→ u.key V M i=0)→ ‖v.key (Transfer.mean e p s M h V) M i‖≤ t*b:= by
   let k:= v.slot; obtain ⟨a,ha,A'⟩:= mint_slot A x (k:=0) hh T.light i k; obtain ⟨b,hb,B⟩:= mint_before A x (k:=0) hh T.light i k; obtain ⟨c,hc,C⟩:= priority T hs x (D:=D) hT hi v hk (second A v) h; obtain ⟨d,hd,H⟩:= key_bill T hs x (D:=D) hT hi h v (second A v); let w :ℝ:= max b a; have hw:0≤w:=hb.trans (le_max_left ..); refine ⟨_,add_nonneg (mul_nonneg hc (add_nonneg zero_le_one hw)) (mul_nonneg hd hw), fun p hp V hv f hf he hx=>?_⟩; let Q:= A.priceWord V; let Y:= A.draw Q; let k:=v.slot; let Z:= w*f; have hz:0≤Z:= mul_nonneg hw hf; let P:=Harrier.Before Γ D x V; let X:= A.left V; let U:= Transfer.mean e p s M h; have hv': Living x M D Y ζ := A.draw_health Q hh; have he': Harrier.Before Γ D x Y i k Z:= ((B V hv _ hf he).lower).mon (mul_le_mul_of_nonneg_right (le_max_left ..) hf); have hX:Issued Γ D x Y i v.slot Z:= ⟨he',w_upped (A' _ _ hf hv he (fun p hp=> by rw [hx p hp,norm_zero]; exact hf)) (mul_le_mul_of_nonneg_right (le_max_right ..) hf) (fun _=>bath_terrace _)⟩; let hw':= hv.sub hv';
   have hx': v.key (U V) M i = v.key (U X) M i+v.key (U Y) M i := by rw [show U V= _ from (show _ = U X + U Y from (Eq.trans (congr_arg U (sub_add_cancel V Y).symm) (means_add T hs x h hp hw' hv')))]; exact v.key_add (cenacle T hp hs hw' h) (lt_of_lt_of_le T.light T.down) (cenacle T hp hs hv' h)
   change ‖v.key (U V) M i‖≤_; rw [hx']; refine (norm_add_le ..).trans ((add_le_add (C X hw' _ (add_nonneg hf hz) (before_sub x he he') (fun u i=> all_clear x A V hv hh T.light u) p hp) ((H Y hv' _ hz hX).1 _ hp)).trans_eq ?_ ); unfold Z; ring
-- finite current correction.Coeff only in this rank.
omit hk hi hT hs T hh
abbrev points (k:ℕ): Finset (Badge A.prism) := Finset.univ.filter (fun w=>w.slot=k)
def offset (F:Sketch G) (i k:ℕ) : Sketch G := ∑ w∈points A k, w.key F M i • surge (A.purse w) i
def pushMatrix (e:Parcel G)(p:Word)(s:Parcel.Step)(A:Ink G h M) (f:Badge A.prism→ℝ)(v:Badge A.prism) := ∑ w∈points A v.slot, f w*graph e p s A v w
def discount (e:Parcel G)(p:Word)(s:Parcel.Step)(A:Ink G h M) (F:Sketch G) (i:ℕ)(v:Badge A.prism):=v.key (Transfer.mean e p s M h F) M i-pushMatrix e p s A (fun v=>v.key F M i) v
lemma ko (F: Sketch G)(h:h ≤ D)(i k:ℕ): Living x M D (offset A F i k) ζ:= Living.sum _ fun v _=> ((A.life v h).surgeM _).scale _
include x
lemma slotOff (F:Sketch G)(he:v.slot=k)(ht:h≤ D)(hz:0<ζ): v.key (offset A F i k) M i=v.key F M i:= by
   subst k; unfold offset; rw [v.key_many (x:=x) (D:=D) hz (points ..) (?_:∀ j∈points A v.slot,_),Finset.sum_eq_single v]; rotate_left; · intro j hj he; rw [v.key_scale ((A.life j (x:=x) ht).surgeM _) hz]; unfold Badge.key surge; rw [fill_shift _ ((A.life j (x:=x) ht).lineage v.phi) hz,if_pos le_rfl,Nat.sub_self,show fill ..=_ from A.character x j v 0]; simp [he] -- arg metavariable
   · simp [points]
   · exact fun v _=> ((A.life v (x:=x) ht).surgeM _).scale _
   rw [v.key_scale ((A.life v (x:=x) ht).surgeM _) hz]; unfold Badge.key surge; rw [fill_shift _ ((A.life v (x:=x) ht).lineage v.phi) hz,if_pos le_rfl,Nat.sub_self,show fill ..=_ from A.character x v v 0]; simp
lemma off_before (F:Sketch G)(b:ℝ)(hb:0≤b) : Harrier.Before Γ D x (offset A F i r) i r b:= by
    intro j n hj; rw [Enroll, Harrier.Transfer.offset,sum_sail]; refine w_raise (w_sum (b:=fun _=>0) (U:=points A r) (fun p hp=> ?_)) ?_; swap; · exact le_trans (b:=0) (by exact le_of_eq (by simp : (∑ z∈points A r, (fun _=> (0:ℝ)) z)=0)) hb -- placeholder f implicit
    let u:=p.key F M i; have he:‖u‖ * (0:ℝ)=0:= mul_zero _; exact he ▸ w_scale ((expenses (ζ:=ζ) x A p i (D:=D) (show p.slot ≤ r from (mem_filter.mp hp).2.le)) j n hj) u -- Z must terrain
include T hs hp
lemma means_zero (j M:ℕ) : Transfer.mean e p s M j 0=0:= by let R:= Transfer.mean e p s M j; let V:=Living.zero (ζ:=ζ) x M 0; change R 0=0; apply add_left_cancel (a:=R 0); simpa only [add_zero] using (means_add T hs x j hp V V).symm
lemma mean_scale (t:ℝ)(j:ℕ)(h:Living x M D F ζ): Transfer.mean e p s M j (t • F)= t • Transfer.mean e p s M j F:= by simpa only [add_zero,means_zero T hp hs x] using mean_tilt T hp hs j t h (Living.zero (ζ:=ζ) x M D)
lemma whole_sum {F:ι→Sketch G}(z:Finset ι)(j M:ℕ)(H:∀ i∈z,Living x M D (F i) ζ) : Transfer.mean e p s M j (∑ i∈z,F i)=∑ i∈z, Transfer.mean e p s M j (F i):= by induction z using Finset.induction with|empty=>simp only [sum_empty,means_zero T hp hs x]|insert i v hi ih=> have h (i) (he:i∈v):=H i (mem_insert_of_mem he); rw [sum_insert hi, sum_insert hi, means_add T hs x j hp (H i (mem_insert_self ..)) (Living.sum v h),ih h]
include hi hT hh
lemma leap (F:Sketch G): v.key (Transfer.mean e p s M h (offset A F i v.slot)) M i=pushMatrix e p s A (fun w=>w.key F M i) v:= by
    let W:= points A v.slot; let H(u:Badge A.prism) := (A.life (x:=x) (ζ:=ζ) u hh).surgeM i; let a(w:Badge A.prism):= w.key F M i; let Q(u:Badge A.prism):= Transfer.mean e p s M h (surge (A.purse u) i); unfold Harrier.Transfer.offset; rw [whole_sum T hp hs x W h _ (fun i _=> (H i).scale _), v.key_many (lt_of_lt_of_le T.light T.down) W (fun i _=> cenacle T hp hs ((H i).scale _) h)]; refine Finset.sum_congr rfl fun u hu=>?_ ; rw [mean_scale T hp hs x _ h (H u),v.key_scale (cenacle T hp hs (H u) h) (lt_of_lt_of_le T.light T.down), grafting T hp hs x A v u hT hh (mem_filter.mp hu).2.symm hi]
omit hp
include hk
lemma depression : ∃ C≥(0:ℝ),∀ p,OK S p→∀ V:Sketch G,Living x M D V ζ→∀ b≥(0:ℝ), Harrier.Before Γ D x V i v.slot b→ ‖discount e p s A V i v‖≤ C*b:= by
   obtain ⟨a,ha,H⟩:= fed T hs x A v hT hi hh hk; refine ⟨a,ha,fun p hp V hV b hb hx=>?_⟩; let W:=offset A V i v.slot; have hhV:=ko x A V (ζ:=ζ) hh i v.slot; let Z:=V-W; let hZ:= hV.sub hhV; let U:=Transfer.mean e p s M h; have he: Harrier.Before Γ D x Z i v.slot b:= add_zero b ▸ before_sub x hx (off_before x A _ _ le_rfl); have hv : Z+W=V:= sub_add_cancel ..; have hs'(u:Badge A.prism)(h:u.slot=v.slot): u.key Z M i=0:= by
      have he:=u.key_add (V:=Z) (P:=W) hZ T.light hhV (i:=i); have ht: u.key W M i=u.key V M i:=slotOff x A u _ h hh T.light; rw [hv,ht] at he; linarith only [he]
   change ‖v.key (U V) M i-_‖≤_; rw [← leap T hp hs x A v hT hi hh V, show U V=U Z + U W from (congr_arg U hv.symm).trans (means_add T hs x h hp hZ hhV), v.key_add (V:=U Z) (P:=U W) (cenacle T hp hs hZ h) (lt_of_lt_of_le T.light T.down) (cenacle T hp hs hhV h)]; change ‖(_+v.key (U W) M i)-v.key (U W) M i‖≤_; rw [add_sub_cancel_right]; exact H p hp Z hZ b hb he hs'
omit hk hT hh
include hh
lemma foothold (hQ:enough (Banked e M K h k D) S)(hP:h+3≤ e.J)(h':h+1≤D)(hd:h+1≤k)(hr:r≤M+i) : ∃ C≥(0:ℝ),∀ p,OK S p→∀ V: Sketch G,Living x M D V ζ→∀ b≥(0:ℝ),Harrier.Before Γ D x V i r b→(∀ v:Badge A.prism, v.slot=r→ ‖v.key V M i‖ ≤ b) →∀ t≥(0:ℝ), Enroll η D x V i r t→ Enroll η D x (Transfer.mean e p s M h V) i r (t/4+C*b):= by
   obtain ⟨a,ha,A₁⟩:=mint_slot (k:=k) A x hh T.light i r; obtain ⟨c,hc,H⟩:=mint_before (k:=k) A x hh T.light i r; obtain ⟨u,hu,U⟩:=position_spent (k:=k) T x (port_health T hs x (D:=D) (tickets hQ) hi hr h); obtain ⟨d,hd',D'⟩:=Transfer.charge_up (H:=A.prism) T hs x hQ hi hd h' hP hr; let w:=max a c; have hw:0≤w:= hc.trans (le_max_right ..); refine ⟨w/4+d*(1+w)+u*w,add_nonneg (add_nonneg (by positivity) (by positivity)) (mul_nonneg hu hw),fun p hp V hV b hb he hk t ht hh' =>?_⟩; let Z:=A.draw (A.priceWord V); let q:= w*b; have hM:0≤q:=mul_nonneg hw hb; have hZ:Living x M D Z ζ:= A.draw_health _ hh; have hZ':= hV.sub hZ; let Y:= Transfer.mean e p s M h; let X:=A.left V; have hx: Harrier.Before Γ D x Z i r q:= ((H _ hV _ hb he).lower).mon (mul_le_mul_of_nonneg_right (le_max_right ..) hb); have hz : Enroll η D x Z i r q:= w_raise (A₁ _ _ hb hV he hk) (mul_le_mul_of_nonneg_right (le_max_left ..) hb); have hl : Issued Γ D x Z i r q:=⟨hx,w_upped hz le_rfl fun _=> bath_terrace _⟩; let H₂:=D' p hp X hZ' (fun u i=> all_clear x A V hV hh T.light u) (b+q) (add_nonneg hb hM) (before_sub x he hx) (t+q) (add_nonneg ht hM) (w_sub hh' hz); have H₁:= (U Z hZ _ hM hl).1 p hp; rw [show Transfer.mean e p s M h V= Y X +Y Z from (congr_arg Y (sub_add_cancel V Z).symm).trans (means_add T hs x h hp hZ' hZ)]; exact w_raise (w_add (show Enroll η D x (Y X) _ _ _ from H₂) H₁) (le_of_eq (by unfold q; ring))
end Transfer
end
end YM.Contacts.Harrier
