import YM.Contacts.Harrier.Paint
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
open Cartons Font Pierian Planned.PrimaryIntegral295 Place Carrier MultiNext.SignedSource Pattern Tensor Barrage.Reserve.Oasis Analysis
variable (x:Dye G) (A:Ink G h M)(u v:Badge A.prism){K:ℕ}(hT:Demand S e M K)
local notation "Γ" => terrain ζ (Dye G)
lemma second : v.slot ≤ M:= (Film.second_fits A.prism _).trans A.ready
lemma expenses (n:ℕ)(he:v.slot ≤ k) : Harrier.Before Γ D x (surge (A.purse v) n) n k 0:= by
   intro i j hi; have hf:sail (surge (A.purse v) n) i j=0:= by
      funext r; rcases hi with hx|⟨hc,hx⟩; · unfold sail surge shiftA; rw [if_neg (by omega)]; rfl
      subst i; unfold sail surge shiftA; rw [if_pos le_rfl,Nat.sub_self]; exact (show _ • A.mask v.loc 0 j=0 from Eq.trans (congr_arg (v.read r • ·) ((A.paint v.loc).rank _ _ (show j ≠ (A.prism.grades v.loc).2+0 from fun h=>by have hn:j=v.slot:=(by rw [Nat.add_zero] at h; exact h); omega))) (smul_zero _))
   unfold Enroll; rw [hf]; apply w_zero
lemma halt : surge (A.purse v) 0=A.purse v:= by funext p i; simp [surge,shiftA]
lemma stop (he:v.slot ≤ k): Harrier.Before Γ D x (A.purse v) 0 k 0:= (halt A v) ▸ expenses x A v 0 he -- method .? namespace Transfer; adjust
lemma mark_cost (a:A.prism.Index)(c:ℝ): Based ζ x M (c • A.mask a):= Based.smul (show Based ζ x M (A.mask a) from ⟨(A.paint a).mount,(A.paint a).chip _ _⟩) _
include x
lemma pole_digit (c:ℝ)(he:0<ζ) (w:A.prism.Index)(i:ℕ):fill A.prism M (c • A.mask v.loc) i w=c*(if i=0∧v.loc=w then 1 else 0):= by
   let h:Based ζ x M (A.mask v.loc):= ⟨(A.paint _).mount,(A.paint _).chip x ζ⟩; simpa only [fill_null A.prism x,print_basis (A.paint _) (second A v) A.pop A.sound A.color w i,add_zero] using fill_linear A.prism h (Based.zero (v:=x)) he c i w
lemma purity (hq:u.pull ≤ v.pull)(A':ℝ)(ht:0<ζ)(k:ℕ)(hk:k ≤ M)(j:ℕ)(hj:j < u.pull):Remains j ((A' • A.mask v.loc) 0 k):= by
    let U:bore G:= A' • A.mask v.loc; let K:= coil U M (M+4+0-k); have hj':j < v.pull:= lt_of_lt_of_le hj hq; obtain ⟨hx,R,H⟩:= mark_cost x A (ζ:=ζ) v.loc A'; have hu:Felt K:= (coil_tags hx H ht _).toFelt
    change Remains j (U 0 k); rw [←Pocket.current_coil M U hk]; apply remains_story A.prism (coil_tags hx H ht _) (hj'.le.trans (A.prism.bound v.loc)); intro w hw; have he: v.loc≠w:= by intro h; rw [←h] at hw; exact (not_lt.mpr hw) hj'
    rw [fueled hx x ht H]; split; swap; · rfl
    rw [pole_digit x A v _ ht]; simp [he]
include T hp hs hT
lemma delivery (z:Site s.L)(H':h≤ e.J)(hD:h≤ D)(hb:v.num ≤ u.num)(ht:u.slot=v.slot)(hq:u.win ≤ v.win) : u.key (pass e p s M z (A.purse v)) M 0= unitStep s.L ^ u.pull * v.read (desk s z u.phi) * (if v.loc=u.loc then 1 else 0) := by
   have ha :u.pull ≤ v.pull:= by unfold Badge.win at hq; omega
   have hk:= second A u; let F:=A.purse v; let Z:=desk s z u.phi; let t:=unitStep s.L ^ u.pull; let c:= v.read Z; let Y:=F Z; have h: Living x M D F ζ := A.life v hD; obtain ⟨H,Q,hQ⟩:= h.lineage Z; have Hx : Harrier.Before Γ D x F 0 u.slot 0:= stop x A v (Eq.le ht.symm); rw [vital T hp hs _ hT (Nat.zero_le K) hk h z Hx]; -- order check
   rw [lamps T hp hs u z _ (hQ.lands 0 u.slot) (H.incarnate.sym 0 u.slot) ((A.prism.bound u.loc).trans H') (purity x A u v ha c T.light u.slot hk)]; change (cursor _ u.pull u.slot (t • ((c • A.mask v.loc) 0 u.slot)) u.loc).re=t*c*_ ; rw [show t • ((c • A.mask v.loc) 0 u.slot)= (((t*c) • A.mask v.loc) 0 u.slot) from smul_smul ..]; -- shape
   rw [←value_axis u.loc (mark_cost (ζ:=ζ) x A _ (t*c)) T.light hk,pole_digit x A v _ T.light]; simp [c,t]
omit T hp hs hT x
lemma pocket_core (he:v.num=u.num)(z:E4)(t:ℝ): v.read (Cards.onRoute z t u.phi)=t^u.num * if u.pocket=v.pocket then 1 else 0 := by -- generalize z:E4
   rcases v with ⟨⟨a,⟨m,hm⟩,x⟩,hv⟩; rcases u with ⟨⟨b,⟨n,hn⟩,y⟩,hu⟩; change m=n at he; subst m; let u: Address h:=⟨⟨n,hn⟩,y⟩; change Font.pay x (Cards.onRoute z t (Font.plait y)) = t^n * if u=(⟨⟨n,hn⟩,x⟩: Address h) then 1 else 0; rw [Font.pay_center]; simp [u,eq_comm]
include T hp hs hT x
lemma paying (z:Site s.L)(H':h≤ e.J)(hD:h≤ D)(ht:u.slot=v.slot)(hq:u.win≤v.win) : u.key (pass e p s M z (A.purse v)) M 0= if u=v then unitStep s.L ^ v.win else 0:= by
   let a:=unitStep s.L; by_cases hv:u.num<v.num
   · have hh:u ≠ v:= by intro he; rw [he] at hv; omega
     rw [if_neg hh]; let V:=A.purse v; let Y:=desk s z u.phi; have hy: v.read Y=0:= Font.pay_above hv (foot s z) _; have hw:V Y=0:= by change v.read Y • A.mask v.loc=0; rw [hy,zero_smul]
     have hk:= second A u; rw [vital T hp hs u hT (Nat.zero_le K) hk (A.life v hD) z (stop (ζ:=ζ) x A v ht.symm.le)]; change (cursor _ _ _ (shade e p s z (V Y 0 u.slot)) _).re=0; rw [hw,Pi.zero_apply,Pi.zero_apply]; rw [show shade _ _ _ _ (0:Field (Fin u.slot) (Node (Dye G)))=0 from (show shade e p s z (0:Field (Fin u.slot) (Node (Dye G)))=0 from by unfold shade Trace.wreath; apply Eq.trans _ print_zero; exact congr_arg printRun (funext fun i=> by simp [allAt]))]; exact (value_axis u.loc (Based.zero (v:=x) (ζ:=ζ) (M:=M)) T.light hk).symm.trans (fill_null A.prism x ..)
   rw [delivery T hp hs x A u v hT z H' hD (by omega) ht hq]; split_ifs with ht hx hx -- nested parentheses
   · subst u; rw [show v.read (desk s z v.phi)=a^v.num * (if v.pocket=v.pocket then 1 else 0) from pocket_core A v v rfl _ _]; change a^_*_*_=a^_; simp [Badge.win,pow_add]
   · have he:u.pocket≠v.pocket:=fun h=>hx (Subtype.ext (Prod.ext ht.symm h)); have hp:v.num=u.num:= by have hh:v.pull=u.pull:= congr_arg (fun i=> (A.prism.grades i).1) ht; unfold Badge.win at hq; omega
     rw [show v.read (desk s z u.phi)=a^u.num* (if u.pocket=v.pocket then 1 else 0) from pocket_core A u v hp _ _, if_neg he,mul_zero,mul_zero,zero_mul]
   · subst v; exact (ht rfl).elim
   exact mul_zero _
-- matrix indexed [output, input]; at same slot only asked here. `epoch` authority.G factors in formulas, spaces not yet restricted to diagonally renormed quotient or unit.
variable (e p s)
omit T hp hs hT x in
def graph : ℝ:= u.key (Transfer.mean e p s M h (A.purse v)) M 0
variable {e p s}
lemma triangle (he:h≤ e.J)(hD:h≤D)(ht:u.slot=v.slot)(hv:u.win ≤ v.win) : graph e p s A u v=if u=v then (s.L.val:ℝ)^(h-v.win) else 0:= by
    unfold graph; rw [concert T hp hs x u (A.life v hD)]; simp_rw [paying T hp hs x A u v hT _ he hD ht hv]; let Z:= (s.L.val:ℝ); by_cases hp:u=v; swap; · simp [hp]
    subst u; rw [if_pos rfl]; simp only [ Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; let W:ℝ:= Fintype.card (Site s.L); have hZ :0<Z:= side_pos _; have hW :0<W:= (by unfold W; positivity); let t:=v.win_le; change Z^h/W*(W*Z⁻¹^v.win)=Z^(h-v.win); simp only [inv_pow]; field_simp; rw [mul_comm (Z^v.win),←pow_add Z (h-v.win) v.win, Nat.sub_add_cancel t]
-- authority persists also with explicit surge (degrees)
lemma settled (z:Site s.L)(hD:h ≤ D)(ht:u.slot=v.slot)(hq:i≤ K): u.key (pass e p s M z (surge (A.purse v) i)) M i=u.key (pass e p s M z (A.purse v)) M 0:= by rw [vital T hp hs _ hT hq (second A u) ((A.life v (x:=x) hD).surgeM i) z (expenses x A v i ht.symm.le), vital T hp hs _ hT (Nat.zero_le _) (second A u) (A.life v hD) z (stop x A v ht.symm.le)]; congr 4; simp [surge, shiftA]
theorem grafting (hD:h≤D)(ht:u.slot=v.slot)(hi:i≤K): u.key (Transfer.mean e p s M h (surge (A.purse v) i)) M i=graph e p s A u v:= by unfold graph; rw [concert T hp hs x u ((A.life v hD).surgeM i),concert T hp hs x u (A.life v hD)]; simp_rw [settled T hp hs x A u v hT _ hD ht hi]
end Transfer
end
end YM.Contacts.Harrier
