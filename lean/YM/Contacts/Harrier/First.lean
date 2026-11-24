import YM.Contacts.Harrier.Lottery
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
local notation "η" => bath ζ k (Dye G)
open Barrage Barrage.Reserve
variable {H:Labels.Frame G h}{V:Sketch G}{K:ℕ} (x:Dye G)
def gateNeed (e:Parcel G)(M K h k D:ℕ) :ℕ:= 256 +(Finset.sup (Iic (M+K)) (fun i=> Port.pleat G e.T e.J h i D k 1)) +2*(M+K+1)
def Banked (e:Parcel G)(M K h k D:ℕ):ℕ:= max e.Quota (max (gateNeed e M K h k D) (e.floorGoal 3 (M+3*K+5)))
lemma tickets (hF:enough (Banked e M K h k D) S): Demand S e M K:= hF.fall ((le_max_right ..).trans (le_max_right ..))
lemma free_paid (hF:enough (Banked e M K h k D) S): enough e.Quota S:= hF.fall (le_max_left ..)
variable (hF: enough (Banked e M K h k D) S) (hi:i≤K)(hk:h+1≤k)(hD:h+1≤D)(hP:h+3≤ e.J) (hr:r ≤ M+i)
include T hs hF hi hk hD hP hr
lemma gains (p:Word)(v:Site s.L)(hz:Living x M D V ζ)(hq:∀ v:Badge H,∀ i,v.key V M i=0)(hh:0≤ b)(ht:Enroll η D x V i r b) : Weight (motion e p s v i r V) D η x (Port.luxury 1 s.L h*b):= by
    let t:=M+4+i-r; have hv: Harrier.Issued η D x V i r b → True:=fun _=>trivial; let F:= sail V i r; have HE(u:Cards):V u i r= coil (V u) M t r:= (Pocket.current_coil M (V u) hr).symm; have he: Clear F (h+1-r):= by rw [show F=(fun v=>_) from (funext HE)]; exact core_void hz T.light le_rfl (fun v _ i=> hq v i)
    let L:= s.L; have h': Port.pleat G e.T e.J h r D k 1 +2*(M+K+1) ≤ s.L.val:= by
        let P:= hF.fall (z:=gateNeed e M K h k D) ((le_max_left ..).trans (le_max_right ..)); exact (Nat.add_le_add_right (le_trans (Finset.le_sup (f:=fun i=> Port.pleat G e.T e.J h i D k 1) (Finset.mem_Iic.mpr (by omega:r≤ M+K))) (Nat.le_add_left ..)) (2*(M+K+1))).trans (P s hs)
    let W:= Origin.bleed G (e.gas p s); have hN(l:List Axis)(ht:l.length≤h+1-r):= e.rod p s l (by omega); let U:=Port.arranged (G:=G) e.T e.J k r h D 1 zero_lt_one (by omega) (by omega); have hU: Port.pleat G e.T e.J h r D k 1= U.choose:= dif_pos ⟨zero_lt_one,by omega,by omega⟩
    have hc: (2*(ζ:ℝ)/ (s.L.val:ℝ))*( (r:ℝ)+1) ≤ ζ:= by
       have hv:2*((r:ℝ)+1)≤ s.L.val:= (by exact_mod_cast (show 2*(r+1) ≤ s.L.val from by omega)); rw [div_mul_eq_mul_div, div_le_iff₀ (side_pos _)]; nlinarith only [hv,NNReal.coe_nonneg ζ]
    have hg:(ζ:ℝ)*2≤e.T.α e.J:= by have hh:=T.warm; push_cast at hh; change _≤(e.reach:ℝ); linarith only [hh,NNReal.coe_nonneg ζ]; -- proof capture
    have hL : IsLinearMap ℝ F:= ⟨fun f g=> congr_fun (congr_fun (hz.lin.map_add f g) i) r, fun a f=> congr_fun (congr_fun (hz.lin.map_smul a f) i) r⟩; let G:= U.choose_spec L (hU ▸ le_trans (Nat.le_add_right ..) h') s.odd _ ζ ζ hg hc hN F hL he b hh x x (curb s v) (rent_lift v) (foot s v) (desk_tick s v) ht; intro a d hd h'; exact print_fee (G a d hd h')
lemma leading_pay : ∃ C≥(0:ℝ),∀ p:Word, OK S p→∀ V: Sketch G, Living x M D V ζ→(∀ v:Badge H, ∀ i,v.key V M i=0) →∀ b≥0,Harrier.Before Γ D x V i r b→∀ t≥0,Enroll η D x V i r t→ Weight (fid e p s h i r V) D η x (t/4+C*b):= by
   choose a ha H' using fun v:Site s.L=> keep_est (D:=D) (k:=k) T hs v x hr; let W:=Fintype.card (Site s.L); let y:= Port.luxury 1 s.L h; let C:=pay s h; let B:= ∑ v,a v; have hB:0≤B:=sum_nonneg fun v _=> ha v; have hC:0<C:= pay_pos s h; refine ⟨C*B,mul_nonneg hC.le hB, fun p hp V hP' hq b hb hx t ht hv=>?_⟩; let D'(v:Site s.L):= lead e p s v i r V; let Y(v:Site s.L):=y*t+a v*b;
   have hY (v:Site s.L) : Weight (D' v) D η x (Y v):= by rw [show D' v=_ from primogen T hp hs v hr hP']; exact w_sub (gains T hs x hF hi hk hD hP hr p v hP' hq ht hv) (H' v V b hb hx p)
   refine w_raise (w_scale (w_sum (U:=univ) (fun v _=> hY v)) C) ?_; unfold Y; rw [Finset.sum_add_distrib, Real.norm_of_nonneg hC.le, mul_add,←sum_mul (a:=b), sum_const,Finset.card_univ,nsmul_eq_mul]; refine add_le_add ?_ (le_of_eq (mul_assoc _ B b|>.symm ));
   unfold C y Port.luxury pay; let L:ℝ:=s.L.val; let s':= L^h; have hc:0<s':=(by unfold s' L; positivity); have he:0 < (W:ℝ):= (by unfold W; positivity); let U:=Real.exp (-Real.log L/2); change _≤ t/4; refine le_trans (b:=U*t) ?_ ((mul_le_mul_of_nonneg_right (floorGain (L:=s.L) (by exact (le_trans ((Nat.le_add_right 256 _).trans (Nat.le_add_right ..)) (((le_max_left (gateNeed e M K h k D) _).trans (le_max_right ..)).trans (hF s hs))))) ht).trans_eq (by ring)); apply le_of_eq; change s'/W*( (W:ℝ)*(U/(1*s')*t))=_; field_simp
-- Spent convenience: use bath at consumers
omit T hs hF hi hk hD hP hr
lemma spa_weight {F: Ribbon X j}{x:X} (h:0<ζ)(hp:Weight F D (terrain (2*ζ) X) x b) : Weight F D (bath ζ k X) x ((fit_spare (2*ζ) ζ k (by rw [two_mul]; exact lt_add_of_pos_right _ h)).choose*b):= fun p d hd H=> mul_assoc _ b d|>.symm ▸ spa_pond h (hp p d hd H)
-- ticket cost basic
include T
lemma position_spent {R:Word→Sketch G→Ribbon (Dye G) i}{H:Sketch G→ℝ→Prop} (h:Spent D x ζ M Υ S H R): Spent D x ζ M η S H R:= by
   obtain ⟨a,ha,h⟩:=h; let p:=(fit_spare (2*ζ) ζ k T.emit_lt).choose; refine ⟨_,mul_nonneg (zero_le_one.trans (fit_spare (2*ζ) ζ k T.emit_lt).choose_spec.1) ha,fun V hv b hb H=> ?_⟩; obtain ⟨h,H⟩:= h V hv b hb H; exact ⟨fun i hi=> (mul_assoc p a b).symm ▸ spa_weight T.light (h i hi), fun n m u h₀ he ht=> by change Weight _ _ _ _ (p*a*b*mileage u); simp only [mul_assoc p]; exact spa_weight T.light (H n m u h₀ he ht)⟩ -- p unfold
include hF hi hk hD hP hr hs
theorem charge_up : ∃ C≥(0:ℝ),∀ p:Word, OK S p→∀ V: Sketch G, Living x M D V ζ→(∀ v:Badge H, ∀ i,v.key V M i=0) →∀ b≥0,Harrier.Before Γ D x V i r b→∀ t≥0,Enroll η D x V i r t→ Enroll η D x (Transfer.mean e p s M h V) i r (t/4+C*b):= by
   obtain ⟨p,hp,P⟩:= position_spent (k:=k) T x (port_less T hs x (tickets hF) hi hr h); obtain ⟨c,hc,C⟩:= leading_pay (H:=H) T hs x hF hi hk hD hP hr; refine ⟨c+p, add_nonneg hc hp,fun i₀ hi V hX H b hb he t ht hh=>?_⟩; let f:=sail (Transfer.mean e i₀ s M h V) i r; let z:= fid e i₀ s h i r V; have hh':= (P V hX b hb he).1 i₀ hi; have h':= C i₀ hi V hX H b hb he t ht hh; change Weight f D _ x _; exact (sub_add_cancel f z) ▸ (w_raise (w_add hh' h') (le_of_eq (by ring))) -- maybe cast
end Transfer
end
end YM.Contacts.Harrier

