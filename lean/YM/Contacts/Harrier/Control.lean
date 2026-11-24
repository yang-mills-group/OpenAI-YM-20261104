import YM.Contacts.Harrier.Prize
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
open Cartons Font Pierian Planned.PrimaryIntegral295 Place Carrier MultiNext.SignedSource Pattern Tensor Barrage Barrage.Reserve.Oasis Analysis
local notation "Γ" => terrain ζ (Dye G)
local notation "Υ" => terrain (2*ζ) (Dye G)
section beforeShot
variable {H:Labels.Frame G h} {P:Sketch G} (x:Dye G){K:ℕ}(hT:Demand S e M K)(hi:i≤ K)
def PriceTx (t:ℕ)(b:ℝ): Prop := ∀ F:Sketch G,Living x M D F ζ→∀ u≥(0:ℝ),Harrier.Before Γ D x F i r u→ (∀ p,OK S p→Harrier.Before Υ D x (Transfer.mean e p s M t F) i r (b*u)) ∧ ∀ p q v,OK S p→OK S q→OK S v→ Harrier.Before Υ D x (Transfer.mean e (v++p) s M t F-Transfer.mean e (v++q) s M t F) i r (b*u*mileage v)
lemma clean_stop {σ:ℝ≥0} {Q:Pulse.Range (Node (Dye G))} (h:Living x M D P σ)(he:M+i<r)(t:ℝ)(ht:0≤t): Enroll Q D x P i r t:= by rw [Enroll,show sail P i r=0 from funext fun j=>(h.lineage j).1.incarnate.thin i r he]; exact w_raise w_zero ht
include T hs hT hi
lemma prior_consumed (t:ℕ):∃ b≥0, PriceTx (i:=i) (r:=r) (D:=D) (ζ:=ζ) (e:=e) (M:=M) (s:=s) (S:=S) x t b:= by
   let R (z:ℕ×ℕ) (a:ℝ):Prop:=∀ F:Sketch G,Living x M D F ζ→∀ b≥(0:ℝ),Harrier.Before Γ D x F i r b→Past i r z.1 z.2 → (∀ p, OK S p→ Enroll Υ D x (Transfer.mean e p s M t F) z.1 z.2 (a*b)) ∧ ∀ p q u,OK S p→OK S q→OK S u→Enroll Υ D x (Transfer.mean e (u++p) s M t F-Transfer.mean e (u++q) s M t F) z.1 z.2 (a*b*mileage u)
   let W:= (Finset.Iic i ×ˢ Finset.Iic (M+i)).filter (fun x:ℕ×ℕ=> x.2≤ M+x.1); have hu (z:ℕ×ℕ)(hg:z∈W) : ∃ a≥(0:ℝ),R z a:= by
     obtain ⟨hl,hz⟩:= mem_filter.mp hg; obtain ⟨p,hp,Q⟩:=port_health (D:=D) T hs x hT ((Finset.mem_Iic.mp (mem_product.mp hl).1).trans hi) hz t; exact ⟨p,hp,fun F hF b hb h hk=> Q _ hF _ hb (h.earlier hk)⟩
   obtain ⟨p,hp,Q⟩:= Parcel.collective W (P:=R) (fun _ _ _ hc H F hF b hb h hk=> ⟨fun i hi=> w_raise ((H F hF b hb h hk).1 i hi) (mul_le_mul_of_nonneg_right hc hb), fun i j w hi hj hw=> w_raise ((H F hF b hb h hk).2 i j w hi hj hw) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hb) (mileage_pos _).le)⟩) hu; have hV(z:ℕ×ℕ)(he:Past i r z.1 z.2)(hg:z∉W): M+z.1<z.2 :=by by_contra! ht; apply hg; unfold Past at he; rw [mem_filter,mem_product,Finset.mem_Iic,Finset.mem_Iic]; omega
   refine ⟨p,hp,fun F hF b hb h=>?_⟩; let f i (hi:OK S i):=cenacle T hi hs hF t; constructor; · intro i hi j k he; by_cases hx:(j,k)∈W; exact (Q (j,k) hx F hF _ hb h he).1 i hi; exact clean_stop _ (f i hi) (hV (j,k) he hx) _ (mul_nonneg hp hb)
   intro i j u hi hj hu z w H; by_cases ht:(z,w)∈W; exact (Q (z,w) ht F hF _ hb h H).2 i j u hi hj hu; exact clean_stop _ ((f _ (hu.append hi)).sub (f _ (hu.append hj))) (hV (z,w) H ht) _ (mul_nonneg (mul_nonneg hp hb) (mileage_pos _).le)
lemma whole_bill (t:ℕ)(hr:r≤ M+i): ∃ a≥0,∀ F:Sketch G,Living x M D F ζ→∀ b≥(0:ℝ), Issued Γ D x F i r b→ (∀ p, OK S p→ Issued Υ D x (Transfer.mean e p s M t F) i r (a*b)) ∧ ∀ p q u,OK S p→OK S q→OK S u→ Issued Υ D x (Transfer.mean e (u++p) s M t F-Transfer.mean e (u++q) s M t F) i r (a*b*mileage u):= by
   obtain ⟨a,ha,P⟩:=prior_consumed (r:=r) (D:=D) T hs x hT hi t; obtain ⟨c,hc,C⟩:= port_health (D:=D) T hs x hT hi hr t; let A:= a+c; have hx : a≤A:= le_add_of_nonneg_right hc; have hy:c≤A:= le_add_of_nonneg_left ha; refine ⟨A,ha.trans hx,fun F h b hb he=>?_⟩; obtain ⟨p,H⟩:=P F h b hb he.1; obtain ⟨q,Y⟩:= C F h b hb he; let hx':=mul_le_mul_of_nonneg_right hx hb; let hy':=mul_le_mul_of_nonneg_right hy hb; exact ⟨fun i hi=> ⟨(p i hi).mon hx',w_raise (q i hi) hy'⟩,fun i j u hi hj hu=> ⟨(H i j u hi hj hu).mon (mul_le_mul_of_nonneg_right hx' (mileage_pos ..).le),w_raise (Y i j u hi hj hu) (mul_le_mul_of_nonneg_right hy' (mileage_pos ..).le)⟩⟩
theorem key_bill (t:ℕ)(v:Badge H)(hk:v.slot≤ M): ∃ a≥(0:ℝ),∀ F:Sketch G,Living x M D F ζ→∀ b≥(0:ℝ),Issued Γ D x F i v.slot b→ (∀ p, OK S p→ ‖v.key (Transfer.mean e p s M t F) M i‖≤ a*b) ∧ ∀ p q u, OK S p→OK S q→OK S u→ ‖v.key (Transfer.mean e (u++p) s M t F) M i-v.key (Transfer.mean e (u++q) s M t F) M i‖ ≤ a*b*mileage u:= by
   let η:=(lt_of_lt_of_le T.light T.down); obtain ⟨c,hc,Q⟩:=whole_bill (D:=D) T hs x hT hi t (hk.trans (Nat.le_add_right ..)); obtain ⟨a,ha,A⟩:=Pocket.key_exp i v.slot (D:=D) v η rfl hk; refine ⟨a*c,mul_nonneg ha hc,fun F hF b hb h=> ?_⟩; obtain ⟨Q,U⟩:= Q F hF b hb h; refine ⟨fun p h=> (A x _ (cenacle T h hs hF t) _ (mul_nonneg hc hb) (Q p h)).trans_eq (mul_assoc ..).symm,fun p q u hi hj hw=>?_⟩; let Z p:= Transfer.mean e (u++p) s M t F; let Y p (hp:OK S p):= cenacle T (hw.append hp) hs hF t; let W:= Z p-Z q; have hv:=(Y p hi).sub (Y q hj); have ht:= v.key_add (V:=W) (P:=Z q) (i:=i) hv η (Y q hj); rw [show W+Z q=Z p from sub_add_cancel ..] at ht; change ‖v.key (Z p) M i-v.key (Z q) M i‖≤ _; rw [ht,add_sub_cancel_right]; exact (A x W hv _ (mul_nonneg (mul_nonneg hc hb) (mileage_pos _).le) (U p q u hi hj hw)).trans_eq (by ring)
end beforeShot
end Transfer
end
end YM.Contacts.Harrier
