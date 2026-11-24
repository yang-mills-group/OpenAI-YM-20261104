import YM.Contacts.Harrier.Birth
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
open Cartons Font Pierian Planned.PrimaryIntegral295 Place Carrier MultiNext.SignedSource Pattern Tensor Barrage Barrage.Reserve.Oasis Analysis PowerSeries Transfer
local notation "Γ" => terrain ζ (Dye G)
local notation "η" => bath ζ k (Dye G)
variable (A: Ink G h M)(x:Dye G) {V P: Sketch G}{Z:Pulse.Range (Node (Dye G))}
-- costs before applying operators
lemma below_dues (ht:h≤ D) (hp:0<ζ)(j i l): ∃ b≥(0:ℝ),∀ w:Badge A.prism, Enroll η D x (surge (A.purse w) j) i l b:= by
   obtain ⟨b,hb,hB⟩:= Parcel.collective (P:=fun w b=>Enroll η D x (surge (A.purse w) j) i l b) univ (fun _ a b he h=> w_raise h he) (fun w _=> by obtain ⟨b,hb,B⟩:= ((A.life w ht).surgeM j|>.budget (y:=x) (ζ:=2*ζ) i l); exact ⟨_,mul_nonneg (zero_le_one.trans ((fit_spare (2*ζ) ζ k (by rw [two_mul]; exact lt_add_of_pos_right _ hp)).choose_spec.1)) hb, spa_weight hp B⟩);
   exact ⟨b,hb,fun i=> hB i (mem_univ _)⟩
lemma sail_break (u:Badge A.prism)(v:ℕ)(w:RodP) : sail (whip w (A.purse u)) i v=∑ j∈Finset.range (i+1), pin w j • sail (surge (A.purse u) j) i v:= by funext φ; simp [sail,surge,whip,fresh]
lemma guardPocket (hq:h≤D)(hp:0<ζ)(i j:ℕ)(v: Badge A.prism)(hr:j ≤ i): ∃ C≥(0:ℝ),∀ (F:Sketch G)(d:ℝ),0≤d→Living x M D F ζ → Harrier.Before Γ D x F i r d → (∀ v:Badge A.prism,v.slot=r→ ‖v.key F M i‖≤d)→ Weight (pin (A.priceWord F v) j • sail (surge (A.purse v) j) i r) D η x (C*d):= by
   obtain ⟨b,hb,B⟩:=below_dues (k:=k) A x hq hp j i r; obtain ⟨c,hc,H⟩:= Pocket.key_exp j v.slot (D:=D) v hp rfl (second A v); let C:=max 1 c; refine ⟨C*b, mul_nonneg (zero_le_one.trans (le_max_left ..)) hb, fun F d hd H' he hv=>?_⟩; rw [pin,Ink.priceWord,coeff_mk]; by_cases ha:j=i ∧ v.slot ≠ r
   · suffices hh:sail (surge (A.purse v) j) i r=0 by rw [hh,smul_zero]; exact w_raise w_zero (mul_nonneg (mul_nonneg (zero_le_one.trans (le_max_left 1 c)) hb) hd);
     funext φ; unfold sail surge shiftA; rw [ha.1, if_pos le_rfl,Nat.sub_self]; have hp : r≠ (A.prism.grades v.loc).2+0:= (by change r≠v.slot+0; omega); exact (show v.read φ • A.mask v.loc 0 r=0 from (by rw [(A.paint _).rank _ _ hp,smul_zero]))
   have hu:‖v.key F M j‖ ≤ C*d := by
       by_cases hf:j=i; · rw [hf]; exact (hv v (by tauto)).trans (le_mul_of_one_le_left hd (le_max_left ..))
       exact (H x F H' d hd (he.earlier (Or.inl (by omega)))).trans (mul_le_mul_of_nonneg_right (le_max_right ..) hd)
   exact w_raise (w_scale (B v) (v.key F M j)) ((mul_le_mul_of_nonneg_right hu hb).trans_eq (by ring))
-- all grade labels; arbitrary sequence of relative references p.Authority. Earlier graph row charges only needed for that rank.
lemma mint_slot (hq:h≤D)(hp:0<ζ)(i:ℕ)(r:ℕ): ∃ C≥(0:ℝ),∀ (F:Sketch G)(d:ℝ),0≤d→Living x M D F ζ → Harrier.Before Γ D x F i r d → (∀ v:Badge A.prism,v.slot=r→‖v.key F M i‖≤d)→ Enroll η D x (A.draw (A.priceWord F)) i r (C*d):= by
   choose! a ha hA using fun (v:Badge A.prism)(j:ℕ)(he:j ≤ i) => guardPocket (k:=k) (r:=r) A x hq hp i j v he; let t:= Finset.range (i+1); let c(v):= ∑ i∈t,a v i; refine ⟨∑ v,c v,sum_nonneg fun v _=> sum_nonneg (s:=t) fun j hj=> ha v j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)),fun F d hd hF H hv=>?_⟩; unfold Enroll Ink.draw; rw [sum_sail,Finset.sum_mul]; apply w_sum; intro v h; rw [sail_break A v r (A.priceWord F v),show c v*d=∑ j∈t,a v j*d from Finset.sum_mul ..]; exact w_sum (fun j hj=> hA v j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) F _ hd hF H hv)
lemma mint_before (hq:h≤D)(hp:0<ζ)(i r:ℕ): ∃ C≥(0:ℝ),∀ F:Sketch G,Living x M D F ζ→∀ b≥(0:ℝ), Harrier.Before Γ D x F i r b→ Harrier.Before η D x (A.draw (A.priceWord F)) i r (C*b):= by
   let W:= Finset.Iic i ×ˢ Finset.Iic (M+i); let P (z:ℕ×ℕ)(c:ℝ):= ∀ F: Sketch G,Living x M D F ζ→∀ b≥(0:ℝ), Harrier.Before Γ D x F i r b→ Past i r z.1 z.2→ Enroll η D x (A.draw (A.priceWord F)) z.1 z.2 (c*b);
   have hZ(w l:ℕ)(V:Sketch G)(H:Living x M D V ζ)(hp:l>w+M): Enroll η D x V w l 0:= by rw [Enroll,show sail V w l=0 from funext fun i=>(H.lineage i).1.incarnate.thin w l (by omega)]; exact w_zero
   have ht(z:ℕ×ℕ) : ∃ c≥(0:ℝ), P z c:= by
      let Q (u:Badge A.prism)(v:ℝ) :Prop:= ∀ (F:Sketch G),Living x M D F ζ→∀ b≥(0:ℝ),Issued Γ D x F z.1 z.2 b→u.slot=z.2 →‖u.key F M z.1‖ ≤ v*b; choose a ha hA using fun v:Badge A.prism=> Pocket.key_exp z.1 v.slot (D:=D) v hp rfl (second A v); obtain ⟨p,hp,H⟩:= mint_slot (k:=k) A x hq hp z.1 z.2; let C:ℝ:= 1+∑ i,a i; have hC:1≤ C:= le_add_of_nonneg_right (Finset.sum_nonneg fun i _=>ha i); refine ⟨p*C,mul_nonneg hp (zero_le_one.trans hC),fun F hF b hb h Hq=> ?_⟩; let B:= C*b; have hB: b≤ B:= le_mul_of_one_le_left hb hC; rw [mul_assoc]; apply H F B (hb.trans hB) hF ((h.earlier Hq).1.mon hB); intro v he; exact (hA v x F hF b hb (by rw [he]; exact h.earlier Hq)).trans (mul_le_mul_of_nonneg_right ((single_le_sum (f:=a) (fun i _=> ha _) (mem_univ _)).trans (le_add_of_nonneg_left zero_le_one)) hb)
   obtain ⟨c,hc,H'⟩:= Parcel.collective W (P:=P) (fun _ _ _ hv H F h b hb hi hn=>w_raise (H F h b hb hi hn) (mul_le_mul_of_nonneg_right hv hb)) (fun i _=> ht i); refine ⟨c,hc,fun F hF b hb he n j hj=>?_⟩; by_cases hx:j ≤ M+n; · exact H' (n,j) (mem_product.mpr ⟨Finset.mem_Iic.mpr (by unfold Past at hj; change n≤ i; omega), Finset.mem_Iic.mpr (by unfold Past at hj; change j≤ M+i; omega)⟩) F hF b hb he hj
   exact w_raise (hZ _ _ (A.draw (A.priceWord F)) (A.draw_health _ hq) (by omega)) (mul_nonneg hc hb)
end
end YM.Contacts.Harrier
