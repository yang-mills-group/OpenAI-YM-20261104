import YM.Contacts.Harrier.Sheet
import YM.Contacts.Procession.Inlet
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
open Cartons Font MultiNext.SignedSource Pattern Barrage.Reserve.Oasis Tensor
-- order-power vs rank. At rank r≤M+i cost ticket, plus all needed Pre.A program.
variable {F:Sketch G}{B':bore G} {P:Pulse.Range (Node (Dye G))}{x:Dye G}{u A:ℕ}
def Enroll (P:Pulse.Range (Node (Dye G)))(D:ℕ)(x:Dye G)(V:Sketch G)(i r:ℕ):ℝ→ Prop:= Weight (sail V i r) D P x
def Before (P:Pulse.Range (Node (Dye G)))(D:ℕ)(x:Dye G)(V:Sketch G)(i r:ℕ)(b:ℝ):= ∀ j k,Past i r j k → Enroll P D x V j k b
def Issued (P:Pulse.Range (Node (Dye G)))(D:ℕ)(x:Dye G)(V:Sketch G)(i r:ℕ)(b:ℝ):= Before P D x V i r b ∧ Enroll P D x V i r b
lemma Before.earlier (h:Harrier.Before P D x F i r b)(hp: Past i r l n): Issued P D x F l n b:= ⟨fun _ _ ht=> h _ _ (pastTrans hp ht),h _ _ hp⟩
lemma Before.weaken {Q:Pulse.Range (Node (Dye G))} (h:Harrier.Before P D x F i r b)(he:b≤c) (ht:∀ (j:ℕ)(s:Option (Fin j)→Node (Dye G)), Q.bill s ≤ P.bill s): Harrier.Before Q D x F i r c:= fun _ _ hi=> w_upped (h _ _ hi) he (ht _)
lemma Before.mon (h:Harrier.Before P D x F i r b) (he:b≤c):Harrier.Before P D x F i r c:=h.weaken he fun _ _=>le_rfl
lemma Before.lower (h:Harrier.Before (bath ζ k _) D x F i r b): Harrier.Before (terrain ζ _) D x F i r b:=h.weaken le_rfl fun _ _=> bath_terrace _
-- reserve horizon, algebra
namespace Pocket
lemma current_coil (u:ℕ)(X:House β) (hr:r ≤ u+i) : coil X u (u+4+i-r) r=X i r:= by unfold coil dazzle shiftA Catch.cap; rw [if_pos (by omega),if_pos (by omega),show _=_ from (show u+4+i-r+r-2-(u+2)=i from by omega)]
lemma subprice (hh:0 ≤ b)(h:Harrier.Before P D x F i r b)(hr:r ≤ M + i) (j:ℕ)(he:j<r): Weight (fun φ:Cards=>coil (F φ) M (M+4+i-r) j) D P x b:= by
   unfold coil dazzle shiftA Catch.cap; split_ifs; · exact h _ _ (Or.inl (by omega))
   all_goals exact w_raise w_zero hh
private lemma runner {T Y:Type}[NormedAddCommGroup T](v:Y→T){a:ℝ}(h:SumBudget (fun i=> ‖v i‖) a): ‖∑' i,v i‖ ≤ a:= (norm_tsum_le_tsum_norm h.2.1).trans h.2.2
lemma peg (k j:ℕ)(hs:0<ζ):∃ C≥(0:ℝ),∀ V:Field (Fin k) (Node (Dye G)),∀ y:Dye G,∀ b:ℝ,Rest (terrain ζ _) (0,y) V b→ ‖Shuttle.sheet k V (Tide.lens G j)‖≤C*b:= by
    let C:=(( (j:ℝ)+1)^k*Shuttle.hail (j*k) (ζ:ℝ)); refine ⟨C,by unfold C Shuttle.hail; positivity,fun V y b h=>?_⟩; unfold Shuttle.sheet; exact (runner (blanket k V (Tide.lens G j)) (blanket_spend h hs (by positivity:0≤(j:ℝ)+1) (Tide.glaze G j))).trans_eq (mul_comm b C)
theorem tower_exp (k d:ℕ)(hs:0<ζ): ∃ C≥(0:ℝ),∀ T:Cohort G,∀ x:Dye G,∀ b≥(0:ℝ),(∀ r≤k,Rest (terrain ζ _) (0,x) (T r) b) → ‖tower T d k‖ ≤ C*b:= by
   let z:= d*(d+1); choose a ha H using fun k':Fin (k+1)=> peg (G:=G) k'.val z hs; refine ⟨(∑ i,a i),sum_nonneg fun i _=> ha _, fun T x b hb hf=> (pi_norm_le_iff_of_nonneg (mul_nonneg (sum_nonneg fun i _=> ha i) hb)).2 fun i=> (H i _ x _ (hf i.val (by omega))).trans (mul_le_mul_of_nonneg_right (single_le_sum (f:=a) (fun i _=>ha i) (mem_univ _)) hb) ⟩
variable {d:ℕ}{H:Labels.Frame G d} (i k:ℕ)
theorem key_exp (v:Badge H)(ht:0<ζ)(hh:v.slot=k) (hk:k ≤ M): ∃ C≥(0:ℝ),∀ x:Dye G,∀ V:Sketch G, Living x M D V ζ→∀ b≥(0:ℝ), Issued (terrain ζ _) D x V i k b→ ‖v.key V M i‖ ≤ C*b:= by
   obtain ⟨c,hc,φ⟩:= Cards.reach D v.phi; obtain ⟨t,ht',H⟩:= tower_exp (G:=G) v.slot d ht; obtain ⟨a,ha,h⟩:= Cartons.prices v.loc; let K:=a*t*c; refine ⟨K,mul_nonneg (mul_nonneg ha ht') hc,fun x V hv b hb hy=>?_⟩; let i':= M+4+i-v.slot; let Q:= coil (V v.phi) M i'; obtain ⟨hx,Z,hZ⟩:=hv.lineage v.phi; have hh' (r)(he:r≤ v.slot) : Rest (terrain ζ _) (0,x) (Q r) (b*c):= by
      subst k; by_cases h:r=v.slot; · subst r; rw [show Q v.slot=V v.phi i v.slot from current_coil _ _ (by omega)]; exact hy.2 v.phi _ hc φ
      exact Pocket.subprice (F:=V) hb hy.1 (by omega:M + i ≥ v.slot) _ (by omega) v.phi _ hc φ
   unfold Badge.key fill; rw [if_pos (by change v.slot ≤ M+i; omega)]; exact (h Q (coil_tags hx hZ ht _)).trans ((mul_le_mul_of_nonneg_left (H Q _ _ (mul_nonneg hb hc) hh') ha).trans_eq (by unfold K; ring))
end Pocket
-- null can be interpreted on all homogeneous card probes, not just coordinate basis.
variable {hZ:ℝ≥0}{d:ℕ}{F₀:Labels.Frame G d}{V:Sketch G}
lemma card_price (h:Living x M D V ζ)(hp:0<ζ)(f:F₀.Index)(v:ℕ): IsLinearMap ℝ (fun y:Cards=> fill F₀ M (V y) v f) := by
   constructor; · intro y z; rw [h.lin.map_add]; simpa only [one_smul,one_mul] using fill_linear F₀ (h.lineage y) (h.lineage z) hp 1 v f
   intro a x'; rw [h.lin.map_smul]; simpa only [add_zero, Pi.zero_apply,fill_null F₀ x,smul_eq_mul] using fill_linear F₀ (h.lineage x') (Based.zero (v:=x) (ζ:=ζ) (M:=M)) hp a v f
lemma inner_void (h:Living x M D V ζ)(hp:0<ζ)(hh:r ≤ d)(hi:∀ v:Badge F₀,v.win ≤ r→v.key V M i=0)(n:ℕ)(u:Cards)(x':F₀.Index)(hU:Powers.home u.val n)(hx:(F₀.grades x').1+n ≤ r) : fill F₀ M (V u) i x'=0:= by
    let u' := (card_price h hp x' i).mk' _; change u' u=0
    rw [Font.reflect u hU,map_sum]; apply sum_eq_zero; intro j _; rw [map_smul]; let v:Badge F₀:=⟨(x',⟨⟨n,by omega⟩,j⟩),by simpa using (hx.trans hh)⟩; rw [show u' (plait j) =0 from hi v hx,smul_zero]
lemma velum_void (h:Living x M D V ζ)(hp:0<ζ)(hh:r≤ d)(hi:∀ v:Badge F₀,v.win ≤ r→∀ i,v.key V M i=0)(u:Cards)(hU:Powers.home u.val n) (x':F₀.Index)(hx:(F₀.grades x').1+n≤ r) : velum F₀ (coil (V u) M l) x'=0:= by
    obtain ⟨he,B,hB⟩:=h.lineage u; rw [fueled he x hp hB]; split; exacts [inner_void h hp hh (fun v ht=> hi v ht _) _ u x' hU hx,rfl]
lemma core_void (h:Living x M D V ζ)(hp:0<ζ)(hh:r≤ d)(hi:∀ v:Badge F₀,v.win ≤ r →∀ i,v.key V M i=0): Clear (fun u:Cards=>coil (V u) M l k) (r+1-k) := by
    let H u :=h.lineage u; choose p P hP using H; have hx (u : Cards):= coil_tags (p u) (hP u) hp l; apply Clear.across (u:=d*(d+1)) (d:=d) (h:=r) (n:=d) (f:=fun u=>coil (V u) M l) hx (by omega) hh rfl le_rfl le_rfl; intro b i he hB; apply silent_projection F₀ (hx b) (by omega) le_rfl le_rfl; intro v hv; rw [← charter (hx b),velum_void h hp hh hi _ hB _ (by omega),Complex.ofReal_zero]
end
end YM.Contacts.Harrier
