import YM.Contacts.Procession.Piper
import YM.Contacts.Procession.Cirrus
import YM.Contacts.Procession.Damask
/-! # Interior motion of principal Mark shells. Canonical A0 filter realizes all moments for Peek.T.Stored budget permit separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Pierian
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter Shuttle.Tide
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
open Tree FreeResolvent Draw PhysicalNext.RankCovariance Catch Hinges Lotus Welcome.Theater
open Barrage Barrage.Slope Barrage.Reserve Barrage.Reserve.Oasis Odor Odor.Winding Odor.Winding.Sales Port
open Planned.PrimaryIntegral295 Carrier Place MultiNext.SignedSource Pattern Shuttle.Tide.Morning
open Tensor Mediator Next.Foundations Labels Source Drops WardBin Cartons Broadcast
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
variable {G:Gauge}{n k i r l p j d h u:ℕ}{b c :ℝ}{X ι E W: Type}[NormedAddCommGroup E] [NormedSpace ℝ E][NormedAddCommGroup W][NormedSpace ℝ W]
variable (e:Oasis G)(B:Labels.Frame G d){V F:Field (Fin k) (Node (Dye G))}{y:Dye G}{s t:ℝ≥0}
lemma tower_express (F:Field (Fin k) (Node (Dye G)))(d:ℕ): subcode (Shuttle.sheet k F (Tide.lens G (d*(d+1))))=Cartons.tower (Pi.single (M:=fun k:ℕ=>Field (Fin k) (Node (Dye G))) k F) d k:= by
    funext i; refine Fin.lastCases ?_ (fun i=>?_ ) i
    · unfold subcode Cartons.tower; rw [Pi.single_eq_same]; erw [show Shuttle.sheet (Fin.last k).val (Pi.single (M:=fun i=> Field (Fin i) (Node (Dye G))) k F _) _=Shuttle.sheet k F (Tide.lens G (d*(d+1))) from congr_arg (fun Y=>Shuttle.sheet k Y _) (Pi.single_eq_same (M:=fun i=> Field (Fin i) (Node (Dye G))) k F)]
    unfold subcode Cartons.tower; have hh : Pi.single (M:=fun k:ℕ=>Field (Fin k) (Node (Dye G))) k F i.castSucc.val=0:= Pi.single_eq_of_ne (by change i.val≠ k; omega) _; rw [Pi.single_eq_of_ne (Fin.castSucc_ne_last _), hh]; have hz(k:ℕ): blanket (E:=Ship G (d*(d+1))) k (X:=Node (Dye G)) 0 (Tide.lens G _)=0:= (by funext; ext; simp [blanket]); unfold Shuttle.sheet; rw [hz]; exact tsum_zero.symm
private lemma choices {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y](P:X →L[ℝ] Y):∃ a≥(0:ℝ),∀ x, ‖P x‖ ≤ a*‖x‖:= ⟨_,norm_nonneg P,P.le_opNorm⟩
private lemma stone (F:Field (Fin k) (Node (Dye G)))(hF:Rest (terrain s _) (0,y) F b) (hp:Poem F)(he:0<s): Felt (Pi.single k F):= by
   let Y:Cohort G:= Pi.single k F; refine ⟨fun i=>?_,fun i=>?_ ⟩ <;> by_cases hx:i=k; · subst i; rwa [Pi.single_eq_same]
   · rw [Pi.single_eq_of_ne hx]; exact Poem.empty
   · subst i; exact ⟨y,s,he,b,by rwa [Pi.single_eq_same]⟩
   exact ⟨y,s,he,0,by rw [Pi.single_eq_of_ne hx]; exact Rest.zero⟩
theorem old_price (j k:ℕ): e.Permit (fun i c=>∀ x:Dye G,∀ F:Field (Fin k) (Node (Dye G)),∀ b≥(0:ℝ),Rest (terrain (e.ξ i) _) (0,x) F b→ ‖cursor B j k F‖≤ c*b):= by
    let u:= d*(d+1); obtain ⟨a,ha,h⟩:= choices (X:=bins G d k) (Y:=B.Coeff) (peek B j k); refine ⟨fun i=>a*joss e u u k i,(e.fair_const a ha).mul (fair_joss e u k 0),fun i x F b hb hf=>?_ ⟩; rw [cursor,tower_express]; apply (h _).trans; rw [mul_assoc,mul_comm (joss ..) b]; refine mul_le_mul_of_nonneg_left (hefty e _ i hb x ?_) ha; intro r hr; by_cases hx:r=k; subst r; simpa; rw [Pi.single_eq_of_ne hx]; exact Rest.ist Rest.zero hb
-- expects ONLY `Poem` (standard). cost unmarked projection.Y
lemma curs_sub {F U:Field (Fin k) (Node (Dye G))}(hF:Rest (terrain s _) (0,y) F b)(hU: Rest (terrain t _) (0,y) U c)(hs:0<s)(ht:0<t)(hp:Poem F)(hu:Poem U)(j:ℕ): cursor B j k (F-U)=cursor B j k F-cursor B j k U:= by
    let P:Cohort G:= Pi.single k F; let Q:Cohort G:= Pi.single k U; have hx:= sheet_tilt Q (stone U hU hu ht) P (stone F hF hp hs) (-1:ℝ) k (u:=d*(d+1)); simp only [neg_one_smul,Pi.add_apply, Pi.neg_apply,P,Q,Pi.single_eq_same] at hx; rw [show -U + F=F-U by abel , add_comm (-Shuttle.sheet ..)] at hx; rw [cursor,cursor,cursor,hx]; unfold subcode; rw [← sub_eq_add_neg,←map_sub]; apply congr_arg; exact Pi.single_sub (f:=fun i:Fin (k+1)=> Tensor.T (Ship G (d*(d+1))) ℝ i.val) (Fin.last k) _ _
open Pigment
variable (E:∀ n,RackCore e.a e.M n)(x:G.ColorIndex)
-- Same slot demand. Teacher parameters. Finances earlier input.No claims θ.FullReport here.CP7 end.Creatures subsequent convergence.
theorem projected_response {R:Rival}{P:MapPrices}(h: Pierian.Charter e.a.clock.kernel.penalty P)(hx:Pierian.Led R e P)(D:ℝ)(hD:0 ≤ D)(k j:ℕ)(hj:j ≤ d) :
     e.Permit (fun i c=>∀ n:ℕ,∀ hi:i<n, j ≤ e.J (i+1) → ∀ z:Cover, Preset e D z i→ ∀ p l:ℕ,∀ F:Cards→ bore G, Puppet G p F → ∀ v:Cards, (∀ a:B.Index,(B.grades a).1 ≤ j → velum B (coil (F v) p l) a=0)→ ∀ y:Dye G,∀ K≥k,0<K → ∀ b≥(0:ℝ), ∀ d:ℝ, Rest (terrain (e.ξ (i+1)) _) (0,y) (coil (F v) p l k) d → (∀ r<k,Rest (terrain (e.ξ (i+1)) _) (0,y) (coil (F v) p l r) b) → ‖cursor B j k ((rentCall e E x i hi).spot K 0 (coil (F v) p l k) z k)‖ ≤ c*b):= by
   obtain ⟨a,ha,hA⟩:= old_price e B j k; obtain ⟨Q,hQ,hS⟩:= pays e E x; let C:= (fair_coin e 0 k D); refine ⟨_,ha.mul C,fun i n hi Hj z hz p l F hF v h0 y K hk hK b hb c hv hL=>?_ ⟩; let X:= F v; let Y:= coil X p l; let T:= rentCall e E x i hi; let Z:= T.spot K 0 (Y k) z k; let W:= total e i n
   let U:= printRun (Trace.wreath z (install (Origin.bleed G W)) (Y k)); let V:=lifts (Slope.nest (e.R i) G W) (Slope.lottery k G (coil (migrated X z) p l)); let η:= e.haloSpan i; obtain ⟨s,B₀,hs,hY⟩:= hF.forecast y v; have he:=coil_tags (hF.holds v) hY hs l; have h': Poem (Y k):= coil_mirror _ (hF.holds v).incarnate l k; have hX: Remains j (Y k):= remains_story B he hj h0; -- use hj
   let d':= newCoin e 0 k i D*b; have hV: Rest (terrain (e.ξ i) _) (0,y) V d':= (Pierian.addon h hx p k 0 n hi hD hz hb hL).upto _ bath_terrace le_rfl; let d'':= (T.gift η (e.Z i) (1+e.Z i) (Real.exp (4+D)) (Q i) K 0 k)*c; have hZ : Rest (terrain (e.ξ i) _) (0,y) Z d'':= ((Theater.donates (hQ.launch i n hi) (e.reaches i) hv (tackle e hz hD) h' hK hk y k)).upto _ (terrain_le (show e.ξ i ≤ e.haloSpan i from le_mul_of_one_le_left (by positivity) one_le_two)) le_rfl
   have ht: Z= U-V:= Pierian.fluct (e:=e) E x h hx hF hQ hi hk hK v y z fun t ht=> (Or.elim (Nat.eq_or_lt_of_le ht) (fun hr=>by subst t; exact ⟨c,hv⟩) (fun ht=> ⟨b,hL t ht⟩))
   have hx' : Rest (terrain (e.ξ i) _) (0,y) U (d''+d'):= (by rw [show U=Z+V from sub_eq_iff_eq_add.mp ht.symm]; exact hZ.add hV)
   change ‖cursor B j k Z‖ ≤_; rw [ht,curs_sub B hx' hV (e.ξ_pos i) (e.ξ_pos i) (print_even _) hoist_shape j,show cursor B j k U=0 from optic_core B e hi hj Hj (e.ξ_pos (i+1)) hv h' hX z,zero_sub,norm_neg]; rw [mul_assoc]; exact hA i y V d' hV.cash hV
end YM.Contacts.Procession.Pierian
