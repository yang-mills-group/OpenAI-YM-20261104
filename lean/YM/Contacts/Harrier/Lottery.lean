import YM.Contacts.Harrier.Stock
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
variable (v:Site s.L)
open Barrage Barrage.Slope
abbrev motion (e:Parcel G)(p:Word)(s:Parcel.Step)(v:Site s.L)(i r:ℕ)(V:Sketch G) : Ribbon (Dye G) r:= fun φ=> printRun (Local.Bery (Origin.bleed G (e.gas p s)) (curb s v) (foot s v) (sail V i r) φ)
abbrev keep (e:Parcel G)(p:Word)(s:Parcel.Step)(v:Site s.L) (M i r:ℕ)(V:Sketch G) : Ribbon (Dye G) r:= fun φ=>lifts (Barrage.Slope.nest (e.flag s) G (e.gas p s)) (Slope.lottery r G (coil (migrated (V (desk s v φ)) (curb s v)) M (M+4+i-r)))
lemma stiff (e:Parcel G)(p:Word)(s:Parcel.Step): (e.gas p s).strip (e.reach:ℝ) e.tax := strip_mono (e.rod p s [] (by simp)) le_rfl (div_le_self e.tax_pos.le (one_le_pow₀ (by exact_mod_cast s.L.property)))
local notation "η" => (2*ζ : ℝ≥0)
local notation "Γ" => terrain ζ (Dye G)
local notation "Υ" => terrain η (Dye G)
variable {V:Sketch G}{x:Dye G}
include T hp hs
set_option maxHeartbeats 1000000 in
lemma primogen (hr:r≤ M+i)(H: Living x M D V ζ) : lead e p s v i r V= motion e p s v i r V-keep e p s v M i r V:= by
   let A:= crafts e p s T hp; funext φ; let y:= desk s v φ; let z:= curb s v; let P:=V y; obtain ⟨hM,B,hB⟩:= H.lineage y; obtain ⟨b,c,Q,hQ⟩:= permits e p s T hp hs; let t:=M+4+i-r; let Y := migrated P z; have hT(j:ℕ):∃ c:ℝ, Rest Γ (0,x) (coil Y M t j) c:= by
       let H:= (Catch.xin (Catch.cap M) 0 (Lotus.revised z hB)); unfold coil dazzle; split; exact ⟨_,H.lands ..⟩; exact ⟨_,Rest.zero⟩
   choose f hf using hT; have ht:= Theater.pure_parade (T:=A) hQ (step_reserved s ζ) (hB.lands i r) (hM.incarnate.sym i r) (show r≤dart i r from by unfold dart; omega) (by unfold dart; omega) z; change A.spot _ (i-i) (P i r) z r= printRun (Trace.wreath z (install (Origin.bleed G (e.gas p s))) (P i r))-keep e p s v M i r V φ -- motion = print not lifts below
   rw [Nat.sub_self,ht,Lotus.orchid,Lotus.orchid]; rw [← Pocket.current_coil M P hr,← coil_burst]; have hy: Row.strip (Origin.stretch A.P A.K G A.W.V) η c := fun v x=> hQ.scope (Sum.inr v) x
   have hL:η≤ e.reach:= by have ht:=T.warm; apply NNReal.coe_le_coe.mp; linarith only [ht,NNReal.coe_nonneg η]
   rw [← Pocket.current_coil M (V y) hr,← coil_burst]
   exact gauge_horizon (step_reserved s ζ) (e.awake p s) (e.wheel p s).governed hQ.glow hQ.ahead (stiff e p s) hL e.tax_pos.le hy (zero_le_one.trans hQ.hold) (migrant z hM hB) (fun j _=> hf j)
omit hp
omit T hs in
lemma spa_pond [Fintype ι]{F:Field ι (Node X)}{x:X}(hs:0<ζ)(h:Rest (terrain η _) (0,x) F b):Rest (bath ζ k _) (0,x) F ((fit_spare η ζ k (by rw [two_mul]; exact lt_add_of_pos_right _ hs)).choose*b) := by
   have he:ζ<η:= by rw [two_mul]; exact lt_add_of_pos_right _ hs
   let A:= fit_spare η ζ k he; have ht:0 ≤ A.choose:=zero_le_one.trans A.choose_spec.1; exact budget_mono (budget_scale ht h) (fun _=> mul_nonneg (norm_nonneg _) (fee_plus _)) (fun i=> (mul_le_mul_of_nonneg_left (show fee (bath ζ k X) (0,x) i ≤ A.choose*fee (terrain η X) (0,x) i from A.choose_spec.2 X (Option ι) _ _) (norm_nonneg _)).trans_eq (mul_left_comm ..)) -- omit T
lemma keep_est (x:Dye G) (hr:r ≤ M+i): ∃ C≥(0:ℝ),∀ V:Sketch G,∀ b≥(0:ℝ), Harrier.Before Γ D x V i r b→∀ p, Weight (keep e p s v M i r V) D (bath ζ k _) x (C*b):= by
   let Y:= parcelY ζ (curb s v); have hy:0<Y:= Real.exp_pos _; let U:= mountain G ζ (fun _=>1) r; let W:=max 0 U; have hw:0≤W:= le_max_left ..; let z:Candles G:= Sum.inr x; let d:= spanned (e.flag s) e.reach e.tax; have hd:0≤d:= spanned_positive e.tax_pos.le; let q:ℝ:= access s.L η (((0:Cover),z)) ((0:Cover),x)* (Fintype.card (Dye G)*beamPrice η d)^r; have hh:0≤q:= by unfold q access beamPrice; positivity
   let w:= fit_spare η ζ k T.emit_lt; refine ⟨w.choose*(q*W*Y), mul_nonneg (zero_le_one.trans w.choose_spec.1) (by positivity), fun F b hb H p φ c hc Gx=>?_ ⟩; let f:= desk s v φ; let P:= F f; let K:= keep e p s v M i r F; let t:=M+4+i-r; have hs:η≤e.reach:=by have ht:=T.warm; apply NNReal.coe_le_coe.mp; linarith only [ht,NNReal.coe_nonneg η]
   let B:=b*c; let X:=coil (migrated P (curb s v)) M t; have hp (j:ℕ)(he:j<r): Rest (terrain ζ _) (0,x) (X j) (Y*B):=by rw [show X j=_ from coil_burst (F:=P) M t j (curb s v)]; exact staple _ (Pocket.subprice hb H hr j he _ c hc (desk_cost s v φ Gx hc))
   have h' : mountain G ζ (fun _=>Y*B) r≤ W*(Y*B):= by refine le_trans (b:=U*(Y*B)) (le_of_eq ?_) (mul_le_mul_of_nonneg_right (le_max_right ..) (show 0≤ Y*B by positivity)); unfold U mountain; simp only [sum_mul,mul_one,mul_assoc]
   apply (spa_pond T.light (hoist_price x (succeeds (P:=e.flag s) (stiff e p s) hs e.tax_pos.le) hd (step_reserved s ζ) ((mountain_fee (G:=G) le_rfl hp z).ist h'))).ist; unfold q; exact le_of_eq (by ring)
end Transfer
end
end YM.Contacts.Harrier
