import YM.OPE.Compatible.Tony.Pra
/-!
# Vertex cap scaffold. use right/left ring.Permit
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL
variable {i j d k m r l b:ℕ}{n:Side}
local notation "D!"=> Bid.Dir G n
variable (h: Board n b)
-- boundary using cover Prom(paths from outer ring root)
noncomputable def quay (b:ℕ): Prom (RingP b) (StepsL.anchorX b) (32*b) := by choose v ht hv hh using fun i:↥(RingP b)=> (crown (lodger b) i.property).sees; exact ⟨v,lodger b,ht,hv,hh⟩
noncomputable def Trim (r:ℕ)(x:Edge (Site n)):Prop:= pdist x.1≤ r ∧ pdist (dotUp x) ≤ r
include h in lemma guardM (v:Edge Cover) (hp:v∈bark b) : Trim b (Moor v n):= by obtain ⟨hx,hV⟩:= (cross_def v).1 hp; exact ⟨aery h hx,by rw [← pier]; exact aery h hV⟩
-- if base and upper on box iff Moor.F.Read. Nonwrap board b+1 (need for corner). choose stronger for collar
lemma edgeMy (e:Edge (Site n))(h:Board n (b+1))(hx:Trim b e):∃ i∈bark b,Moor i n=e:=by
       obtain ⟨hp,H⟩:=hx; let k:= lift e.1; let i:Edge Cover:=(k,e.2); have hh:k∈Lattice.box b:= (lift_le e.1).mp hp; have he: Moor i n=e:=Prod.ext (wrap_lift e.1) rfl; refine ⟨i,(cross_def _).mpr ⟨hh,?_⟩,he⟩; have hM:wrap n (dotUp i)=dotUp e:= (pier i).trans (congr_arg dotUp he); rw [← level h (show dotUp i∈Lattice.box (b+1) from (up _ e.2 hh).1),hM]; exact (lift_le _).mp H
lemma rimS (e:Edge (Site n))(hv: ¬Trim k e) : (pdist e.1 ≤ k→ pdist e.1=k)∧ (pdist (dotUp e) ≤ k→ pdist (dotUp e)=k):=by
        have hx:= (boulder e.2 e.1).2; change pdist (dotUp e) ≤ _ at hx; have hy:= (boulder e.2 (dotUp e)).1; rw [show dotUp e-step e.2=e.1 from add_sub_cancel_right ..] at hy; unfold Trim at hv; omega
lemma grand (h:Board n b)(x:Site n) (hp: pdist x=b):lift x∈RingP b:=by obtain ⟨k,hk,rfl⟩:= Finset.mem_image.mp ((high h _).2 hp); rw[level h (close hk)];exact hk
noncomputable def stemL (h:Board n b)(U:Config G n)(x:Site n):G.El:= if hz:pdist x=b then travel (expandAt 0 U) (anchorX b) ((quay b).voyage ⟨lift x,grand h x hz⟩) else 1
lemma stem_rule (u:Site n→ G.El)(U:Config G n)(x:Site n)(hx:pdist x=b): stemL h (Lattice.gauge u U) x=u (wrap n (anchorX b))*stemL h U x*(u x)⁻¹:=by
        simp only [stemL,dif_pos hx,expandAt_gauge]; rw [travel_gauge, Prom.ends, wrap_lift, add_zero,add_zero]
lemma stem_off (U:Config G n)(x:Site n)(hx:b < pdist x):stemL h U x=1:=dif_neg hx.ne'
-- retain box links and replace others by boundary transports
noncomputable def hermM (h:Board n b)(U:Config G n)(e:Edge (Site n)): G.El:= if Trim b e then U e else (stemL h U e.1)⁻¹ * stemL h U (dotUp e)
lemma fieldKom (u:Site n→G.El)(U:Config G n): ∃ s:Site n→ G.El, hermM h (Lattice.gauge u U)= Lattice.gauge s (hermM h U):=by
        let V:= u (wrap n (anchorX b)); let s (i:Site n):= if pdist i ≤ b then u i else V; refine ⟨s,?_⟩; funext e; by_cases hp:Trim b e
        · unfold Lattice.gauge; change hermM h (Lattice.gauge u U) e= s _*_* (s _)⁻¹; rw [hermM,if_pos hp,hermM,if_pos hp, show s e.1 = u e.1 from if_pos hp.1, show s (dotUp e)=u _ from if_pos hp.2]; rfl
        have hh(x:Site n)(h':b ≤ pdist x): stemL h (Lattice.gauge u U) x= V*stemL h U x* (s x)⁻¹:=by
              rcases h'.eq_or_lt with h'|h'
              · rw [show s x=u x from if_pos h'.symm.le]; exact stem_rule h _ _ x h'.symm
              rw [stem_off _ _ _ h',stem_off _ _ _ h',show s x=V from if_neg h'.not_ge]; simp
        have hx: b ≤ pdist e.1:=by by_contra! h; exact h.ne ((rimS e hp).1 h.le)
        have ht: b ≤ pdist (dotUp e):= by by_contra! h; exact h.ne ((rimS e hp).2 h.le)
        change hermM h (Lattice.gauge u U) e=s e.1 * hermM h U e * (s (dotUp e))⁻¹; rw [hermM, hermM, if_neg hp,if_neg hp,hh e.1 hx, hh (dotUp e) ht]; group
lemma beamOut (U V:Config G n)(_H:Board n (b+1))(hx: Agrees {i:Site n|pdist i ≤ b} U V):hermM h U=hermM h V:=by
      have he: Agrees (↑(RingP b)) (expandAt 0 U) (expandAt 0 V):=by
           intro e hv hS; unfold expandAt; simp only[add_zero]; apply hx; exact aery h (close hv); change pdist (dotUp (Moor e n)) ≤ _; exact (pier e) ▸ aery h (close hS)
      have hh(x): stemL h U x=stemL h V x:=by unfold stemL;split; exact (quay b).trough _ _ _ he; rfl
      funext e; unfold hermM; split; next hk=> exact hx e hk.1 hk.2
      next hk=> rw[hh,hh]
end YM.OPE.Merchant
