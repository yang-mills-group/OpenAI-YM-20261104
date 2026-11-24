import YM.FormalBulk08.Hay.Motor

/-! On any matching Kin, real comparison can take extras STARTING at
three, no β-scale powers from support that aren't declared. K,L here
entry before block. Keep explicit Λ from comparison using THAT particular
path representation, not claiming it itself paid by `Render`.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Hay
open Filter Set Function MeasureTheory Lattice RG Exterior Wilson Precision Tree Work.F05
open Stationary hiding shine Rays
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa Broc City Cork Lotus Shore Gorge Laurent Bloch Flat Next.Free Bank Wine
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{A B C σ τ η:ℝ}{p:Clip}{R:PathData G}{E:ℕ}{V B':Pot G}
lemma leaf_up (hG:G.Simple)(hs:0<σ)(h:0<τ)(ha:0≤ A)(a:ℝ)(hp:0≤a)(E:ℕ)(hE:2 ≤ E):∃ δ d K D:ℝ,0<δ∧ 0<d ∧0≤K∧0≤D∧ ∃ B:ℝ, 0≤B ∧ ∀ p: Clip,p.direct≤ a →∀ (R:PathData G) Λ,R.Bounds p σ A Λ→ ∃ U:Pot G,Troupe U p R∧ Fits U E δ (K+Λ*D)∧ ∀ (V:Pot G) C,Fits V E τ C→ Temper V E → Sane V E → (∀ j≤2,V j=U j) → ∃ P,PrintK (V-U) E 3 (E-2) d ((C+(K+Λ*D))*B) P:= by
   obtain ⟨δ,K,D,hδ,hK,hD,X⟩:= manuscript G hG σ A a hs ha hp E
   let u:=min δ τ; have hu:0<u:= lt_min hδ h
   obtain ⟨v,W,hv,hw,H⟩:=larvae G hG E (E-2) u hu
   refine ⟨δ,v,K,D,hδ,hv,hK,hD,W,hw,fun p hx R Λ hz=>?_⟩
   obtain ⟨U,hU,ht⟩:= X p hx R Λ hz; refine ⟨U,hU,ht,fun V C c f s hb=> ?_⟩
   apply H 3 (by omega) _ _ ((c.mono (min_le_right ..) le_rfl).sub (ht.mono (min_le_left ..) le_rfl)) (temper_less f (float_temp hU.toFloatK _) c ht h.le hδ.le) (s.sub (hU.seals E) c ht h hδ)
   intro j hj i;rw [Pi.sub_apply,hb j (by omega),sub_self,Pi.zero_apply]
lemma extra_seen {P: List (LeafD G)}(h:PrintK (V-B') E 3 (E-2) η A P)(hk:2≤E)(b:Troupe B' p R)(hv:Fits V E σ B)(hp:Fits B' E τ C)(h1:0≤σ)(h2:0≤τ)(n:Side): Through E (stone V n) (novel p R n+(P.map (fun a=> mountain (issue a.field) n a.u)).sum) := by
    intro i hi; rw [←book_mountain h.honest,← b.buys,map_add]; have he: coeff i (stone (V-B') n)=coeff i (stone (binding P) n):= by rw [sow_coeff,sow_coeff]; simp_rw [sow,h.agrees i (by omega)]
    rw [←he,shed_stamp h1 h2 hv hp i hi,map_sub]; abel
end YM.FormalBulk08.Hay
