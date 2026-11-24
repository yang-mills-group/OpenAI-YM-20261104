import YM.MS.ScaleForest.Planted
/-!
# Forest sum on multi-pin families (angular continuation not left behind)

The sum over all admissible subtractive forests is *calculated*. Actual
signed quotient integrals with powers of z coming from single & bulk polar
vertices, so they need NOT be finite at the puncture. Identity BEFORE finite
sector specialization. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Planted
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I : Type} [TopologicalSpace I] {X Y : Curtain G I} {h n : ℕ} {b : Bool} (μ:ℝ)
omit [TopologicalSpace I] in
theorem startSum (F:List (Flats G))(t:ℕ): startPaid (I:=I) μ t F.sum=(F.map (startPaid μ t)).sum:= by
   induction F with
   | nil=> simp [ startPaid ];
   | cons V F ih=>
      funext z s x; rw [List.map_cons,List.sum_cons,List.sum_cons,← ih]; have hp:= congr_arg (plow 0 (-s)) (congr_fun (page_add V F.sum t μ s) z); simp_rw [ Pi.add_apply, ← starter _ μ t t z s x, backing,sub_self, ← cert,map_add] at hp; simpa only [cert,snow,neg_add_cancel,posing,Pi.add_apply] using hp
omit [TopologicalSpace I] in
theorem settled (F:GraphSum G b h)(t:ℕ): Iris (asLeaf (I:=I) F.instructions.renorm μ t) ((F.quotients.map (startPaid μ t)).sum) := by rw [ ← startSum ]; exact EventuallyEq.trans (popTie _) (sameStation F.forest_summed μ t)

def Clocked (F:Planted G I b)(μ:ℝ):Prop:= ∀ X∈forests μ F,∃ n,Mercurial (fun V=> active V F.slots b) X n
def Charged (F:Planted G I true)(μ:ℝ): Prop:= ∀ X∈Planted.parts μ F,∃ n,Mercurial (fun V=> Crossing V F.slots) X n
variable [FirstCountableTopology I]
private theorem counted (F : Planted G I true)(hp:F.Charged μ) : Clocked F μ := by
   unfold Clocked; rw [found]; intro _ hx; obtain ⟨i,hi,rfl⟩:= List.mem_map.mp hx; obtain ⟨n,hV⟩:=hp i hi; exact ⟨ n,(migrate_m hV).maps (fun x hx=> activated hx.1 hx.2)⟩
omit [FirstCountableTopology I] in
private lemma bulk_plan {F:GraphSum G true 4}{X:Curtain G I} (ht:X∈F.quotients.map (startPaid μ 0)) : ∃ n,Mercurial (fun V=> Hover V F.slots) X n:= by
   obtain ⟨x,hx,rfl⟩:= List.mem_map.mp ht; obtain ⟨n,hn⟩:= tiBulk (I:=I) hx μ; exact ⟨ n,_,EventuallyEq.symm (popTie _),hn⟩
private theorem c_U (K:LineRule G)(F:Planted G I true)(hF:F.Clocked μ) : (U K F).Charged μ:= by
   intro X he; obtain ⟨i,hi,rfl⟩:= List.mem_map.mp he; obtain ⟨n,hp⟩:= hF i hi; exact ⟨ _, loopMerc (p:=F.slots) (hp.maps (fun i h=> h.1 rfl)) K μ⟩
omit [FirstCountableTopology I] in
private theorem c_B (K:LineRule G)(F:GraphSum G true 4)(X:Planted G I true)(hX:X.Clocked μ) : (B K F X).Charged μ:= by
   intro Y he; obtain ⟨i,hi,hU⟩:= List.mem_flatMap.mp he; obtain ⟨j,hj,rfl⟩:= List.mem_map.mp hU; obtain ⟨n,hp⟩:= bulk_plan μ hi; obtain ⟨ k,hv⟩:= hX j hj; exact ⟨ _,bridgeMerc hp (q:=X.slots) (hv.maps (fun i h=> h.1 rfl)) K⟩
private theorem c_P {c:Bool}(K:LineRule G)(X:Planted G I b)(Y:Planted G I c)(hX:X.Clocked μ)(hY:Y.Clocked μ) {A:I→QP}(h:AdmittedGap A): (P K A X Y).Charged μ:= by
   intro V he; obtain ⟨i,hi,hU⟩:= List.mem_flatMap.mp he; obtain ⟨j,hj,rfl⟩:= List.mem_map.mp hU; obtain ⟨n,hp⟩:= hX i hi; obtain ⟨k,hV⟩:= hY j hj; exact ⟨ _,pinMerc (p:=X.slots) (q:=Y.slots) (hp.maps (fun i hu=> hu.2.1)) (hV.maps (fun i hu=> hu.2.1)) K μ h⟩

theorem clocked (F:Planted G I b)(he:F.Stand): F.Clocked μ := by
   induction F with
   | bed X=> intro i he; obtain ⟨p,hp,rfl⟩:= List.mem_map.mp he; obtain ⟨n,hF,hH⟩:= tires (I:=I) hp μ; exact ⟨ n,_, EventuallyEq.symm (popTie _), inert hH hF⟩
   | U K X ih=> exact counted μ _ (c_U μ K _ (ih he))
   | B K F X ih=> exact counted μ _ (c_B μ K _ _ (ih he))
   | P K A X Y ih it=> exact counted μ _ (c_P μ K _ _ (ih he.1) (it he.2.1) he.2.2)

theorem charged (F:Planted G I true)(he:F.Stand): F.Charged μ:= by
   cases F with
   | U K X=> exact c_U μ K _ (clocked μ X he)
   | B K X Y=> exact c_B μ K _ _ (clocked μ Y he)
   | P K A X Y=> exact c_P μ K _ _ (clocked μ X he.1) (clocked μ Y he.2.1) he.2.2

theorem fluxing (F:Planted G I true)(he:F.Stand) : ∀ i∈Planted.parts μ F, Fluxible i := fun i hi=> (charged μ F he i hi).choose_spec.quo (fun _ h=> (_root_.YM.MS.ScaleForest.Crossing.possible h).2)
theorem permitted (F:Planted G I b)(he:F.Stand) : ∀ i∈forests μ F, Visits i := fun i hi=> (clocked μ F he i hi).choose_spec.tide (fun _ h=> paceVisits h.2.1)
private def KnotTie (X:Planted G I b) (μ:ℝ) := ∀ p:b=true, let F:Planted G I true:= p ▸ X; Iris (push μ F) (Planted.parts μ F).sum
private theorem authorized (X:Planted G I b)(he:X.Stand): Iris (resolve μ X) (forests μ X).sum ∧ KnotTie X μ := by
   have hT(X:Planted G I true)(he:X.Stand)(hu:Iris (push μ X) (Planted.parts μ X).sum): Iris (resolve μ X) (forests μ X).sum∧ KnotTie X μ:= ⟨(by rw [rooting,found]; exact EventuallyEq.trans (recoil hu) (spends_v _ (fluxing μ X he))),fun _=>hu⟩
   induction X with
   | bed X=> exact ⟨ settled μ .., fun p=>Bool.noConfusion p⟩
   | U K X ih=> exact hT _ he (EventuallyEq.trans (close_delivery (ih he).1 K μ) (spends_u K μ _ (permitted μ X he)))
   | B K X Y ih=> exact hT _ he (EventuallyEq.trans (bridge_delivery (settled μ X 0) (ih he).1 K) (spends_b K _ _ (fun i h=>(bulk_plan μ h).choose_spec.tide (fun i h=> hoverVisits h)) (permitted μ Y he)))
   | P K A X Y ih it=> exact hT _ he (EventuallyEq.trans (pin_delivery (ih he.1).1 (it he.2.1).1 K μ A) (spends_p K μ A _ _ (permitted μ X he.1) (permitted μ Y he.2.1)))

theorem exactCampaign (X:Planted G I b)(h:X.Stand) : Iris (resolve μ X) (forests μ X).sum := (authorized μ X h).1
theorem forceed (X:Planted G I true)(h:X.Stand): Iris (push μ X) (Planted.parts μ X).sum:= (authorized μ X h).2 rfl
end YM.MS.ScaleForest.Planted
