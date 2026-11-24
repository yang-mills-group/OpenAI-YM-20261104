import YM.MS.ScaleForest.Triangle
/-!
# Actually distribute the pole-subgraph forest formula in the ghost-line example

This verifies that the regulated integral (at every root of the triangle
construction) is still evaluated at the *current dimension*, with the pole
prior to specializing. Infrared lengths held finite. For use both on the
local quotient tree and on the meromorphic (bare) integrals. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle XSpace XSpace.Chiral Cylinder
open scoped Topology ContDiff

lemma frozenLeft {b:Bool}{G:Gauge}{h:ℕ}(K : LineRule G)(A: LocalVertex G true 4)(B: LocalVertex G b h)(n:ℕ) :
    combine b h K (collapsed (Ice n A.symbol)) (classicalPage B.symbol) = collapsed (Ice n (firstSymbol A B K)):= by
    unfold GraphSum.combine connect collapsed classicalPage collapsed
    rw [bridge_single K.half K.ok.rev, Finsupp.smul_single,Nat.add_zero,integrate_single];
    have ht := (firstSew A B K).accepted.force; rw [first_force] at ht; have he:= ht.force; unfold Return at he; simp_rw [classicalPage,collapsed,Finsupp.single_eq_same, Pi.zero_apply] at he
    congr 1; funext z; let c := z⁻¹^n; let x:ℂ:= factor b; change scaleIntegral z h 0 (x • bridgeG K.half (c • A.symbol) B.symbol)=c • firstSymbol A B K
    rw [show bridgeG K.half (c • A.symbol) B.symbol=c • bridgeG K.half A.symbol B.symbol from (by simp_rw [bridgeG_eq K.ok.rev, ← schedule]; exact map_smul ((squad K.half).flip B.symbol) ..),smul_comm x c]; change scaleIntegral z h 0 (c • firstForce A B K)= _; rw [integrate_scale (collapsed_kernel ht.eye).price he.exists.choose_spec, firstSymbol,← scaleZero_invariant z]

namespace Triangle
open Planted Quadratic
variable {G : Gauge} {I : Type} (μ : ℝ) (X Y : Pupil) (A:I→QP) (V:GraphSum G true 4) {F H:Flats G} {U W P:Curtain G I}
local notation "K" => cursor false

section
variable [TopologicalSpace I] (hA:AdmittedGap A)

structure Board (b:Bool)(F:Flats G): Prop where
   own : ∃ f:Coat G,Sewable b 2 4 f F
   rank : OfRank 2 F

omit [TopologicalSpace I] in
lemma boarded (X: GraphSum G true 4)(hp:X.slots=2) : Board true X.instructions.prep:= by
   constructor; exact ⟨_, hp ▸ X.accepted.before⟩; exact hp ▸ X.accepted.legs_pre
omit [TopologicalSpace I] in
lemma board_q (X:GraphSum G true 4)(hp:X.slots=2) : Board true (collapsed X.instructions.pole):= by
   constructor
   exact ⟨ _, Sewable.ofHomogeneous (hp ▸ X.accepted.poleShape) X.accepted.after.back⟩
   exact hp ▸ collapse_rank (Eventually.of_forall X.accepted.legs_ct)
omit [TopologicalSpace I] in
lemma seat (X:Pupil)(G:Gauge) : Board false (plain X G):= ⟨⟨ _, (originPin X G).accepted.usable⟩,(originPin X G).accepted.after_rank⟩
omit [TopologicalSpace I] in
lemma stored (hp:Board true F) : Board false (armData X F) := by
   obtain h:= connect_sewable hp.own.choose_spec (seat X G).own.choose_spec K; exact ⟨ ⟨ _,(integrate_sewable h).2⟩,
      integrate_rank h ( (bridge_rank hp.rank (seat X G).rank (cursor false).ok).realScale _)⟩

abbrev cred (X:Curtain G I) (p:ℤ) := ∃ n:ℕ,Mercurial (fun F=> Crossing F p) X n
lemma thick (hp:Board true F): ∃ n:ℕ,Mercurial (fun X=> Hover (I:=I) X 2) (startPaid μ 0 F) n:= by
   obtain h:= clockMoon hp.own.choose_spec.clock; refine ⟨ poleOrderBound F,_,EventuallyEq.symm (popTie _),?_⟩; refine basicKit ?_; obtain ht:= compensated (I:=I) 0 μ h hp.rank (sufficientBound (Moony.toast h)); simpa only [Nat.cast_zero] using ht
lemma lining (hp:Board false F): ∃ n,Mercurial (fun X=> Paces (I:=I) X 2) (startPaid μ 4 F) n:= by
   obtain h:=clockMoon hp.own.choose_spec.clock; exact ⟨ _,_,EventuallyEq.symm (popTie _), (tenure (by norm_num) h hp.rank (sufficientBound (Moony.toast h)) μ).2⟩
lemma mercVisit (hX:Board false F): Visits (I:=I) (startPaid μ 4 F):= (lining (I:=I) μ hX).choose_spec.tide fun _ h=> paceVisits h
lemma cred_flux {p:ℤ} (hp:cred U p): Fluxible U:= hp.choose_spec.quo fun _ h=> h.possible.2

variable [FirstCountableTopology I] (hF:Board true F) (hH:Board true H)
include hA hF
lemma funded_x : cred (xSlope μ X Y A F) 2 := by
   refine ⟨ _,pinMerc (lining (I:=I) μ (stored X hF)).choose_spec (lining (I:=I) μ (seat Y G)).choose_spec K μ hA⟩
lemma funded_y : cred (ySlope μ X Y A F) 2 := by
   exact ⟨ _,pinMerc (lining (I:=I) μ (seat X G)).choose_spec (lining (I:=I) μ (stored Y hF)).choose_spec K μ hA⟩
lemma funded_b : cred (bSlope μ X Y A F) 2 := by
   obtain h:= (migrate_m (pinMerc (lining (I:=I) μ (seat X G)).choose_spec (lining (I:=I) μ (seat Y G)).choose_spec K μ hA)).maps (fun u h=>h.1)
   exact ⟨ _,bridgeMerc (thick (I:=I) μ hF).choose_spec h K⟩
omit hF hA
lemma cred_seal (h:cred U 2): cred (sealUp μ U) 0:= ⟨ _,loopMerc ((migrate_m h.choose_spec).maps fun _ h=>h.1) K μ⟩

omit [TopologicalSpace I] [FirstCountableTopology I] in
lemma seals (h:Iris U P): Iris (sealPay μ U) (sealPay μ P):= recoil (close_delivery (recoil h) K μ)

omit [TopologicalSpace I] [FirstCountableTopology I] in
private lemma migrate_add (hi:Fluxible U)(hp:Fluxible W): Iris (vertical (U+W)) (vertical U+vertical W):= by
   obtain h:= spends_v [U,W] (fun _ (he:_)=>show _ from (by simp at he; rcases he with rfl|rfl; exact hi; exact hp))
   simpa using h
private lemma visitVert (h:cred U 2): Visits (vertical U):= (migrate_m h.choose_spec).tide (fun _ h=> paceVisits (paceFuel h.1))
lemma seals_plus (hp:cred U 2) (ht:cred W 2): Iris (sealPay μ (U+W)) (sealPay μ U+sealPay μ W) := by
   obtain h:= close_delivery (migrate_add (cred_flux hp) (cred_flux ht)) K μ
   have he : Visits (vertical U) := visitVert hp; have hv:= visitVert ht
   obtain hU:=spends_u K μ [vertical U,vertical W] (fun _ (hu:_)=> show _ from (by simp at hu; rcases hu with rfl|rfl; exact he; exact hv)); simp at hU
   exact EventuallyEq.trans (recoil (EventuallyEq.trans h hU)) (migrate_add (cred_flux (cred_seal μ hp)) (cred_flux (cred_seal μ ht)))

-- raw (punctured) distribution before factoring z^-1 explicitly
omit [TopologicalSpace I] [FirstCountableTopology I] in
lemma start_pair (F H:Flats G)(w:ℕ): startPaid μ w (F+H)=( startPaid μ w F : Curtain G I)+startPaid μ w H:= by simpa using (startSum (I:=I) μ [F,H] w)

include hF hH
omit [TopologicalSpace I] [FirstCountableTopology I] in
lemma start_arm : Iris (I:=I) (startPaid μ 4 (armData X (F+H))) (startPaid μ 4 (armData X F)+startPaid μ 4 (armData X H)):= by rw [ ← start_pair ]; exact sameStation (combine_left hF.own.choose_spec hH.own.choose_spec (seat X G).own.choose_spec K) _ _

include hA
lemma line_pair : Iris (lineIntegral μ X Y A (F+H)) (lineIntegral μ X Y A F+lineIntegral μ X Y A H):= by
   obtain hx:= pin_delivery (start_arm (I:=I) μ X hF hH) (EventuallyEq.rfl (f:=startPaid μ 4 (plain Y G))) K μ A
   obtain hy:= pin_delivery (EventuallyEq.rfl (f:=startPaid μ 4 (plain X G))) (start_arm (I:=I) μ Y hF hH) K μ A
   obtain hx:=seals μ (EventuallyEq.trans hx (smoke_promise K A μ (mercVisit μ (stored X hF)) (mercVisit μ (stored X hH)) (mercVisit μ (seat Y G))).1)
   obtain hy:=seals μ (EventuallyEq.trans hy (smoke_promise K A μ (mercVisit μ (stored Y hF)) (mercVisit μ (stored Y hH)) (mercVisit μ (seat X G))).2)
   obtain hx:= EventuallyEq.trans hx (seals_plus μ (funded_x μ X Y A hA hF) (funded_x μ X Y A hA hH)); obtain hy:= EventuallyEq.trans hy (seals_plus μ (funded_y μ X Y A hA hF) (funded_y μ X Y A hA hH))
   have hb : bSlope μ X Y A (F+H)=bSlope μ X Y A F+bSlope μ X Y A H:= by unfold bSlope; rw [ start_pair ]; funext z t x; simp only [Bfor,Pi.add_apply,bridgeG_eq (cursor (G:=G) false).ok.rev,← schedule,map_add,LinearMap.add_apply]
   unfold lineIntegral; rw [hb, show ∀ x y z u v w:Curtain G I,(x+y+z)+(u+v+w)=(x+u)+(y+v)+(z+w) from fun x y z u v w=> by abel]; exact EventuallyEq.add (EventuallyEq.add hx hy) (seals_plus μ (funded_b μ X Y A hA hF) (funded_b μ X Y A hA hH))
end
end Triangle
end YM.MS.ScaleForest
