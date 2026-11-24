import YM.LocalLTE.Port.Panels
import YM.LocalLTE.Quartz.Tapes
/-! # contracting analytic generations while preserving their own leases. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Set Lattice RG Pressure Wilson Finset MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus FrameBox Cabana Push
open Progress.DirectedRecipe MergeProof Menu Marker Accent Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}{c f : Side}{Q : Rep G f} {S:StepData c f} {σ κ Λ μ' w t v : ℝ}
variable {V I J : Type}[DecidableEq V][Fintype V] {R:Marker.Census V}(B:Bands R Q)(r:V→ℝ) (hr:∀ i,0<r i) (o:V→Site f)
open Extra.Trajectories Next.Foundations
variable {d U:ℕ}
local notation "P"=> Q.p
local notation "ν" => Q.p.threshold
local notation "W₀"=> Config G f
-- assume prepared.Count.All.Nonempty.Site.Real.Anchor.Remnant.L.
variable {a₀ c₁ a β:ℝ} -- fix
variable (h:B.Active)(hw:B.Radial r a₀ a v c₁)
open Push.AbsoluteSums Push.AbsoluteSums.Animals
-- route. Ticket inherited all known Geometric.Bounds. 'stored polynomial' besides displayed.F.Same for both colour projections.
structure Shine (R:Marker.Census V)(B:Overlay.Bands R Q)(d U:ℕ)(κ:ℝ) : Prop where
   legacy (i:ℕ) : B.H i≠0→ ∃ x∈ B.support i,B.support i⊆neighbors U x∧ ∃ h≤ U,∃ X:Grove x,∀ k:Bool,∃ S:Pkt (Directions G f) (d+1), scaleQ k ∘ (B.H i) = polymer X h (d+1) κ S
-- hit to any specified anchor.Nonmark legacy.Point.
abbrev Stellar (f:Side)(n:ℕ) := Σ o:Site f,Grove o × Fin (n+1)
abbrev Outpost (R: Marker.Census V)(f:Side)(U:ℕ) := (R.Mode × Support f) × Stellar f U

section finite
instance {o:Site f}: Finite (Grove o):=by
   let t (X:Grove o) := (X.parent,X.link)
   have he:Injective t:=by intro x y h; cases x; cases y; unfold t at h; cases h; rfl
   -- finite Dependent Pi
   haveI : Finite Lattice.Step := Finite.of_injective (fun i : Lattice.Step => (i.dir,i.neg)) (by rintro ⟨a,b⟩ ⟨c,d⟩ h; cases Prod.mk.inj h; congr)
   exact Finite.of_injective t he
instance (o:Site f): Fintype (Grove o):= Fintype.ofFinite _
instance (f:Side)(n:ℕ): Fintype (Stellar f n):=by unfold Stellar; infer_instance
instance (R: Marker.Census V) (f:Side)(U:ℕ): Fintype (Outpost R f U):=by unfold Outpost; infer_instance
end finite
-- need unpack: use abbrev
local notation "Θ"=> Outpost R f U
def Land (O:V→Site f)(p:Outpost R f U) : Prop:= p.1.1.val.Nonempty ∧ p.1.1.val.image O ⊆ p.1.2 ∧ p.2.1∈ p.1.2 ∧ p.1.2⊆neighbors U p.2.1
abbrev HarborP (B:Overlay.Bands R Q)(U:ℕ):= {p:Outpost R f U // Land B.origins p}
abbrev FamilyE (B: Bands R Q):= {i:ℕ// B.H i≠0}
-- composite definitions transparent for root splitting.
local notation "TP" => HarborP B U
local notation "TT"=> FamilyE B
variable (hc:Shine R B d U κ)
abbrev pedestal (z:HarborP B U) : RegularAddress f := ⟨z.val.2.1,z.val.1.2,z.property.2.2.1⟩
include hc h
omit [Fintype V] in
lemma guideL : ∃ F:FamilyE B → HarborP B U, ∀ i,let p:=F i; B.support i.val=p.val.1.2 ∧ B.rays i.val=p.val.1.1∧ ∀ k:Bool,∃ S, scaleQ k ∘ (B.H i.val) =polymer p.val.2.2.1 p.val.2.2.2.val (d+1) κ S:=by
    choose z hz hU t' ht V hV using fun i:FamilyE B=> hc.legacy i.val i.2
    refine ⟨fun i=> ⟨((B.rays i.val,B.support i.val),⟨z i,V i, ⟨t' i,Nat.lt_add_one_of_le (ht i)⟩⟩),?_,?_,hz i,hU i⟩,fun i=> ⟨rfl,rfl,hV i⟩⟩
    · exact h.proper _
    intro j hj; obtain ⟨k,hk,rfl⟩:=mem_image.mp hj; exact h.pins _ _ hk
-- ticket at x needs rebased charges.ActU.small.One.Warning when rows trimmed small. For output carry.S.Margin.Step.Vol.
omit hc
variable (u:I→ℝ)
-- Σ f_Budget via reanchor.S.(P). Poly.rSO.
variable (Y:FamilyE B → HarborP B U)(hk:∀ i:FamilyE B,B.support i.val=(pedestal B (Y i)).support∧ B.rays i.val=((Y i).val.1.1))
local notation "z" i=> pedestal B (Y i)
include h hw hk
local notation "W'"=> (1+(U:ℝ))^(Q.p.power*Q.p.order)
lemma axels : ∃ b:FamilyE B→ ℝ,(∀ i,(∀ k:Bool,(P).Regular (pedestal B (Y i)).support (scaleQ k ∘ (B.H i.val)) ∧ (P).supBounds (pedestal B (Y i)).site (pedestal B (Y i)).support (scaleQ k ∘ (B.H i.val)) (b i)) ∧ Q.p.supBounds ((pedestal B (Y i)).site) (pedestal B (Y i)).support (B.H i.val) (2*b i)) ∧
    SumBudget (fun i:FamilyE B=> Poly.toll r ((Y i).val.1.1) *Q.p.mass ((pedestal B (Y i)).support) (b i)) ( ((1+(U:ℝ))^(Q.p.power*Q.p.order)) * (((Fintype.card V):ℝ)*a)):=by
    obtain ⟨b,hb,hB⟩:= hw.bulk; let z':=fun i=> Y i; let b' i:= W' * b i
    have hf (i):0≤ b' i:= mul_nonneg (by positivity) (hb i|>.1)
    refine ⟨fun i=> b' i.val, fun i=>?_,?_⟩
    · obtain ⟨p,hp⟩:= h.proper i.val
      let P':= Q.p; let x:=(pedestal B (Y i)).site; let X:=(pedestal B (Y i)).support
      let G0:=B.H i.val; have hz:P'.Regular X G0:=  (show B.support i.val=X from (hk i).1) ▸ h.regular i.val
      have ha:1+(separation (B.origins p) x:ℝ) ≤ 1+ (U:ℝ):= by
         refine add_le_add_right (Nat.cast_le.mpr ?_) _; rw [separation_comm]; exact (neighbors_mem ..).1 ((Y i).property.2.2.2 ((show B.support i.val=(Y i).val.1.2 from (hk i).1) ▸ (h.pins _ _ hp)))
      have he k:= Fan.spokeR P' ha ((Port.framesV (h.regular _) ((hb _).2 p hp) k).2) -- yes edit
      have H k:P'.supBounds x X (scaleQ k ∘ B.H i.val) (b' i.val):=  (show B.support i.val=X from (hk i).1) ▸ he k
      constructor; · exact fun k=> ⟨ (hk i|>.1) ▸ (Port.framesV (h.regular _) ((hb _).2 p hp) k).1,H k⟩
      refine ⟨mul_nonneg zero_le_two (hf _),fun u hu l hl hd=>?_⟩
      let v:=leftDerivs G0 l u; have ht(k:Bool): ‖(↑(scaleQ k v):ℂ)*ink k‖ ≤ b' i.val :=by rw [norm_mul,tintX,mul_one,Complex.norm_real]; rw [show scaleQ k v= _ from (Push.Local.left_linear _ _ (hz.smooth u hu) hl).symm]; exact (H k).2 u hu l hl hd
      change ‖v‖ ≤ _; rw [← harvestQ v]; exact (norm_sum_le ..).trans ((sum_le_sum fun k _=> ht k).trans_eq (by simp))
    let f i:=Marker.Poly.toll r (B.rays i) * (P).mass (B.support i) (b i)
    have hd(i):0≤ f i:=mul_nonneg ((Poly.worth hw.pure _).le) (mul_nonneg (Real.exp_nonneg _) (hb i|>.1))
    convert! budget_scale (show 0≤W' by positivity) (budget_pull _ Subtype.val_injective (Overlay.per_system hd h.proper hB)) using 1
    ext i
    try unfold f; rw [(hk i).1,(hk i).2]; unfold b' BudgetPoint.mass; ring
end YM.LocalLTE.Port
