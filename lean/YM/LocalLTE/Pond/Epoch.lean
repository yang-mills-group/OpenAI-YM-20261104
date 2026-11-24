import YM.LocalLTE.Pond.Beta
import YM.LocalLTE.Rate.Permit
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes
variable {G}
open Extra.Iteration Urns
variable {t σ C' Λ Δ α k κ a v w u:ℝ} {c:Clip} {L:Side} {p:BudgetPoint} {d N:ℕ}
variable {R:PathData G}(hR:R.Bounds c σ C' Λ) (hv : Width p c σ)(hG:G.Simple)(hn:20<n.val)(hg:32*p.B<n.val) (ht:p.B=Pressure.radiusB t) (hC:p.threshold=Pressure.temp t) (he:p.threshold ≤2*Pressure.fiery G t L)(hx:1 ≤ betaF G t L) (hb:3 ≤ p.B)(hk:Reliable G κ k) (hd:WilsonStartup.Decent c p)
-- Numerics.After.D.D F.bore universe all.Current.True accuracy.
variable (X:Listing G n) (g:Source G n) (P0:ℕ→Pot G n)(V:Tour X d)
open East Averaging Song Refrain Ovens Payments Rack Ovens.Pipes
variable {M:ℕ}(α Δ:ℝ)(F:ℕ→ EKey n→ Pot G n)
local notation "t₀"=> bells p R X M
local notation "t₁"=> azures c p R X g M Δ α F
local notation "g₁"=> Collection.fill X R c p g α Δ
local notation "E" => Price.tubeX R p X
variable {β C₀:ℝ}
variable (hxβ:1 ≤ β) (h:∀ i: Fin (M+2), Stocked p (Price.tubeX R p X) (fun k=> Price.silt c R X g M Δ α F (i,k)) (C₀*β^(chip i.val)))
include h hxβ
variable (e v u:ℝ)
-- universal newborn index. use for ALL reps.Furnished on honest.Budget.Finiteness
abbrev grade (n:Side)(j:ℕ)(i:ℕ):ℕ:= match (regularKeys n i).2 with
    | Sum.inl i=> pocket n j i
    | .inr _=> j+1
local notation "E₀"=> finish R c p t₀ t₁ u v
lemma gathers (ht: Price.bars p M C₀ β ≤ e): Raw.Pumps (E₀) (fun i=> bloom β (grade n M i)) e:=by
    let Y:=t₀; let T:=t₁; let E':=upE Y
    obtain ⟨f,H,hF⟩:= Price.voracity X g α Δ F hxβ h
    refine ⟨fun i=> East.bloom_bill hxβ _,stuff E' f,fun i=>?_,fun i=>?_⟩
    · change p.supBounds ((drawer G n).reg i).site ((drawer G n).reg i).support (stuff E' T.regular i) _
      by_cases hv:i∈Set.range E'; swap
      · rw [blank _ _ hv,blank _ _ hv]; exact VerifiedReset.sup_le (VerifiedReset.sup_const 0) abs_zero.le
      obtain ⟨i,rfl⟩:= hv; rw [stuffed,stuffed, show (drawer G n).reg (E' i)=Y.reg i from Rack.reg_up Y i]; exact H i
    refine transfer_budget E' ?_ ?_ (budget_loosen (hF i) ht)
    · intro j; have hs : ((E₀).activities.reg (E' j))=Y.reg j:= by apply Rack.reg_up Y
      rw [stuffed]; dsimp only; unfold Price.grade; simp only [E',Rack.upE,book]; unfold E' upE at hs; rw [hs]; rfl
    intro j hj; rw [blank _ _ hj,mul_zero]; simp [BudgetPoint.mass]
-- Poly syntax all grade ≤M. transfer AFTER. exact
variable (H :∀ j, j≤M → Alike (EKey n) (Price.tubeX R p X) (F j) κ (Price.gallery R p X d V hb) j d)
omit h hxβ
include H hk hb
lemma dots (i:ℕ)(hi:pocket n M i≤M) : ∃ m≤d,YM.LocalLTE.FrameBox.Polynomial m κ ((Price.bells p R X M).reg i).site (pie (Price.pocket n M i)) ((t₁).regular i) ∧ ((t₁).regular i≠0→ ((Price.bells p R X M).reg i).support⊆ neighbors d ((Price.bells p R X M).reg i).site):= by
   let T:=t₀; let g':= Price.gallery R p X d V hb; let a:=numbering (Price.Rol M n) i; let j:=a.2.1.val; let w:=a.2.2; let X':=E; let x:=X' w; let U:=T.reg i; let h:=t₁; let F':=silt c R X g M Δ α F a.2
   have ht:h.regular i=Song.Rim n • (F' ∘ Seat.view a.1):=rfl
   have he:j = pocket n M i:=rfl
   rw [← he]; change ∃ m≤d,LocalLTE.FrameBox.Polynomial m κ U.site (pie j) (h.regular i) ∧ _
   have hh:j≠ M+1:=by omega
   have ha:F'= if j=0 then F 0 w else F j w-F (j-1) w:=by unfold F' silt stairs; rw [if_neg hh]; split <;> rfl
   obtain hj|⟨t,V',hy⟩ : g' w=none ∨ ∃ t:ℕ, ∃V':Art x t,g' w=Option.some ⟨t,V'⟩:=by cases he:g' w with
      | none=> exact Or.inl rfl
      | some q=> exact Or.inr ⟨q.1,q.2,rfl⟩
   · have hv:F'=0:=by
         rw [ha]; split_ifs
         · exact (H 0 (by omega) w).1 hj
         rw [(H j (by omega) w).1 hj, (H (j-1) (by omega) w).1 hj,sub_zero]
     have ht:h.regular i=0:= by rw [ht,hv,show (0:Config G n→ℝ)∘ a.1.view=0 from rfl,smul_zero];
     refine ⟨0,Nat.zero_le _,?_,fun hp=>False.elim (hp ht)⟩; rw [ht]; exact ⟨cane U.site, Price.rp_zero (cane U.site)⟩
   -- ssh
   have hP i (hp:i≤M):= (H i hp w).2 t V' hy
   have hp:=hP j (by omega)
   have hv: Replicated V'.grove V'.radius κ (pie j+1) F':= by
       rw [ha]; split
       next hez=> rw [hez]; exact (hP 0 (by omega)).2
       next ht=> exact rp_sub V'.grove hp.2 (rp_raise V'.grove (hP (j-1) (by omega)|>.2) (by unfold pie; omega))
   let Vp:= V'.turn a.1 U rfl rfl; have hS : Replicated Vp.grove Vp.radius κ (pie j+1) (h.regular i) := by rw [ht]; exact rp_scale Vp.grove _ (Price.rotatedG V' _ a.1 U rfl rfl hk hv)
   exact ⟨Vp.radius,Vp.bonus.le.trans hp.1,⟨Vp.grove,hS⟩,fun _=>show U.support⊆neighbors d U.site from (by rw [Vp.crisp]; exact Corona.halo_mono hp.1 (Finset.Subset.refl _))⟩
include hxβ h
lemma painter (hv' : Price.bars p M C₀ β ≤ β^(chip 0)): Coup.License M E₀ κ β (Price.grade n M) d :=by
    let T:=t₁; let Y:= t₀; let Q:= E₀; let v' := Rack.upE Y; have hu:=gathers X g α Δ F hxβ h _ v u hv'
    have hx i:Q.activities.reg (v' i)= Y.reg i ∧ Q.activities.E (v' i)= T.regular i∧grade n M (v' i)= pocket n M i :=by
       refine ⟨Rack.reg_up Y i, stuffed v' T.regular i,?_⟩; unfold v' grade upE; simp only [book]
    refine ⟨hu,fun i hi=>?_,fun {i} hi hl=>?_⟩
    · by_cases he:i∈Set.range v'
      · obtain ⟨i,rfl⟩:=he; change ∃ k≤d, LocalLTE.FrameBox.Polynomial _ _ ((Q.activities.reg _).site) _ (Q.activities.E _)
        rw [(hx i).2.2,(hx i).2.1,(hx i).1]; obtain ⟨_,he,hk,_⟩:= Price.dots hb hk X g V α Δ F H i ((hx i).2.2 ▸ hi); exact ⟨_,he,hk⟩ -- order
      change ∃ k≤d, LocalLTE.FrameBox.Polynomial _ κ _ _ (Rack.widen Y T|>.regular i)
      rw [show (Rack.widen Y T).regular i=0 from blank _ _ he]; refine ⟨0,Nat.zero_le _,cane _,?_⟩
      exact Price.rp_zero _
    · by_cases hv:i∈Set.range v'; swap; · exact False.elim (hl (blank v' T.regular hv))
      obtain ⟨i,rfl⟩:=hv; obtain ⟨z,ht,hS,hx'⟩:= Price.dots hb hk X g V α Δ F H i ((hx i).2.2 ▸ hi); change (Q.activities.reg _).support ⊆ _; exact (hx i).1 ▸ hx' ((hx i).2.1 ▸ hl)
end YM.AnalyticBridge.VerifiedReset.Collection.Price
