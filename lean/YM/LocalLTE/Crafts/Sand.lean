import YM.LocalLTE.Crafts.Keel
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
-- Variance at PRE for all.Cut.
open RG.Shoot Averaging
variable (K: Set ℝ) (g:ℝ→Source G n) {x₀:ℝ}(hK:x₀∈K){f w:ℝ→ℝ} (hq: ∀ x∈K, Local X p (g x) (f x) (w x)) (hh:Compared X p g K)
local notation "𝒪" => 𝓝[K] x₀
include hn hG hR hd hq hh hK hv
variable (α:ℝ)(M:ℕ)(F:ℝ→ ℕ→ EKey n→ Pot G n) (hF:∀ j≤M,∀ x∈K,∀ v:ℝ, 0<v→∀ᶠ y in 𝓝[K] x, Stocked p (Price.tubeX R p X) (F x j-F y j) v)
set_option quotPrecheck false
local notation "T" y=> azures c p R X (g y) M (delta (X.read (g y))) α (F y)
local notation "Z" y=> silt c R X (g y) M (delta (X.read (g y))) α (F y)
local notation "X₀"=> bells p R X M
local notation "V"=> Price.tubeX R p X
include hF
lemma sand_at (v:ℝ)(he:0<v) : ∀ᶠ y in 𝒪, Stocked p (sands p R X M) ((Z x₀)-Z y) (↑ (Fintype.card (Fin (M+2)))*v):= by
    let e:=v/2
    have h' (i:Fin (M+2)) (a:ℝ) (z:ℝ) : (fun k=> ((Z a) -Z z) (i,k)) =(if i.val=M+1 then archive X R c (g a) α (delta (X.read (g a)))-archive X R c (g z) α (delta (X.read (g z)))-(F a M-F z M) else if i.val=0 then F a 0-F z 0 else F a i.val-F z i.val-(F a (i.val-1)-F z (i.val-1))) := by
       funext k; simp only [Pi.sub_apply]; unfold silt stairs; split_ifs <;> simp only [Pi.sub_apply] <;> abel
    filter_upwards [(eventually_all_finset (Finset.range (M+1))).mpr (fun i h=>hF i (by apply Nat.le_of_lt_succ; exact mem_range.mp h) x₀ hK e (half_pos he)), Price.viewU hR hv hG hn hd X K g hK hq hh e (half_pos he) α] with y hy hV -- order
    have h (i: Fin (M+2)): Stocked p V (fun k=> ((Z x₀)-Z y) (i,k)) v:=by
       rw [h']; split
       · exact (hV.minus (hy M (mem_range.mpr (by omega)))).cheaper ((add_halves v).le)
       split
       · exact (hy 0 (mem_range.mpr (by omega))).cheaper ((half_lt_self he).le)
       exact ((hy i.val (mem_range.mpr (by omega))).minus (hy (i.val-1) (mem_range.mpr (by omega)))).cheaper ((add_halves v).le)
    choose f h hF using h; exact ⟨fun i=> f i.1 i.2,fun i=>h _ _,fun i=>Cost.product (Cost.finite _ he.le) fun j=> hF j i⟩
lemma torque (v:ℝ)(he:0<v) : ∀ᶠ y in 𝒪, Stocked p (X₀|>.reg) ((T x₀).regular-(T y).regular) v:=by
    let t:= turnFee p; let u:ℝ:= Fintype.card (Fin (M+2)); have ht':0<t*u:= mul_pos (turnFee_pos _) (by unfold u; positivity)
    let e:=v/(t*u)
    filter_upwards [Price.sand_at hR hv hG hn hd X K g hK hq hh α M F hF e (div_pos he ht')] with y hy
    obtain ⟨f,h,hM⟩:= hy.rotation; let w:=numbering (Rol M n); let Q:= Song.choir ((Z x₀)-Z y)
    have hx : (T x₀).regular-(T y).regular=Q∘ w:= by
       funext i; let a:= w i; change Song.Rim n•((Z x₀) a.2∘a.1.view)-Song.Rim n•((Z y) a.2 ∘ a.1.view)=_
       rw [← smul_sub]; rfl
    have ht:turnFee p*(u*e)=v:= mul_assoc _ _ _|>.symm.trans (Eq.trans (mul_comm _ e) (div_mul_cancel₀ v ht'.ne')) -- edit
    rw [hx]; refine ⟨f ∘ w,fun i=>h (w i),fun i=>(budget_loosen (Cost.equiv w (hM i)) ht.le)⟩ -- dependent rw
end YM.AnalyticBridge.VerifiedReset.Collection.Price
