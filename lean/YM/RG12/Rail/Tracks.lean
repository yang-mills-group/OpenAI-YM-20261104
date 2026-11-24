import YM.RG12.Rail.LampR
/-! Moving lengths sampled at actual axis-aligned joint positions. Exact s to t conversion,
    no interpolation between physical grids or extra occlusion assumptions. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Rail
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open MergeProof Analysis Next.UVStress Climb Ward MergeProof.East Arche Shapes Roof
variable {G:Gauge}{C:Family G}{ϕ : Filter UVIndex}[ϕ.NeBot]{l:Filter UVIndex}[l.NeBot] {M:∀ d, ℕ→RepChart C d}
  {d e n D k N p m:ℕ}
  {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ β δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (P:ι → Tapes.Panel D) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ β δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
local notation "F!"=> standard C
variable (z:ℝ) (hZ : ∀ i≤D,MergeProof.Accent.generator G i≤ z) (index:ι)
set_option quotPrecheck false
local notation "a!"=> (P index).arc
local notation "κ" k:max=> C.S.a k
variable {S : Table C.book} {f: Extraction.Order}(F:Final C f S)(hQ:Observing C H ϕ M)(hb:ϕ ≤ f.fuse)
variable (ax:Axis) (N₀:ℕ) (hN:0<N₀)(hn:2≤n)
-- map (n= number rungs) to exact lattice multiple spacing & test geometry
private def lined (a:Axis)(N v:ℕ): Fin 2→ Cover:= ![fun i=> if i=a then (v*N:ℤ) else 0,fun i=> if i=a then -(v*N:ℤ) else (v:ℤ)]
private lemma arrived (a:Axis)(N v:ℕ)(μ:ℝ)(hN:0<N): tag μ (lined a N v) = (μ*(v*N:ℕ)) • bearing a (N:ℝ)⁻¹:=by
   have ht:0<(N:ℝ):=Nat.cast_pos.mpr hN
   rw [← Shapes.scaling]; ext j i; fin_cases j
   · change _=compass _ _ _ 0 i;rw [Arche.Shapes.front]
     change μ*((↑(if i=a then (v*N:ℤ) else 0):ℝ))=_; split
     · push_cast; rfl
     norm_num
   change _=compass _ _ _ 1 i;rw [rear]
   change μ*((↑(if i=a then -(v*N:ℤ) else v):ℝ))=_; split
   · push_cast; ring
   push_cast; field_simp
private lemma lining (C:Family G)(a:Axis)(N n k:ℕ)(hN:0<N): Extraction.Order.grid C k (lined a N n)=(C.S.a k*(n*N:ℕ)) • bearing a (N:ℝ)⁻¹:=arrived _ _ _ _ hN

include F hQ hb H h hp hZ hN hn
omit [Fintype ι] [ϕ.NeBot] in
lemma lightR :∃ c:ℝ,0 ≤ c ∧ ∀ᶠ k in atTop,∀ T: ℕ→ℕ→TableL C D,Poised P B H O J n z k T→
      ∀ (Z:∀ i:Fin (D+1),Module.End ℂ (C.label i)), let μ:= mag A a! k
      Comparer (ϕ:=ϕ) (hC:=H) l k D T μ Z→∀ m:ℕ, let x:ℝ:= (m*N₀:ℕ); let y:=μ⁻¹*x; y∈Icc 1 ((A).clock.monitor k)→ CastH F D ax N₀ (c * Ship.budget A n k) ((κ k)*x) y M k Z:=by
    -- full Ray input. growing layout. mass charges on adj etc ONLY, no opening of slips/captures.
    let C₀:= bearing ax (N₀:ℝ)⁻¹; have hu: C₀∈conf 2:=opens ax _ 1 zero_lt_one
    obtain ⟨c,hc,hM⟩:=rails (l:=l) P B H h hp O J z hZ index F.room.generic F.room.kernel.laws.toSymmetric hQ hb hu hn
    choose V hV H₀ using fun i:Fin (D+1)=>mass_adj C i ax
    let K:=∑ i,V i; have hK:0≤K:=sum_nonneg fun _ _=>hV _
    have hy i:V i≤K:=single_le_sum (fun j _=>hV j) (mem_univ i)
    refine ⟨c*K,mul_nonneg hc hK,?_⟩
    filter_upwards [hM] with k hk T hT Z μ he m x y hh j i v w
    let q:= lined ax N₀ m; let sig:= C.book.adj i ax
    have hr:=arrived ax N₀ m μ⁻¹ hN;change tag μ⁻¹ q=y • C₀ at hr
    have hR: Anemos C₀ ((A).clock.monitor k) (tag μ⁻¹ q):=⟨_,hh,hr⟩
    have hY:=zero_lt_one.trans_le hh.1
    have hS : tag μ⁻¹ q ∈ generic _:= by
        rw [hr,← Shapes.scaling]; exact all_directions ax _ _ hY (inv_ne_zero (Nat.cast_pos (α:=ℝ)|>.mpr hN).ne')
    let D':= aligned C M k (Z i)
    have h1 : (F!).adj (Extra.FD.table_spin C.labels) i ax ((F!).project i w)=(F!).project i (sig w):= rfl
    have ha : S.adj F.room.kernel.spin i ax (S.project i (D' w))= S.project i (D' (sig w)):=by
       change S.project i ((C.labels.level i).act (Signed.reflect ax) (star (D' w)))= _
       have h1:= star_aligned hQ he hT.charts i w (hT.early _ i.is_le)
       have h2:= acts_aligned hQ he hT.charts i (Signed.mirror ax) (star w) (hT.early _ i.is_le)
       rw [← show D' (star w)=star (D' w) from h1, ← show D' _=(C.labels.level i).act (Signed.reflect ax) (D' (star w)) from h2]; rfl
    have hUp:= hk T hT Z he q hR hS j i v (sig w)
    have hc': 0 ≤ c*Ship.budget (A) n k*mass C j v:=mul_nonneg (mul_nonneg hc (Ship.budget_pos ..).le) (mass_nonneg ..)
    unfold illumination polished; simp only [LinearMap.compl₂_apply]; rw [show glowH M k (Z i) w=S.project i (D' w) from rfl, ha,h1,pair_at,pair_at,Shapes.scaling,show x=(↑(m*N₀):ℝ) from rfl,← lining _ _ _ _ _ hN,Shapes.scaling, ← hr]
    exact hUp.trans ((mul_le_mul_of_nonneg_left ((H₀ i w).trans (mul_le_mul_of_nonneg_right (hy i) (mass_nonneg ..))) hc').trans_eq (by ring))
end YM.RG12.Rail
