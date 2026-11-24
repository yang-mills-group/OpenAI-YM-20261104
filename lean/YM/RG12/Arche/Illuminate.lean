import YM.RG12.Arche.Strict
/-!
# Uniform error on the full matrix (incl null letters), leading
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Arche
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open MergeProof Analysis Next.UVStress Climb Ward MergeProof.East
variable {G:Gauge}{C:Family G}{ϕ : Filter UVIndex}{l:Filter UVIndex}[l.NeBot] {M:∀ d, ℕ→RepChart C d}
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
variable (ax:Axis) (i₀ N₀:ℕ) (hN:0<N₀)(hi:0 < i₀)(hn:2≤n)
open Shapes YM.RG12.Desk.Paired
-- actual mixed calibrated reflected test (can use different horizons in slots), at
-- the chosen length but no dilation on fields.
def illumination (S : Table C.book)(H : S.RealSpin)(d e : ℕ) (a:Axis)(N:ℕ)(s:ℝ) : S.Field d→ₗ[ℂ] (S.Field e→ₛₗ[starRingEnd ℂ] ℂ) :=
  (paired S d e (compass a (N:ℝ)⁻¹ s)).compl₂ (S.adj H e a)

def lamp (C:Family G)(N k:ℕ)(μ:ℝ):ℝ:=C.S.a k * ticks N μ

def glowH {S : Table C.book}(M : ∀ d,ℕ→RepChart C d) (k:ℕ)(r:Module.End ℂ (C.label d)) : C.label d→ₗ[ℂ] S.Field d := (S.project d).comp (aligned C M k r)

lemma mass_adj (C : Family G)(d:ℕ)(a:Axis) : ∃ K:ℝ,0 ≤ K∧ ∀ v:C.label d,
    mass C d (C.book.adj d a v) ≤ K*mass C d v:=by
  let H : Module.End ℂ (C.label d):= (C.labels.level d).act (Signed.reflect a)
  let z:= ‖(LinearMap.toContinuousLinearMap H)‖
  let m:= ((C.labels.level d).extra+1:ℝ)
  refine ⟨m*z,by dsimp only [m,z]; positivity,fun u=>?_⟩
  have h: ‖star u‖ ≤ mass C _ u:= by rw [norm_star]; exact norm_le_mass ..
  calc
    _ ≤ m * ‖C.book.adj d a u‖ := by unfold m; simpa using mass_le_norm C d (C.book.adj d a u)
    _ ≤ m * (z*mass C _ u):=mul_le_mul_of_nonneg_left (((LinearMap.toContinuousLinearMap H).le_opNorm (star u)).trans (mul_le_mul_of_nonneg_left h (norm_nonneg _))) (by unfold m; positivity)
    _ = _:=by rw [mul_assoc]

include F hQ hb H h hp hZ hN hn hi
set_option maxHeartbeats 500000 in
lemma surface :∃ c:ℝ,0 ≤ c ∧ ∀ᶠ k in atTop,∀ T: ℕ→ℕ→TableL C D,Poised P B H O J n z k T→
      ∀ (Z:∀ i:Fin (D+1),Module.End ℂ (C.label i)), let μ:= mag A a! k; let y:= Shapes.ratio N₀ μ*i₀
      Comparer (ϕ:=ϕ) (hC:=H) l k D T μ Z→∀ (j i:Fin (D+1))(v:C.label j)(w:C.label i),
      let t:= lamp C N₀ k μ; ‖illumination _ F.room.kernel.spin j i ax N₀ (t*i₀) (glowH M k (Z j) v) (glowH M k (Z i) w)-
        polished C.labels j i ax (N₀:ℝ)⁻¹ y ((F!).project j v) ((F!).project i w)‖ ≤ c* Ship.budget A n k*mass C j v*mass C i w:=by
    obtain ⟨hR,hD⟩:= thicket ax N₀ i₀
    have ha: 0 < a! := by have hf:=(P index).huge; linarith [Nat.cast_nonneg (α:=ℝ) D]
    obtain ⟨c,hc,hM⟩:=lamps (l:=l) P B H h hp O J z hZ index F.room.generic (Maxwell.table_smooth _) F.room.kernel.laws.toSymmetric hQ hb hR hD hn
    choose V hV H₀ using fun i:Fin (D+1)=>mass_adj C i ax
    let K:=∑ i, V i; have hK:0≤K:=sum_nonneg fun _ _=>hV _
    have hy i: V i≤K:=single_le_sum (fun j _=>hV j) (mem_univ i)
    refine ⟨c*K,mul_nonneg hc hK,?_⟩
    filter_upwards [hM,(Next.Rank.Station.mag_rate (A) h ha).eventually_ge_atTop N₀] with k hk hh T hT Z μ y he j i v w t
    let q:= berth ax N₀ i₀ μ; let sig:= C.book.adj i ax; obtain ⟨hR,hS⟩:= still_tree ax N₀ i₀ μ hN hi hh
    let D':= aligned C M k (Z i)
    have h1 : (F!).adj (Extra.FD.table_spin C.labels) i ax ((F!).project i w)=(F!).project i (sig w):= rfl
    have ha : S.adj F.room.kernel.spin i ax (S.project i (D' w))= S.project i (D' (sig w)):=by
       change S.project i ((C.labels.level i).act (Signed.reflect ax) (star (D' w)))= _
       have h1:= star_aligned hQ he hT.charts i w (hT.early _ i.is_le)
       have h2:= acts_aligned hQ he hT.charts i (Signed.mirror ax) (star w) (hT.early _ i.is_le)
       rw [← show D' (star w)=star (D' w) from h1, ← show D' _=(C.labels.level i).act (Signed.reflect ax) (D' (star w)) from h2]; rfl
    have hUp:= hk T hT Z he q hR hS j i v (sig w)
    have hc' : 0≤ c*Ship.budget (A) n k*mass C j v:= mul_nonneg (mul_nonneg hc (Ship.budget_pos ..).le) (mass_nonneg ..)
    unfold illumination polished; simp only [LinearMap.compl₂_apply]; rw [show glowH M k (Z i) w=S.project i (D' w) from rfl, ha,h1,pair_at,pair_at,Shapes.scaling,show t= C.S.a k*ticks N₀ μ from rfl, ← gears _ _ _ _ _ _ hN,Shapes.scaling,show y=Shapes.ratio N₀ μ *i₀ from rfl, ← dated _ _ _ _ hN] -- args y & t opaque
    exact hUp.trans ((mul_le_mul_of_nonneg_left ((H₀ i w).trans (mul_le_mul_of_nonneg_right (hy i) (mass_nonneg ..))) hc').trans_eq (by ring))
end YM.RG12.Arche
