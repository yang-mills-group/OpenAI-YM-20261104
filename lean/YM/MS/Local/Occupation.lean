import YM.MS.Local.Harmony
import YM.MS.Local.Recovery

set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.BV
open Function Filter Set Finset Plane Koszul Real Momentum Tensor Submodule MatrixLet
open Landau Detect
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge} {f: Grade G} {F: Law G} {h q H x y a b c: ℤ} {V A: Mover G} {r: ℕ}
namespace Woven
abbrev Bed (G : Gauge):= tile (A:=Branch G Axis) FourP mslug ghostNo
lemma loom_eq (G:Gauge) (h q:ℤ) (r:ℕ) : Bed G h q r=Loom (A:=Branch G Axis) (Momentum Axis) (w:=mslug) (c:=ghostNo) h q r:= tile_eq mslug ghostNo h q r
lemma planting (hv:f∈ yields a b) (hF:F∈Bed G x y r): bud f F∈Bed G (a+x) (b+y) (r+1):= tileCub.mpr (enters (seedStar.mp hv) (tileCub.mp hF))
lemma compose_line {F:Fin r→ Grade G} (hv : line r F≠0) (i:Fin r): F i≠0:= by
   intro he; apply hv
   ext l; by_cases h : l.length=r; swap; exact line_rank F h; obtain ⟨p,q,rfl⟩:= discovered l h; rw [line_gaze]; exact Finset.prod_eq_zero (mem_univ i) (by rw [he]; rfl)
lemma bed_le (X : Submodule ℂ (Law G)) (hp : ∀ (f : Fin r→ Grade G) (u v : Fin r→ℤ), (∀ i,f i∈ yields (u i) (v i)) → (∑ i, u i)=h → (∑ i,v i)=q → (∀ i,0≤u i) → line r f∈X) : Bed G h q r ≤ X:= by
   rw [loom_eq,Loom,span_le]; rintro _ ⟨p,x,y,H,hx,hy,rfl⟩
   by_cases ht : line r p=0; rw [ht]; exact zero_mem _
   exact hp p x y (fun i=> seedStar.mpr (H i)) hx hy fun i=> (canbe (seedStar.mpr (H i)) (compose_line ht i)).1
lemma parity_bud (hv:f∈ yields a b) : V.Q (bud f F) =bud (MatrixLet.one V f) F+(cross true (Local.parity b):ℂ) • bud f (V.Q F):= exact_at _ _ _ (par_seed hv)
end Woven
end YM.MS.Local.BV
