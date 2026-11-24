import YM.RGLocalTaylor.Post.Lease
import YM.RGLocalTaylor.Post.Law
/-!
# Reuse the same hard actors with the Taylor families

At this pre-reset stage and again after resetting, the whole forced support,
inventory and tests stay fixed; the numbers themselves stay the true K. The
forest gauge covariance for modeled E stems needs to respect the actual orbit
conventions. A family retaining its rebuilt constellation cannot assume some
other witness took the same perm, but can compose in the vacuum Moves criterion
when reconstituting one circulation; we prove for the advertised integrated
E model and error here. No assertion of subsequent marker insertion snooping
on those rows separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Post
open Function Filter Set Lattice Wilson RG RG.Shoot Ovens Ovens.Pipes
open AnalyticBridge VerifiedReset Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open PhysicalNext PhysicalNext.Repeat Collection Extra.Iteration Song Refrain Geo Quotes
open Residual WilsonStartup Averaging Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open UVNext.CouplingReset Input
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

section reusable
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint}
    {X : Listing G n} {v a : Collection.Source G n} {σ C Λ α Δ u w e t : ℝ}
open RGLocalTaylor.Read
namespace Anchor
variable {A V W: Activities G n}
lemma impart (f : ℕ → Config G n→ℝ) {s : Signed} {x:Site n} (h : Nonempty (A.Moves s x)) (hp : Nonempty (V.Moves s x))
    (hb:A.reg=W.reg) (he: A.E=W.E) (hK:V.K=f)(hk:W.K=f)(hV:V.forced=W.forced): Nonempty (W.Moves s x):= by
  obtain ⟨x',w',y,z,_,_,_,u',v⟩:=h; obtain ⟨xx,w,_,_,u,M,h,v,v'⟩:=hp
  refine ⟨⟨x',w,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · rw [← hb]; exact y
  · rw [← hb]; exact z
  · rw [←hV]; exact u
  · rw [←hV]; exact M
  · rw [←hV]; exact h
  · rw [←he]; exact u'
  rw [hk, ←hK]; exact v'
lemma replicate (F : ℕ → Config G n→ℝ) (s : Signed)(b:Site n) (g:G.Simple) (h : Collection.Local X p v u w)(hx : R.Bounds c σ C Λ)
    (hc:WilsonStartup.Decent c p)(hn:20<n.val) (ha:A.reg=(drawer G n).reg)(he:A.K=F) (hu:Nonempty (A.Moves s b))(α:ℝ) :
    Nonempty (({A with E:=central R c p X v α}:Activities G n).Moves s b):= by
  let Z:= X
  let f:= Rack.widen (shelves Z R p) (branch Z R c p v α)
  let Y:= (drawer G n).pours f
  have hM := (h.fittings g hx hc hn α (Averaging.delta (Z.read v))).moves
  exact impart F (show Nonempty (Y.Moves s b) from ⟨on_shelves (hM s b|>.some)⟩) hu ha.symm rfl he he rfl
lemma civilized (hm:a.hardRead=v.hardRead)(hg:∀ s b,Nonempty ((X.read a).Moves s b))
    (ha : orient p X.reg a.logRead u)(h : Collection.Local X p v t w) : Collection.Local X p a u w:= by
  rcases h with ⟨_,⟨hs,hK,hX,hT,hr,hM,hv⟩,_,_,hv'⟩; obtain ⟨f,hf,hw⟩:=ha
  refine ⟨fun i=>(hw i).1,?_,hg,⟨f,fun i=>(hw i).2,hf⟩,?_⟩
  · unfold Listing.read; rw [hm]; exact ⟨hs,hK,hX,hT,hr,hM,hv⟩
  rw [hm]; exact hv'
end Anchor
end reusable
end YM.RGLocalTaylor.Post
