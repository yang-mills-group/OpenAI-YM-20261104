import YM.OPE.Compatible.Lady.Fling
/-! # pan book scales before accepting. interior selection -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lass
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*}{j i k m n B:ℕ}{R v t s u r:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Borealis Borealis.Galea Borealis.Lav
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:Host K T}(o:Site L.c)
abbrev rink (o: Site L.c):Site L.f:= L.Z.ratio.embed o
abbrev Ξ (L:Host K T)(x:Site L.f)(k:ℕ):= seatB L.ForestQ (roomB x k)
-- canopy geometry
lemma groveV (x:Site L.f)(m:ℕ): Training (G:=G) L x (Crown.crux L.Z L.H x m) (4*m):=by
       intro i hi; obtain ⟨w,hp⟩:= (mem_filter.mp hi).2; change (separation x i.1.val.1:ℝ) ≤ 4*m; rw [hp]; exact_mod_cast ((doors ..).mp (mem_filter.mp w.property).2.1)
lemma groveT (x:Site L.f)(m:ℕ)(h:m+8≤n): pledgesF (Spindle.patch m x) (Ξ L x n):=fun _ hi=>mem_filter.mpr ⟨mem_univ _, (Corona.halo_mono (show 8+m ≤ n by omega) (Finset.Subset.refl _) (haloY 8 m _ (Next.Scheduling.flag_layer _ hi)))⟩
variable (t:ℕ)(q:Bid.Dir G L.c)(Z:Seats L.ForestQ) (y:AxisChart G L.ForestQ)
variable (p: Support L.f)
abbrev Brite (x:Site L.f)(q: Bid.Dir G L.c)(B:ℕ):Prop:=∀ i:Body 1 L.c, L.Z.ratio.embed i.1∉roomB x B → q i=0
variable (d N:ℕ)
noncomputable abbrev burnS (o:Site L.c)(d N:ℕ)(q:Bid.Dir G L.c)(y:AxisChart G L.ForestQ):Studio L:= ⟨Ξ L (rink o) d,q,y,roomB (rink o) N⟩
include d N
lemma Rootq (ℓ:ℕ)(hh:64*ℓ≤d): ReserveQ L (rink o) (burnS o d N q y) q ℓ:=by
       refine ⟨fun i hi=> Finset.mem_filter.mpr ⟨mem_univ _,?_⟩,fun _ _=>rfl⟩; change i.1.val.1∈halo _ _; have he: separation (rink o) i.1.val.1 ≤64*ℓ:=(by exact_mod_cast hi); exact halo_spec.mpr ⟨_,mem_singleton_self _,he.trans hh⟩
lemma Coverq (he:Brite (L:=L) (rink o) q B) (h:d≤ N) (hY:B≤N)(hv:∀ i∉ Ξ L (rink o) N, y i=0) : ∀ x:(burnS o d N q y).St,Dew.ShadeQ L.Z L.ForestQ ((burnS o d N q y).V x) (roomB (rink o) N):=by
       intro x; refine ⟨fun i hi=> he i (fun H=>hi (Corona.halo_mono hY (Finset.Subset.refl _) H)),fun i hi=>?_⟩; let f:= Ξ L (rink o); change y i+stake (f d) x i=0; rw [hv _ (fun h=>hi (Finset.mem_filter.mp h).2),stake_off (f d) x i (fun hz=>hi (Corona.halo_mono h (Finset.Subset.refl _) (Finset.mem_filter.mp hz).2)), zero_add]
omit d N
lemma TSpot (x:Site L.f)(q: Bid.Dir G L.c)(n:ℕ): Brite (L:=L) x (Qspot L x n q) (64*n):=by
       intro j hj; apply Q_off; intro hi; exact hj (halo_spec.mpr ⟨x,mem_singleton_self _,(Push.AbsoluteSums.Animals.neighbors_mem ..).mp (mem_filter.mp hi).2⟩)
end
end YM.OPE.Lass
