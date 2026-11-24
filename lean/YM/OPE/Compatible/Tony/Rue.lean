import YM.OPE.Compatible.Tony.Room
/-! # Whole costume sponsors. Shifted budgets.Ph.Cartesian 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
namespace Sleeve
variable {I J:Type}{A:I→ Side}{a c:ℝ}{φ:Filter I}{Z:I→ℝ}{W:I→ℕ}
variable {p q:GlyphQ G A}{V U:Forge G A}
lemma Photos.zero : Photos φ Z a (0:GlyphQ G A):=⟨fun _=>0,RateLE.zero _ _ _,Eventually.of_forall fun _ _ _=> show ‖(0:ℝ)‖ ≤ 0 from le_of_eq (norm_zero)⟩
lemma Photos.prod (h:Photos φ Z a p)(hv:Photos φ Z c q): Photos φ Z (a+c) (p*q):=by
       obtain ⟨u,hu,H⟩:=h.cost; obtain ⟨v,hv,h⟩:=hv.cost; refine ⟨_,hu.mul hv,?_⟩; exact (H.and h).mono fun i hi x hx=> (norm_mul_le ..).trans (mul_le_mul (hi.1 _ hx) (hi.2 _ hx) (norm_nonneg _) ((norm_nonneg (p i x)).trans (hi.1 _ hx)))
structure Silks (φ:Filter I)(Z:I→ℝ)(a:ℝ)(p:Forge G A):Prop where
        marks (s:Phase): Photos φ Z a (eyeR p s)
lemma Silks.doyen {x y: Forge G A}(h:Silks φ Z a x)(hp:∀ᶠ i in φ,x i=y i): Silks φ Z a y:=by constructor; intro s; apply Photos.cone (h.marks s); filter_upwards [hp] with i hi; unfold eyeR;rw[hi]
lemma Silks.empty : Silks φ Z a (0: Forge G A):=by constructor; intro s; fin_cases s<;> exact Photos.zero
variable (h:Tendsto Z φ atTop)
include h
lemma Silks.green (hq:Silks φ Z a V)(hz:Silks φ Z a U): Silks φ Z a (V+U):=by constructor; intro s; rw [eye_add]; exact (hq.marks s).green (hz.marks s) h
lemma Silks.prod (hq:Silks φ Z a V)(hz:Silks φ Z 0 U): Silks φ Z a (V * U):=by
       have he(i j:Phase): Photos φ Z a (eyeR V i*eyeR U j):=by simpa only[add_zero] using Photos.prod (hq.marks i) (hz.marks j)
       constructor; intro i; fin_cases i; exact he 0 0; exact Photos.green (he 0 1) (he 1 0) h; exact Photos.green (Photos.green (he 0 2) (he 1 1) h) (he 2 0) h -- direction
lemma Silks.sum {U:J→ Forge G A}(s:Finset J)(hp:∀ i∈s,Silks φ Z a (U i)): Silks φ Z a (∑ i∈s,U i):=by
       induction s using Finset.induction_on with
       | empty=>rw[sum_empty]; exact Silks.empty
       | insert i s hi ih=> rw[sum_insert hi]; exact Silks.green h (hp _ (mem_insert_self ..)) (ih (fun j hj=>hp j (mem_insert_of_mem hj)))
omit h in
lemma Silks.rise (a':Phase)(hp:Silks φ Z a U): Silks φ Z a (LiftA a' U):=by
       constructor; intro s; by_cases ht:s<a'; rw[early a' s U ht]; exact Photos.zero
       have hv:a'.val ≤ s.val:= le_of_not_gt ht; let j:Phase:=⟨s.val-a'.val,by have hz:=s.isLt;omega⟩; rw[usually a' j s _ (by change s.val=s.val-a'.val+a'.val; omega)]; exact hp.marks j
-- any finite differential sensor & analytic port.P support radius M
variable (Y:Audience φ Z A W r)
omit h
include Y
lemma holdT (i:I)(x:Bid.Dir G (A i))(h:Roster x ≤1): let P:=bark (W i); ‖jetK G P (fun _ h=>h) (Y.room i).board (BlurD G P _ x)‖ ≤ 1+↑(W i):=by
        intro P; apply (frame_e G _ _ _ _).trans; refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j=>?_ ; rw [echoP]; apply (rentE x _).trans; apply (mul_le_of_le_one_right (tensile _|>.le) h).trans; change 1+(_ :ℝ) ≤1+ _; apply add_le_add_right ?_ 1 -- wrong order
        exact_mod_cast (aery (Y.room i).board ((cross_def _).1 j.property).1)
private lemma ordinary_radius (hp:Filμ (fun i=>bark (W i)) φ Z p k) :
    ∃c:I→ℝ,RateLE φ Z c 0 ∧ ∀ᶠ i in φ,∀ a:Bid.Dir G (A i),‖a‖ ≤ 1+(W i:ℝ) → ‖p i a‖ ≤ c i := by
  let v:I→ℝ:=fun i=>1+(W i:ℝ)
  have rate:RateLE φ Z v 0 := (RateLE.const _ Y.fair).add Y.cash Y.fair
  exact hp.loud.radiusH Y.fair rate hp.tariff

omit Y in
private lemma compact_eval {s:Side} {b:ℕ} (board:Board s b) (func:Bid.Dir G s→ℝ)
    (kept:Crisp (G:=G) (n:=s) (bark b) func) (d:ℝ) (x:Bid.Dir G s)
    (cap:∀ u:Bid.Dir G s,‖u‖ ≤ 1+(b:ℝ) → ‖func u‖ ≤ d)
    (fare:‖jetK G (bark b) (fun _ h=>h) board (BlurD G (bark b) s x)‖ ≤ 1+(b:ℝ)) :
    ‖func x‖ ≤ d := by
  have h:=Crisp.pack (G:=G) (bark b) (fun _ hp=>hp) board func kept x
  exact (congrArg norm h).le.trans (cap _ fare)

lemma Filμ.See (hp: Filμ (fun i=>bark (W i)) φ Z p k): Photos φ Z 0 p:=by
  obtain ⟨c,cost,cap⟩:=ordinary_radius Y hp
  refine ⟨c,cost,?_⟩
  filter_upwards [cap,hp.here] with i bound kept
  intro x unit
  exact compact_eval (G:=G) (Y.room i).board (p i) kept (c i) x bound (holdT Y i x unit)
lemma paid (hp:PlaneQ (fun i=>bark (W i)) φ Z V k): Silks φ Z 0 V:=⟨fun i=>Filμ.See Y (hp.roll i)⟩
end Sleeve
end YM.OPE.Merchant
