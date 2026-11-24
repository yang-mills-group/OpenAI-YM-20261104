import YM.RG11Proof.Fields.FreeScale
import YM.RG11Proof.Rigidity.Frozen
import YM.RG11Proof.Scale.Flowing

/-!
# Join CS and power matching on ACTUAL E presentations

Consumer at fixed finite powers N independently at any d≥6. Need frozen
leading coherence (now unconditionally from Yang--Mills datum h Simple)
and ONE first triangle slope (on A) at d=6. B-independent reg-rate and
other analytic hypotheses not supplied (B slope will need its own independent
calculation to identify the coupling tangent via `probeRuler`).
Full grade-preserving *conversion derived*, not obtained by postulating final
Z admissible. Logs derived from CS even at order zero provided arrays are
distributions from continuous kernels (or prove the analogous LF respiration)
and the mass-independent b-adjustment grades hold. Need canonical/fixed
β, μ, gamma and ACTUAL proofs of their scale laws on the independent schemes.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.RG11.Fields
open scoped Topology Classical BigOperators ContDiff
open PowerSeries YM.PertExtension.Position YM.RG11.Jets Labels
open YM.RG11.Scale YM.Pert.Triangle
open YM.Pert.Position (E)
variable {G : Gauge}{F:Frames G}

/-- Minimal continuum representing functions; this API concerns only
fixed finite powers/demand. Smoothness & exact limits required by program
are stronger.
-/
def Tangible (A:ShapeReport G F) {d}(X:Basis F d)(N:ℕ) : Prop:=
   ∀ k≤N,∀ (n:ℕ)(v:Fin n→X.J),∃ (K:Points n→ℂ),ContinuousOn K (conf n) ∧ ∀ f:Test n,A.table k d n f (X.b ∘ v)=f.applyTo K

 theorem breath (A:ShapeReport G F){d}(X:Basis F d){N:ℕ}(h:Tangible A X N):
   Respiration narrow scalesX (A.realAt X) N := by
   intro k hk v u
   obtain ⟨K,hK,hp⟩:=h k hk v.1.order v.2
   simp only [ShapeReport.realAt,narrow,scalesX,Keeper.move,coeff_mk,form]
   have h (f:Test v.1.order) : A.table k d v.1.order f (X.b ∘ v.2)=f.applyTo K:=hp f
   change HasDerivAt (fun t=> (A.table k d v.1.order (compress _ t v.1.test) (X.b ∘ v.2)).re) ((A.table k d _ (blows _ (compress _ u v.1.test)) (X.b ∘ v.2)).re) u
   simp_rw [hp,←commute]
   exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt _ (GaugeEuler hK _ _)

/-- Declare scale behavior of each FINAL formal prescription at this horizon,
not by just naming its beta/gamma. Here CS accepted-sign convention (see
`Scale/CS`). Scale cost at higher omitted powers is not provided.
-/
structure Shows (A:ShapeReport G F){d}(X:Adapted F d)(N:ℕ)(β:PowerSeries ℝ)(b:Square X.toBasis.J (PowerSeries ℝ)): Prop where
   kernels : Tangible A X.toBasis N
   cs : Stem N scalesX (height X) (A.realAt X.toBasis) β b
   free_beta : ∀ k≤1,coeff k β=0
   free_b : piece 0 b=0
   adjusts : ∀ k,graded (height X) (piece k b)
   valid : vertical (L:=X.toBasis.guard) b

 theorem beams {A:ShapeReport G F}{d}{X:Adapted F d}{N}{β:PowerSeries ℝ}{b:Square X.toBasis.J (PowerSeries ℝ)}(ha:Shows A X N β b):
 Engineering (height X) narrow (A.realAt X.toBasis) N :=by
   intro k hk v
   obtain ⟨p,hp⟩ := logarithms (height X) scalesX ha.cs (breath A X.toBasis ha.kernels) ha.free_beta ha.free_b (fun k _=>ha.adjusts k) k hk v
   exact ⟨p,fun u _=>hp u⟩

 theorem engineering_match (A B:ShapeReport G F){d}(hX:6≤d)(X:Adapted F d)
    (hG:G.Simple)(h:A.table 1 6 3 profileChoice (basic F)=cTest G)
    (p:Change ℝ X.toBasis.J)(hZ:X.toBasis.guard.Lawful p.Z)(hg:Anchored p.g){N:ℕ}
    (hm:∀ v,Through N (p.act (A.realAt X.toBasis) v) (B.realAt X.toBasis v))
    {β μ : PowerSeries ℝ}{b m:Square X.toBasis.J (PowerSeries ℝ)}(ha:Shows A X N μ m)(hb:Shows B X N β b):
   (∀ k≤N,graded (height X) (piece k p.Z)) ∧ Through N (β*derivative ℝ p.g) (PowerSeries.subst p.g μ) ∧
     MatThrough N (β • (flash p.Z)) (b*p.Z - p.Z * subs p.g m):=by
   have ht:=Rigidity.Ice.polar_rank F hG d
   have he:Free X.toBasis.guard (A.realAt X.toBasis):=free_from_frozen X.toBasis (A.price0 _) ht
   have hqu:Sees X.toBasis.guard (A.realAt X.toBasis):=(A.ticket hG h hX X.toBasis ht).sees
   apply stamp_transport p (by convert! hZ) hg (lift_permits X) narrow narrow_id scalesX hqu he (beams ha) (beams hb) hm ha.cs hb.cs _ ha.valid hb.valid
   unfold Anchored; rw [← coeff_zero_eq_constantCoeff_apply]; exact hb.free_beta _ (by omega)

 theorem engineering_all (A B:ShapeReport G F){d}(hX:6≤d)(X:Adapted F d)
    (hG:G.Simple)(h:A.table 1 6 3 profileChoice (basic F)=cTest G)
    (p:Change ℝ X.toBasis.J)(hZ:X.toBasis.guard.Lawful p.Z)(hg:Anchored p.g)
    (hm:p.act (A.realAt X.toBasis)=B.realAt X.toBasis)
    {β μ : PowerSeries ℝ}{b m:Square X.toBasis.J (PowerSeries ℝ)}(ha:∀N,Shows A X N μ m)(hb:∀N,Shows B X N β b):
   graded (height X) p.Z ∧ β*derivative ℝ p.g = PowerSeries.subst p.g μ ∧
     β • (flash p.Z)=b*p.Z - p.Z * subs p.g m:=by
   have ht(k:ℕ):=engineering_match A B hX X hG h p hZ hg (by rw [hm]; exact fun _=>Through.refl _) (ha k) (hb k)
   exact ⟨graded.piece_all.mpr (fun i=> (ht i).1 _ le_rfl),PowerSeries.ext (fun i=> (ht i).2.1 _ le_rfl), Matrix.ext fun i j=> PowerSeries.ext (fun n=>(ht n).2.2 _ _ _ le_rfl)⟩
end YM.RG11.Fields
