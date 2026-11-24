import YM.Integration.WilsonOriginalSeparatedFrontClusters

/-! One small Lie direction on every short front of the finite physical roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalClusteredAxialDirection
open Lattice Wilson RG Comparison.Density Comparison.Density.Transport Comparison.Density.Mirrors
open AnalyticBridge.SectorAffine.Offset
open WilsonOriginalSeparatedFrontClusters
open scoped Classical
variable {G:Gauge} {n:Side} {V:Type}

def turn (o:V→Site n)(k:ℕ)(crew:V→Site n→G.El)(x:Site n):G.El:=
  if h:∃v,separation (o v) x ≤ k then crew (front o (2*k+2) h.choose) x else 1

private theorem own (o:V→Site n)(k:ℕ)(crew:V→Site n→G.El){v:V}{x:Site n}
    (near:separation (o v) x ≤ k):
    turn o k crew x=crew (front o (2*k+2) v) x:=by
  have h:∃v',separation (o v') x ≤ k:=⟨v,near⟩
  rw [turn,dif_pos h,overlapping o k h.choose_spec near]

def cut (o:V→Site n)(k:ℕ)(z:Site n→G.El)(U:Config G n):Config G n:=fun e=>
  if ∃v,separation (o v) e.1 ≤ k ∧ separation (o v) (e.1+step e.2) ≤ k then gauge z U e else 1

def Common (o:V→Site n)(k:ℕ)(tube:LinkTube G)(w:ℝ)(U:Config G n):Prop:=
  ∃ (z:Site n→G.El)(X:Directions G n), ‖X‖ ≤ w ∧ increment 1 X=cut o k z U ∧
    (∀e,G.chord (cut o k z U e)<tube.radius) ∧
    ∀(v:V)(f:Config G n→ℂ),LocalOn (neighborhood k (o v)) f→GaugeInvariant f→f (increment 1 X)=f U

theorem original [Fintype V](o:V→Site n)(k:ℕ)(B:BudgetPoint)(tube:LinkTube G)(U:Config G n){w:ℝ}
    (inside:(Fintype.card V-1)*(2*k+2)+k<B.B)(room:Room B n tube B.B w)
    (bright:∀v,Healthy B.threshold (neighborhood B.B (o v)) U):Common o k tube w U:=by
  classical
  let a:=2*k+2
  let reach:=(Fintype.card V-1)*a+k
  have fit:reach<B.B:=inside
  choose crew charge using fun v=>axial_to B (o v) B.B reach U fit room.side (bright v)
  let z:=turn o k crew
  let W:=cut o k z U
  have chord (e:Edge (Site n)):G.chord (W e) ≤ axialCost B B.B:=by
    dsimp only [W,cut]
    split
    next h =>
      obtain ⟨v,h1,h2⟩:=h
      have center:separation (o (front o a v)) e.1 ≤ reach:=
        (separation_triangle (o (front o a v)) (o v) e.1).trans (Nat.add_le_add (extent o a v) h1)
      have agreed:gauge z U e=gauge (crew (front o a v)) U e:=by
        change turn o k crew e.1*U e*(turn o k crew (e.1+step e.2))⁻¹=_
        rw [own o k crew h1,own o k crew h2]
        rfl
      rw [agreed]
      exact charge _ _ center
    next _=>rw [G.chord_one];exact axial_nonneg ..
  have core e:=lt_of_le_of_lt (chord e) room.core
  have logs:‖logField W‖ ≤ w:=(pi_norm_le_iff_of_nonneg (B.threshold_pos.le.trans room.budget)).2
    fun e=>(tube.log_size _ (core e)).trans ((mul_le_mul_of_nonneg_left (chord e) tube.scale.le).trans room.logs)
  have recovered:increment 1 (logField W)=W:=by
    funext e
    change G.lieExp (G.plog (G.mat (W e)))*1=W e
    rw [mul_one,tube.recovers _ (core e)]
  refine ⟨z,logField W,logs,recovered,core,?_⟩
  intro v f localRead ward
  rw [recovered,←ward z U]
  apply localRead
  intro e e0 e1
  have kept:∃u,separation (o u) e.1 ≤ k ∧ separation (o u) (e.1+step e.2) ≤ k:=
    ⟨v,(neighborhood_iff ..).1 e0,(neighborhood_iff ..).1 e1⟩
  exact if_pos kept

theorem cropped [Fintype V](o:V→Site n)(B:BudgetPoint)(tube:LinkTube G)(U:Config G n){w:ℝ}
    (late:64*(Fintype.card V+1) ≤ B.B)(room:Room B n tube B.B w)
    (bright:∀v,Healthy B.threshold (neighborhood B.B (o v)) U):
    Common o (2*crop B.B (Fintype.card V)+2) tube w U:=by
  apply original o _ B tube U _ room bright
  have paid:=fits B.B (Fintype.card V) late
  dsimp only at paid
  omega

end YM.Integration.WilsonOriginalClusteredAxialDirection
end
