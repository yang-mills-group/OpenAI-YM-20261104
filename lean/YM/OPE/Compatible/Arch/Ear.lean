import YM.OPE.Compatible.Arch.Rings
/-!
# score charts are dimed exactly. Lift maps read all tangent curves.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision OPE.Libra
attribute [local instance] Gauge.frobInner
variable {I J:Type}{G:Gauge}
local notation "Lf" => Tested.germ
namespace Score.Stand
variable {D V:Type} {B:Set V}{R:Score D V}
variable (T:R.Stand B)
@[simp] lemma dress1 : T.cite (1:T.Stable→G.El) 1=1:=by funext p; unfold cite;split<;>rfl
@[simp] lemma sweep1 : T.sweep (1:D→G.El)=1:=by rw [← dress1 T,T.treed]
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{u:E→ Tile G D}
lemma sweptLog {i:E}(h:∀ j,ContDiffAt ℝ ω (fun i=> G.mat (u i j)) i): ∀ p:V, ContDiffAt ℝ ω (fun i=> G.mat (T.sweep (u i) p)) i := by
    intro p; induction v : T.flick p using Nat.strong_induction_on generalizing p with
    | _ v ih=>
      by_cases hx:p∈ Bᶜ
      · let q: ↥(Bᶜ):=⟨p,hx⟩; let f:=T.point q; have hh:=ih _ ((T.bump q).trans_eq v) (R.lastV f) rfl
        simp_rw [show p=q.val from rfl,T.sweptJ]; simp only [G.mat_mul,G.mat_inv]; refine hh.mul ?_; change ContDiffAt ℝ ω (fun i=> star (G.mat (taste (u i) f))) i
        unfold taste; split
        next hD=> simp only [G.mat_inv,star_star]; exact h _
        next hD=> exact (starL' ℝ : G.Mat≃L[ℝ] G.Mat).contDiff.contDiffAt.comp i (h _)
      simp_rw [T.swept _ (not_not.mp hx)]; exact contDiffAt_const
lemma dellLog {i:E}(h:∀ j,ContDiffAt ℝ ω (fun i=> G.mat (u i j)) i) (p:T.Free): ContDiffAt ℝ ω (fun i=> G.mat (T.dell (u i) p)) i :=by
      unfold dell dress; simp only [G.mat_mul,G.mat_inv]; exact ((T.sweptLog h _).mul (h _)).mul ((starL' ℝ : G.Mat≃L[ℝ] G.Mat).contDiff.contDiffAt.comp i (T.sweptLog h _))
end
variable [Fintype D]
nonrec def rollX : Keys G T.Free→ₗ[ℝ] Keys G D where
    toFun := T.cite 0
    map_add' _ _:= by funext i; unfold cite; split_ifs <;> simp [*]
    map_smul' _ _:= by funext i; unfold cite; split_ifs <;> simp [*]
omit [Fintype D] in lemma rollPut (x:Keys G T.Free): put (T.rollX x)=T.cite 1 (put x):=by funext i; unfold put Chart.expLinks; simp only [rollX,cite,coe_mk,AddHom.coe_mk];split<;>simp
lemma paintD (i:Keys G D)(j:D):ContDiffAt ℝ ω (fun x:Keys G D=>G.mat (put x j)) i := (G.exp_jet.comp (contDiff_apply ..)).contDiffAt
omit [Fintype D] in lemma drape_zero (H:R.Stand B): T.drapeX H (1:Tile G T.Free)=1:=by funext i; change R.dress (H.sweep _) (T.cite 1 (1:Tile G T.Free)) _ =_; rw [dress1,sweep1,R.dance];rfl
def beenX (H:R.Stand B): Dimes G T.Free H.Free where
    q:= { T.drapeX H with
          continuous_toFun:=T.delegates H
          continuous_invFun:=H.delegates T }
    acts := T.drapeHaar H
    clan := T.drape_zero H
    lifted := by
        apply contDiffAt_pi.mpr; intro i; change ContDiffAt ℝ ∞ (fun x=> G.plog (G.mat (H.dell (T.cite 1 (put x)) i))) (0:Keys G T.Free); have h0: G.mat (H.dell (T.cite 1 (put (0:Keys G T.Free))) i)=1:=by rw [put_zero,show H.dell (T.cite 1 1)=_ from T.drape_zero H]; rfl -- mat one?
        refine ContDiffAt.of_le (ContDiffAt.comp (g:=G.plog) 0 (by exact h0.symm ▸ G.plog_diff) (H.dellLog ?_ i)) le_top; intro p; simp_rw [← T.rollPut]; exact (paintD (T.rollX 0) p).comp _ (toContinuousLinearMap T.rollX |>.contDiff |>.contDiffAt)
end Score.Stand
end YM.OPE.Cascade
