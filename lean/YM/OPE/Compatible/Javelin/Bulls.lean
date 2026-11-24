import YM.OPE.Compatible.Glade.Respite
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {u v:ℝ}(A: Alps K T i u)(x y:Site n)(H:Even n.val)(hS:G.Simple)(hi:4 ≤ i)(hr:LocalRatio R)
local notation "Y"=> solar G d τ
abbrev Warp (A:Alps K T i u)(H:Even n.val)(hi:4 ≤ i)(h:G.Simple)(x y:Site n)(p q: Y)(Z:ChartRatio G): Token:=SpecH A H hi h (bramble H) p q x y Z
local notation "Φ" p:arg q:arg=> Warp A H hi hS x y p q R
lemma BoltCom (p q:Y): Warp A H hi hS x y p q R= Warp A H hi hS y x q p R:=by unfold Warp SpecH RGram isolate; rw [mul_comm (cutφ _ p.val x)]
include hr
lemma linkZ(p q: Y): Warp A H hi hS x y p q R= let V:=(bredV A 0 _ hi hS).L (bramble H); fair (Chart.tangent G (Stand.Free (bramble H))) (penon V) (V.hat R) (isolate H (bramble H) p.val q.val x y):= Lid.cutOut ((bredV A 0 H hi hS).L (bramble H)) hr _ _ (penon_shape _)
lemma bolt_plus (p q r:Y) : Warp A H hi hS x y (p+q) r R= Φ p r + (Φ q r):=by
     rw [linkZ _ _ _ _ _ _ hr,linkZ _ _ _ _ _ _ hr,linkZ _ _ _ _ _ _ hr]; let Z:=isolate (G:=G) (d:=d) (τ:=τ) H (bramble H); have hh:(Z (p+q).val r.val x y)=Z p.val r.val x y+Z q.val r.val x y:=by
         funext i; change Vtap (p+q).val x _* Vtap r.val y _= _; have ht(a:Bid.Dir G n): Vtap (p+q).val x a= Vtap p.val x a+Vtap q.val x a:=by unfold Vtap; erw [map_add]; exact Ink_sum _ _ _ _ d _ _ (resin p.val (m:=0) (fun _=>Nat.zero_le _)) (resin q.val (m:=0) (fun _=>Nat.zero_le _))
         rw [ht,add_mul];rfl
     dsimp only; rw [show isolate H (bramble H) _ _ _ _=_ from hh]; exact Firmly _ _ _ (Lid.hat_toll _ hr) (isolateB _ _ _ _ _ _) (isolateB _ _ _ _ _ _)
open JetS
lemma boltTint (p q:Y)(v:ℝ): Warp A H hi hS x y (v • p) q R= plainJ v* Φ p q :=by
    rw [linkZ _ _ _ _ _ _ hr, linkZ _ _ _ _ _ _ hr]; dsimp only; let f:= isolate H (bramble H) p.val q.val x y; rw [show isolate H (bramble H) _ _ _ _=(fun i=> plainJ v *f i) from ?_]; swap
    · funext i; change Vtap (v • p).val x _* Vtap q.val y _ = _; unfold Vtap; erw [map_smul,Ink_scale]; exact mul_assoc (plainJ v) _ _
    exact coin_F _ _ _ _ f (isolateB _ _ _ _ _ _) (Lid.hat_toll _ hr)
variable (hh:0 ≤ u)
abbrev Pencil (j:Phase)(p q: Y):= (Warp A H hi hS x y p q R).seq j.val
abbrev Dice (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] := E→L[ℝ] E →L[ℝ] ℝ
lemma pencilP (j:Phase)(p q v:Y): Pencil A x y H hS hi j (p+q) v (R:=R)= Pencil (R:=R) A x y H hS hi j p v+ Pencil (R:=R) A x y H hS hi j q v :=by unfold Pencil; rw [bolt_plus _ _ _ _ _ _ hr]; fin_cases j<;>rfl
lemma pencilQ (j:Phase)(p q:Y)(v:ℝ): Pencil A x y H hS hi (R:=R) j (v • p) q=v* Pencil A x y H hS hi j p q (R:=R):=by unfold Pencil; rw [boltTint _ _ _ _ _ _ hr]; fin_cases j <;> simp [plainJ,JetS.seq]
include hr hh
lemma worthP (p:Phase): ∃ L: Dice Y,∀ x' y', L x' y'=Pencil A x y H hS hi (R:=R) p x' y':=by
    let P:Y→ Y→ℝ:=Pencil A x y H hS hi p (R:=R)
    let F:Y→ₗ[ℝ] Y→ₗ[ℝ] ℝ:= LinearMap.mk₂ ℝ P (pencilP _ _ _ _ _ _ hr p) (fun v q t=> pencilQ _ _ _ _ _ _ hr p q t v) ?_ ?_; rotate_left
    · intro s t v; unfold P Pencil; rw [BoltCom A,BoltCom A x,BoltCom A x]; exact pencilP _ _ _ _ _ _ hr _ _ _ _
    · intro t v q; unfold P Pencil; rw [BoltCom A,BoltCom A x]; exact pencilQ _ _ _ _ _ _ hr _ _ _ _
    obtain ⟨c,hc,H'⟩:= (glowV (fun _:Y × Y=>n) (fun _=>H) (fun _=>bramble H) (v:=fun _=>u) (b:=fun _=>0) (fun _=>A) (fun _=>bredV A 0 H hi hS) Prod.fst Prod.snd (fun _=>x) (fun _=>y) hS hr hi rfl ⟨⟨A.clip,fun _=>rfl⟩,⟨u,hh,fun _=>le_rfl⟩,fun _=>hh⟩) p
    let b':ℝ:=c*n.val^(4+(0+8)+4*((d+2+(d+2))+6)+(4+8+4*6+(4+8+4*6))); let hP:∀ x y,‖F x y‖ ≤ b'*‖x‖ * ‖y‖:=fun i j=> (H' (i,j)).trans_eq (mul_assoc _ ‖i‖ ‖j‖).symm
    exact ⟨F.mkContinuous₂ b' hP,fun _ _=>rfl⟩
noncomputable def ArmZ (p:Phase) : Dice Y:= (worthP A x y H hS hi hr hh (d:=d) (τ:=τ) p).choose
lemma lanceZ (p:Phase)(u v:Y):ArmZ A x y H hS hi hr hh p u v=(Warp A H hi hS x y u v R).seq p.val:= (worthP A x y H hS hi hr hh p).choose_spec u v
end YM.OPE.Quit.PriceZ
