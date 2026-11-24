import YM.MS.Cylinder.Characters
import YM.MS.Wilson.Bare
/-!
# Unscaled Wilson charge/parity control

Symm and degree typed before translation and concentration. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native
open Function Filter Finset Set Plane Koszul Cylinder Taylor Lab Bare Focus Landau Sew Chart Draft
open Lattice
open scoped Topology ContDiff
variable {G:Gauge} {A P:Type}
abbrev Tuned (H:Dot G P)(q:ℤ):= Tune parity ghostNo q H
@[simp] lemma charged (i:ToneS G): ghostNo ((Spectrum G).dual i)+ghostNo ((Spectrum G).plain i)=-1:= by rcases i with ⟨i,j⟩|i <;> rfl
lemma ghostParity (i: Branch G Axis) : Local.parity (ghostNo i) = Landau.parity i:= by rcases i with ⟨⟨_|_,_|_⟩,_⟩ <;> rfl

lemma Tune_port [Fintype A][DecidableEq A] (W:A→Edge P)(f:Lot G A→ℝ)(h:germ f): Tuned (Sew.art W f) 0:= by
   let X : Sector (A × Conn G):=fun _=> false
   let F := ink priv f; let H : Cyl _ ℂ := region.symm F
   have hs : Symm X F:= ink_s _ (fun _ H=> by contradiction) h
   have hv : Rails (fun _:A×Conn G=>0) 0 F:= by intro l H; apply False.elim (H ?_); simp [chargeInt]
   exact ⟨((ferry_tie (p:=X) (q:=DotFlip) (knot W) (R:=ℂ) (fun _=>rfl)).sym H hs),hv.ferry (w:=ghostNo ∘ Prod.fst) (knot W) (fun _=> rfl) H, Still.passes (knot W) H (uncoloured _ _ )⟩
variable [AddCommGroup P] (d:Chart.Rail P)
omit [AddCommGroup P] in
lemma Tune_edge (x:Edge P)(F:G.Color→ℝ)(h:germ F): Tuned (onedge x F) 0:= Tune_port _ _ (show germ (fun b:Lot G Unit=> F (b ())) from h.comp (f:=fun b:Lot G Unit=> b ()) 0 (contDiff_apply ..|>.contDiffAt))
lemma sym_w (G:Gauge)(x:P): Tuned (weightW G d x) 0:= Tune.sum _ fun _ _=> Tune_port _ _ bill_gone
omit [AddCommGroup P] in
lemma sym_h (G:Gauge)(x:P): Tuned (weightH G x) 0:= Tune.sum _ fun _ _=> Tune_edge _ _ (Maurer.hlog _)
omit [AddCommGroup P] in
lemma sym_s (x:P)(i: Conn G)(q: Edge P)(J:Conn G→ Maurer.Ends G): Tuned (steerA x i q J) 1:= by
    unfold steerA; refine Tune.sum _ (fun k _=>?_); exact (Tune.lit (p:=parity) (m:=ghostNo) (ghostAt k x)).pair (Tune_edge q _ (vel_germ (J k) i))
lemma sym_all (G:Gauge)(x:P): Tuned (bosons G d x) 0:= by
    refine (sym_w d G x).add (Tune.sub (Tune.sum _ fun i _=> Tune.sum _ fun j _=>?_) (Tune.sum _ fun j _=>?_))
    · exact (Tune.lit (p:=parity) (m:=ghostNo) ((anti i,j),x)).pair ((sym_s x j (x,i) leftStem).add (sym_s _ _ _ _))
    · have he k l: Tuned (couple DotFlip (GH k x) (GH l x)) (G:=G) 2:= (Tune.lit (p:=parity) (m:=ghostNo) (ghostAt k x)).pair (Tune.lit (ghostAt l x))
      have hs : Tuned (cog x j) 2:= Tune.sum _ fun k _=> Tune.sum _ fun l _=> (he k l).cash (-(letterLie k l j:ℂ)/2) (by simp)
      exact (Tune.lit (p:=parity) (m:=ghostNo) ((gaugeC,j),x)).pair hs
end YM.MS.Native
