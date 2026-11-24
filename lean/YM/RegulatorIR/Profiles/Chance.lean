import YM.RegulatorIR.Profiles.Cadence
import YM.RegulatorIR.Profiles.Aperture

/-!
# Center interpolation from canonical cover registration

Movie indices cannot alter intrinsic parameters. `Fix` seed only on top
translation law. Cover periodic law through *capture prescribed stop*.
Still need payment for jitter average on half-open cube. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Profiles
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Labels Source Centered
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I X:Type}{q u b p a i e k d m:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{J D:Choice M}
variable {S:Heir n G} (R: Reel S){T:S.Accounts}

section Shift
variable {F:Labels.Frame G d}(B:SectionData F)(Ψ: PhaseTests d)(A:Tap F)(Q: Feeds)(ε:ℝ)(z:Room)(t:Cover)
open Aperture
lemma repriceP (i:Stroke F)(y: Cover) : kindle Ψ A Q ε (slide ε t + z) (y+t) i= kindle Ψ A Q ε z y i:=by
 ext r; simp_rw [kindle,map_add]; rw [show slide ε y+slide ε t-(slide ε t+z)=slide ε y-z by abel]
lemma layersP (y:Cover): Intag Ψ A B Q ε (slide ε t + z) (y+t)=convey t (Intag Ψ A B Q ε z y):=by
 ext1 g; ext1 v; simp_rw [Intag, convey,Finset.sum_apply]; apply Finset.sum_congr rfl; intro i _;rw [flare,flare, guardP, repriceP];unfold convey guardP;rw [show translate (y+t) v=translate y (translate t v) from funext fun i=> by simp [translate,add_assoc]]
lemma adheres (h:0<ε) : Testifies Ψ A B Q ε (slide ε t+z)=convey t (Testifies Ψ A B Q ε z):=by
 let x:=slide ε t+z; let P:= Address.census ε Ψ.radius x; let V:= Address.census ε Ψ.radius z
 have hp(y): y∈V ↔ y+t∈P:=by unfold V P x; simp_rw [Address.enroll ε h, map_add]; rw [add_comm (slide ε y) (slide ε t)]; simp
 let r:= Equiv.addRight t
 have hv:P= V.map r.toEmbedding:=by
    ext1 i; rw [Finset.mem_map]; refine ⟨fun v=>?_,?_⟩
    · obtain ⟨y,rfl⟩:= r.surjective i; exact ⟨y,(hp y).mpr v,rfl⟩
    rintro ⟨j,hj,rfl⟩; exact (hp j).mp hj
 ext1 i;ext1 y; simp_rw [convey,Testifies,Finset.sum_apply]; change (∑ z∈P,Intag _ _ _ _ _ _ _ i y)= _; rw [hv,Finset.sum_map]; apply Finset.sum_congr rfl; intro j _; exact congr_fun (congr_fun (layersP B Ψ A Q ε z t j) i) y
end Shift

section Top
-- Pose fixes actual input independently of choices; applying cylinder transports stays independent of FPS beyond valuations in expenses.
variable {m p:ℕ}{P:Portrait G}{W A:Orders (Foot G)} (h:Halo.BasisT m p P W)(H:Halo.BasisT m p P A)
include h H
lemma certifies (hv:Ranks m W)(he:Ranks m A): W=A:=by
 ext1 i
 apply guessed (hv i) (he i) (h.symmetry _) (H.symmetry _); intro x
 have hp:= (h.pose x).symm.trans (H.pose x); have hx : shelter m W x=shelter m A x:= mul_left_cancel₀ (pow_ne_zero _ (PowerSeries.X_ne_zero)) hp
 exact (coeff_mk ..).symm.trans ((congr_arg (PowerSeries.coeff i) hx).trans (coeff_mk ..))
end Top
section Family
abbrev motif (S:Heir n G):= album S (film W)
abbrev portraitR (T:S.Accounts):= movie T (film W)
abbrev signM (M: W→ℕ) := M ∘ film W
abbrev leafX (p:Page M)(x:Room): Page (signM M):= ⟨(p.bindW,x),p.downW,p.good⟩
abbrev turnX (p:Flap M)(x:Room): Flap (signM M):= ⟨(p.volW,x),p.offset,p.ok⟩

lemma scaledCard (w: Flap M): S.l w.next=S.l w.prev*((R.steps w).patch.L:ℝ):=by
 have he:= R.phase w.prev;have hp:= R.phase w.next;let k:=n w.next;let f:=n w.prev;let p:= (R.steps w).patch.L
 have hx:f.val=k.val*p.val:=(R.steps w).sizes
 change S.l w.prev * f.val=S.P w.volW at he; change _* (k.val:ℝ)= S.P w.volW at hp; rw [hx,Nat.cast_mul,← hp] at he
 change _=S.l w.prev*(p:ℝ); apply mul_right_cancel₀ (show (k.val:ℝ)≠0 by positivity); rw [← he];ring
lemma indentX (w: Flap M)(p:Cover) : slide (S.l w.next) p=slide (S.l w.prev) (strideR (R.steps w) p):=by
 rw [scaledCard R];unfold strideR;ext i; simp; ring

variable (B:(portraitR T).Report m)(P:plane W→Portrait G){h:ℕ}
def CenterE (P: plane W→Portrait G)(S:Heir n G):Prop:=∀ w t x, P (w,slide (S.ε w) t + x) = convey t (P (w,x))
def swing (B:(portraitR T).Report m)(i:Page M)(t:Cover)(x:Room):Prop:=∀ e j,Echos (carryX t) (B.main (leafX i x) e j) (B.main (leafX i (slide (S.l i) t+x)) e j)
variable {R} (V:Passage R) (he:Common R)(hv:R.Follows T)(hp:CenterE P S)(H:∀ w, Halo.BasisT m h (P w) (B.main (Page.opening _ w)))
include hp H
lemma topCadence (w t x): swing B (Page.opening M w) t x:=by
 let f:= Page.opening M w; let y:= slide (S.l f) t+x; let s:= leafX f x;let u:= leafX f y
 let A:= B.main s
 have hk:Halo.BasisT m h (convey t (P (w,x))) (B.main u):=by rw [← hp w];exact H (w,y)
 have hx:Halo.BasisT m h (convey t (P (w,x))) (fun e j=> echo (carryX t) (A e j)):= (H (w,x)).vayne t
 have hq:=certifies hk hx (fun e=> B.ceilingM (w,y) e) (fun e j he=> B.ceilingM (w,x) e j (fun hz=> he (by rw [show A e j=0 from hz,echo_zero])))
 intro i j; change Echos (carryX t) _ (B.main u i j); rw [hq]; exact echos _ _
include V he hv
lemma periodic : ∀ i x t, swing B i x t:=by
 refine Page.proves (topCadence B P hp H) ?_
 intro w hS t x e j; rw [indentX R];let d:=strideR (R.steps w) t; let y:= slide (S.l w.prev) d + x;let f:= S.frames w;let p:=turnX w x;let u:=turnX w y
 change Echos _ (B.main p.next e j) (B.main u.next e j); rw [← B.step_m p,← B.step_m u]
 let r:= T.bulk w.prev
 change Echos _ (f.each m r _ e j) (f.each m r _ e j)
 exact flames (carryX d) (carryX t) (V.cells he hv w.prev d) (V.levels w t).1 (V.levels w t).2 (Passage.assets he w t) (hS d x) e j
lemma beats (w:W)(j:Choice M)(e:ℕ): Centered.Rhythm (S.l (j.choose w)) (medium S T B j e w):=by
 intro y x; have hx:= periodic B P V he hv hp H (j.choose w) y x e 0 Fin.elim0;rw [Subsingleton.elim (onPath _ _) (Fin.elim0:Tuple _ 0)] at hx; exact hx
end Family
end YM.RegulatorIR.Profiles
